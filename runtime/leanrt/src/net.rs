//! `Std.Internal.UV` for lean2rr's shim (`lean2rr/L2RShim.lean`) over
//! lean-runtime: the loop, its timers and signal watchers
//! (`lean_runtime::sched::uv`), TCP and UDP sockets, name resolution and the
//! interface addresses (`lean_runtime::net`, feature `net`), and the text
//! forms of addresses (`lean_runtime::semantics::net`). The event loop is
//! lean-runtime's scheduler's own (one per program); every rule (libuv's
//! state machines, system calls and their order, errors, when a promise
//! resolves) is lean-runtime's. This module converts values only.
//!
//! lean2rr's runtime cannot build Lean values (`Except IO.Error ...`,
//! `Option ByteArray`, a `SocketAddress`), so the shim builds them, in Lean,
//! from an operation's outcome (`OpSt`), read through the shim's
//! primitives (`l2r_shim_*` in the prelude). An operation that completes
//! later works the same way everywhere: the shim makes a promise `r` (of
//! `Unit`), starts the operation with it, and attaches a continuation to `r`
//! (a `sync` dependent, which runs where `r` is resolved); lean-runtime's
//! completion closure (`Completion`, its `done`) stores the outcome in the
//! `Op` and drops its reference to `r`, whose last reference resolves it
//! (with `none`: `task::Promise`'s drop) and so runs the continuation,
//! which reads the `Op` and resolves the promise the program sees, as
//! libuv's callback does natively. Completions run on lean-runtime's loop
//! context, as natively on libuv's thread. An operation lean-runtime gives
//! up (its closure dropped uncalled: `cancelRecv`, `cancelAccept`, a stopped
//! timer) is marked canceled, and its continuation does nothing.
//!
//! Errors are lean-runtime's `IoError`s, kept in the `Op` (the start's, at
//! the call, and the completion's); the shim builds the `IO.Error` with the
//! builder `fs::kind_of` names, its code, file name and details
//! (`L2RShim.ioErrorOf`).
//!
//! Addresses travel as bytes: a `SocketAddress` as the family (4 or 6), the
//! port (big-endian), then the 4 or 16 bytes of the address; an `IPAddr`
//! without the port.

use crate::array::RVec;
use crate::fs::LHandle;
use crate::task::LPromise;
use lean_runtime::io::IoError;
use lean_runtime::net::tcp::TcpSocket;
use lean_runtime::net::udp::UdpSocket;
use lean_runtime::net::{dns, iface, IpAddr, Ipv4Addr, Ipv6Addr, SendData, SocketAddr};
use lean_runtime::sched::uv::{self, LoopPromise, Signal, Timer};
use std::cell::{RefCell, UnsafeCell};
use std::rc::Rc;

// ---------------------------------------------------------------------------
// Operations

/// An operation's outcome, which the shim reads.
#[derive(Default)]
pub struct OpSt {
    /// Completed (before its start returned, or later).
    pub done: bool,
    /// Given up without completing: the continuation does nothing.
    pub canceled: bool,
    /// A value: a signal's number, a `bool` (`waitReadable`), 1 for the end
    /// of a stream (`recv?`'s `none`) and for a system query's `none`
    /// (`sys`: no such group, an unset variable).
    pub code: i32,
    /// The error its start reports at once (the extern throws it).
    pub start_err: Option<IoError>,
    /// The completion's error.
    pub err: Option<IoError>,
    pub bytes: Vec<u8>,
    pub handle: Option<LHandle>,
    pub addr: Vec<u8>,
    pub strs: Vec<Vec<u8>>,
    /// `Timer.next`/`Signal.next`: the loop's promise is the one the shim
    /// passed (`fresh`), or this one, which the loop already had.
    pub fresh: bool,
    pub promise: Option<LPromise>,
}

pub fn op_new() -> LHandle {
    reussir_rt::rc::Rc::new(Box::new(UnsafeCell::new(OpSt::default())) as Box<dyn std::any::Any>)
}

pub fn op(h: &LHandle) -> &'static mut OpSt {
    let c = h.downcast_ref::<UnsafeCell<OpSt>>().expect("leanrt: not an operation");
    // The operation lives as long as the handle, which the caller holds;
    // nothing else reads it during the access.
    unsafe { &mut *c.get() }
}

/// An operation whose start failed (or succeeded: `Ok`).
pub(crate) fn started(r: Result<(), IoError>) -> LHandle {
    let o = op_new();
    if let Err(e) = r {
        op(&o).start_err = Some(e);
    }
    o
}

/// The error of operation `o`: its start's (`which` 0) or its completion's
/// (1), if it has one.
pub fn op_err(o: &LHandle, which: u8) -> Option<&'static IoError> {
    let x = op(o);
    if which == 0 { x.start_err.as_ref() } else { x.err.as_ref() }
}

/// The `IO.Error` builder of an error (`fs::kind_of`), `u32::MAX` for none.
pub fn err_kind(o: &LHandle, which: u8) -> u32 {
    op_err(o, which).map_or(u32::MAX, crate::fs::kind_of)
}

/// Its code (0 for a user error, which has none).
pub fn err_errno(o: &LHandle, which: u8) -> u32 {
    op_err(o, which).and_then(IoError::os_code).unwrap_or(0)
}

/// Its file name and details (the empty string where it has none).
pub fn err_texts(o: &LHandle, which: u8) -> (Vec<u8>, Vec<u8>) {
    let text = |s: Option<&String>| s.map(|s| s.as_bytes().to_vec()).unwrap_or_default();
    match op_err(o, which) {
        Some(e) => (text(e.file_name()), text(e.details())),
        None => (Vec::new(), Vec::new()),
    }
}

/// lean-runtime's completion closure of an operation (its `done`, which
/// natively holds the loop's reference to the promise): the operation and
/// the shim's promise `r`. `finish` stores the outcome and drops `r`;
/// dropped unfinished, the operation is canceled (and `r` dropped).
struct Completion {
    op: LHandle,
    r: Option<LPromise>,
}

impl Completion {
    fn new(o: &LHandle, r: LPromise) -> Completion {
        Completion { op: o.clone(), r: Some(r) }
    }

    fn finish(mut self, f: impl FnOnce(&mut OpSt)) {
        let o = op(&self.op);
        f(o);
        o.done = true;
        drop(self.r.take());
    }

    /// Finish with `res`'s error, or with `ok` applied to its value.
    fn result<T>(self, res: Result<T, IoError>, ok: impl FnOnce(&mut OpSt, T)) {
        self.finish(|o| match res {
            Ok(v) => ok(o, v),
            Err(e) => o.err = Some(e),
        })
    }
}

impl Drop for Completion {
    fn drop(&mut self) {
        if let Some(r) = self.r.take() {
            op(&self.op).canceled = true;
            drop(r);
        }
    }
}

/// An operation with a completion: `start` gets the completion closure;
/// its failure is the start's error.
fn pending(r: LPromise, start: impl FnOnce(Completion) -> Result<(), IoError>) -> LHandle {
    let o = op_new();
    let c = Completion::new(&o, r);
    if let Err(e) = start(c) {
        op(&o).start_err = Some(e);
    }
    o
}

/// Complete operation `o` (its promise `r`) with the error `err` (or
/// none) on lean-runtime's loop context at the loop's next turn, as
/// natively a libuv callback after its thread pool's work (`sys::random`).
pub fn complete_on_loop(o: &LHandle, r: LPromise, err: Option<IoError>) {
    let c = RefCell::new(Some(Completion::new(o, r)));
    let err = RefCell::new(err);
    let cb: Rc<dyn Fn()> = Rc::new(move || {
        if let Some(c) = c.borrow_mut().take() {
            let e = err.borrow_mut().take();
            c.finish(|x| x.err = e);
        }
    });
    lean_runtime::sched::timer_start(std::time::Instant::now(), cb);
}

fn new_handle<T: 'static>(v: T) -> LHandle {
    reussir_rt::rc::Rc::new(Box::new(v) as Box<dyn std::any::Any>)
}

fn get<T: 'static>(h: &LHandle) -> &T {
    h.downcast_ref::<T>().expect("leanrt: not a handle of this kind")
}

// ---------------------------------------------------------------------------
// Addresses

/// A socket address from the shim's encoding.
pub fn decode_addr(b: &[u8]) -> Option<SocketAddr> {
    let port = u16::from_be_bytes([*b.get(1)?, *b.get(2)?]);
    Some(SocketAddr::new(decode_ip(&[&b[..1], b.get(3..)?].concat())?, port))
}

/// An IP address from the shim's encoding.
pub fn decode_ip(b: &[u8]) -> Option<IpAddr> {
    match b.first() {
        Some(4) if b.len() >= 5 => Some(IpAddr::V4(Ipv4Addr::new(b[1], b[2], b[3], b[4]))),
        Some(6) if b.len() >= 17 => {
            let mut o = [0u8; 16];
            o.copy_from_slice(&b[1..17]);
            Some(IpAddr::V6(Ipv6Addr::from(o)))
        }
        _ => None,
    }
}

/// The shim's encoding of an IP address, 17 bytes (the family, then the
/// address, zero-padded).
fn encode_ip17(a: &IpAddr) -> [u8; 17] {
    let mut v = [0u8; 17];
    match a {
        IpAddr::V4(x) => {
            v[0] = 4;
            v[1..5].copy_from_slice(&x.octets());
        }
        IpAddr::V6(x) => {
            v[0] = 6;
            v[1..17].copy_from_slice(&x.octets());
        }
    }
    v
}

/// The shim's encoding of a socket address.
pub fn encode_addr(a: &SocketAddr) -> Vec<u8> {
    let ip = encode_ip17(&a.ip());
    let n = if a.is_ipv4() { 5 } else { 17 };
    let mut v = vec![ip[0]];
    v.extend_from_slice(&a.port().to_be_bytes());
    v.extend_from_slice(&ip[1..n]);
    v
}

/// The address the shim passed, or `EINVAL` (the shim encodes every
/// `SocketAddress`, so this cannot fail).
fn addr_of(b: &[u8]) -> Result<SocketAddr, IoError> {
    decode_addr(b).ok_or_else(|| IoError::decode_uv_error(-22, None))
}

fn ip_of(b: &[u8]) -> Result<IpAddr, IoError> {
    decode_ip(b).ok_or_else(|| IoError::decode_uv_error(-22, None))
}

/// `uv_inet_pton` of the family (`IPv4Addr.ofString`, `IPv6Addr.ofString`,
/// lean-runtime's `semantics::net`): the address bytes, empty if `s` is not
/// an address of the family.
pub fn pton(s: &[u8], v6: bool) -> Vec<u8> {
    use lean_runtime::semantics::net as sn;
    if v6 {
        sn::pton_v6(s).map_or(Vec::new(), |g| g.iter().flat_map(|w| w.to_be_bytes()).collect())
    } else {
        sn::pton_v4(s).map_or(Vec::new(), |o| o.to_vec())
    }
}

/// `uv_inet_ntop` of an IP address in the shim's encoding (lean-runtime's).
pub fn ntop(a: &[u8]) -> Vec<u8> {
    use lean_runtime::semantics::net as sn;
    let mut s = String::new();
    let _ = match decode_ip(a) {
        Some(IpAddr::V4(x)) => sn::ntop_v4(x.octets(), &mut s),
        Some(IpAddr::V6(x)) => sn::ntop_v6(x.segments(), &mut s),
        None => Ok(()),
    };
    s.into_bytes()
}

// ---------------------------------------------------------------------------
// The loop, timers and signal watchers (lean-runtime's `sched::uv`)

/// `Loop.configure` (lean-runtime's `uv::loop_configure`).
pub fn loop_configure(accumulate_idle_time: bool, block_sigprof: bool) {
    let _ = uv::loop_configure(accumulate_idle_time, block_sigprof);
}

/// `Loop.alive` (lean-runtime's `uv::loop_alive`).
pub fn loop_alive() -> bool {
    uv::loop_alive()
}

/// A timer's or a signal watcher's promise as the loop holds it
/// (lean-runtime's `LoopPromise`): the program's promise `p` and the
/// completion of the operation that resolves it (the shim's continuation
/// resolves `p` with `()` or the signal's number). Clones are references;
/// the last one's drop gives up `p` (natively `lean_dec`: `p` resolves with
/// `none` only when the program's own references are gone too) and cancels
/// the operation.
#[derive(Clone)]
pub struct LoopP(Rc<LoopPInner>);

struct LoopPInner {
    p: LPromise,
    done: RefCell<Option<Completion>>,
    op: LHandle,
}

impl LoopPromise for LoopP {
    fn is_resolved(&self) -> bool {
        op(&self.0.op).done || crate::task::promise_resolved(crate::task::promise_cell(&self.0.p))
    }

    fn resolve(&self, value: i64) {
        let c = self.0.done.borrow_mut().take();
        if let Some(c) = c {
            c.finish(|o| o.code = value as i32);
        }
    }
}

/// `next` of a timer or a watcher: `next(new)` with a new loop promise over
/// `p` and `r`; the operation says whether the loop took it (`fresh`) or
/// gave the one it had (`promise`).
fn next_op(p: LPromise, r: LPromise, next: impl FnOnce(LoopP) -> Result<LoopP, i32>) -> LHandle {
    let o = op_new();
    let fresh = LoopP(Rc::new(LoopPInner { p, done: RefCell::new(Some(Completion::new(&o, r))), op: o.clone() }));
    let key = Rc::as_ptr(&fresh.0);
    match next(fresh) {
        Ok(got) => {
            let x = op(&o);
            if Rc::as_ptr(&got.0) == key {
                x.fresh = true;
            } else {
                x.promise = Some(got.0.p.clone());
            }
        }
        Err(code) => op(&o).start_err = Some(IoError::decode_uv_error(code, None)),
    }
    o
}

/// `Timer.mk timeout repeating`.
pub fn timer_new(timeout: u64, repeating: bool) -> LHandle {
    new_handle(Timer::<LoopP>::new(timeout, repeating))
}

/// `Timer.next`.
pub fn timer_next(t: &LHandle, p: LPromise, r: LPromise) -> LHandle {
    let t = get::<Timer<LoopP>>(t);
    next_op(p, r, |fresh| Ok(t.next(move || fresh)))
}

/// `Timer.reset` (0), `stop` (1), `cancel` (2).
pub fn timer_ctl(t: &LHandle, which: u8) {
    let t = get::<Timer<LoopP>>(t);
    match which {
        0 => t.reset(),
        1 => t.stop(),
        _ => t.cancel(),
    }
}

/// `Signal.mk signum repeating`.
pub fn signal_new(signum: i32, repeating: bool) -> LHandle {
    new_handle(Signal::<LoopP>::new(signum, repeating))
}

/// `Signal.next`.
pub fn signal_next(s: &LHandle, p: LPromise, r: LPromise) -> LHandle {
    let s = get::<Signal<LoopP>>(s);
    next_op(p, r, |fresh| s.next(move || fresh))
}

/// `Signal.stop` (1), `cancel` (2): the start's error (`stop` never fails).
pub fn signal_ctl(s: &LHandle, which: u8) -> LHandle {
    let s = get::<Signal<LoopP>>(s);
    if which == 1 {
        started(s.stop().map_err(|c| IoError::decode_uv_error(c, None)))
    } else {
        s.cancel();
        started(Ok(()))
    }
}

// ---------------------------------------------------------------------------
// Sockets (lean-runtime's `net::tcp`, `net::udp`)

/// A `send`'s buffers (Lean's `Array ByteArray`), held until the write is
/// done, as natively.
struct Bufs(RVec<RVec<u8>>);

impl SendData for Bufs {
    fn count(&self) -> usize {
        self.0.len()
    }
    fn get(&self, i: usize) -> &[u8] {
        self.0.as_slice()[i].as_slice()
    }
}

/// A receive's new `ByteArray` of `size` bytes (`lean_alloc_sarray(1, 0,
/// size)`, with Lean's checked arithmetic and internal panics), as a `Vec`
/// whose spare capacity lean-runtime reads into.
fn recv_buf(size: u64) -> Vec<u8> {
    crate::array::check_alloc(size, 1);
    let mut v = Vec::new();
    if v.try_reserve_exact(size as usize).is_err() {
        crate::lean_internal_panic(lean_runtime::semantics::panic::InternalPanic::OutOfMemory)
    }
    v
}

/// `TCP.Socket.new`: an operation with the socket as its handle, or with
/// lean-runtime's error (which libuv 1.48 never reports for `uv_tcp_init`;
/// natively it would be an `IO.Error` too).
pub fn tcp_new() -> LHandle {
    socket_op(TcpSocket::new().map(new_handle))
}

/// An operation holding a new socket's handle, or its start's error.
fn socket_op(r: Result<LHandle, IoError>) -> LHandle {
    match r {
        Ok(h) => {
            let o = op_new();
            op(&o).handle = Some(h);
            o
        }
        Err(e) => started(Err(e)),
    }
}

fn tcp(h: &LHandle) -> &TcpSocket {
    get::<TcpSocket>(h)
}

fn udp(h: &LHandle) -> &UdpSocket {
    get::<UdpSocket>(h)
}

pub fn tcp_bind(s: &LHandle, a: &[u8]) -> LHandle {
    started(addr_of(a).and_then(|a| tcp(s).bind(a)))
}

pub fn tcp_listen(s: &LHandle, backlog: u32) -> LHandle {
    started(tcp(s).listen(backlog))
}

pub fn tcp_connect(s: &LHandle, a: &[u8], r: LPromise) -> LHandle {
    pending(r, |c| tcp(s).connect(addr_of(a)?, move |res| c.result(res, |_, ()| {})))
}

pub fn tcp_send(s: &LHandle, data: RVec<RVec<u8>>, r: LPromise) -> LHandle {
    pending(r, |c| tcp(s).send(Bufs(data), move |res| c.result(res, |_, ()| {})))
}

/// `recv? size`: `some` bytes, or the end of the stream (`code` 1).
pub fn tcp_recv(s: &LHandle, size: u64, r: LPromise) -> LHandle {
    pending(r, |c| {
        tcp(s).recv(
            || recv_buf(size),
            move |res| {
                c.result(res, |o, got| match got {
                    Some((b, _)) => o.bytes = b,
                    None => o.code = 1,
                })
            },
        )
    })
}

/// `waitReadable`: `code` 1 when readable, 0 at the end of the stream.
pub fn tcp_wait_readable(s: &LHandle, r: LPromise) -> LHandle {
    pending(r, |c| tcp(s).wait_readable(move |res| c.result(res, |o, b| o.code = b as i32)))
}

pub fn tcp_cancel_recv(s: &LHandle) {
    tcp(s).cancel_recv()
}

/// `accept`: the connection's socket (`handle`).
pub fn tcp_accept(s: &LHandle, r: LPromise) -> LHandle {
    pending(r, |c| tcp(s).accept(move |res| c.result(res, |o, t| o.handle = Some(new_handle(t)))))
}

/// `tryAccept`: the connection's socket, if one is waiting.
pub fn tcp_try_accept(s: &LHandle) -> LHandle {
    let o = op_new();
    match tcp(s).try_accept() {
        Ok(t) => op(&o).handle = t.map(new_handle),
        Err(e) => op(&o).start_err = Some(e),
    }
    o
}

pub fn tcp_cancel_accept(s: &LHandle) {
    tcp(s).cancel_accept()
}

pub fn tcp_shutdown(s: &LHandle, r: LPromise) -> LHandle {
    pending(r, |c| tcp(s).shutdown(move |res| c.result(res, |_, ()| {})))
}

/// `getPeerName` / `getSockName` of a TCP (`udp` false) or UDP socket: the
/// address (`addr`).
pub fn sock_name(s: &LHandle, peer: bool, is_udp: bool) -> LHandle {
    let r = match (is_udp, peer) {
        (false, true) => tcp(s).peer_name(),
        (false, false) => tcp(s).sock_name(),
        (true, true) => udp(s).peer_name(),
        (true, false) => udp(s).sock_name(),
    };
    let o = op_new();
    match r {
        Ok(a) => op(&o).addr = encode_addr(&a),
        Err(e) => op(&o).start_err = Some(e),
    }
    o
}

pub fn tcp_nodelay(s: &LHandle) -> LHandle {
    started(tcp(s).no_delay())
}

pub fn tcp_keepalive(s: &LHandle, enable: i32, delay: u32) -> LHandle {
    started(tcp(s).keep_alive(enable, delay))
}

/// `UDP.Socket.new`, as `tcp_new`.
pub fn udp_new() -> LHandle {
    socket_op(UdpSocket::new().map(new_handle))
}

pub fn udp_bind(s: &LHandle, a: &[u8]) -> LHandle {
    started(addr_of(a).and_then(|a| udp(s).bind(a)))
}

pub fn udp_connect(s: &LHandle, a: &[u8]) -> LHandle {
    started(addr_of(a).and_then(|a| udp(s).connect(a)))
}

/// `send data addr?` (`a` empty: none).
pub fn udp_send(s: &LHandle, data: RVec<RVec<u8>>, a: &[u8], r: LPromise) -> LHandle {
    pending(r, |c| {
        let to = if a.is_empty() { None } else { Some(addr_of(a)?) };
        udp(s).send(Bufs(data), to, move |res| c.result(res, |_, ()| {}))
    })
}

/// `recv size`: the datagram (`bytes`) and its sender (`addr`, empty for
/// none).
pub fn udp_recv(s: &LHandle, size: u64, r: LPromise) -> LHandle {
    pending(r, |c| {
        udp(s).recv(
            || recv_buf(size),
            move |res| {
                c.result(res, |o, (b, _, from)| {
                    o.bytes = b;
                    o.addr = from.map_or(Vec::new(), |a| encode_addr(&a));
                })
            },
        )
    })
}

pub fn udp_wait_readable(s: &LHandle, r: LPromise) -> LHandle {
    pending(r, |c| udp(s).wait_readable(move |res| c.result(res, |_, ()| {})))
}

pub fn udp_cancel_recv(s: &LHandle) {
    udp(s).cancel_recv()
}

/// `setBroadcast` (0), `setMulticastLoop` (1), `setMulticastTTL` (2),
/// `setTTL` (3).
pub fn udp_option(s: &LHandle, which: u8, v: u32) -> LHandle {
    let u = udp(s);
    started(match which {
        0 => u.set_broadcast(v != 0),
        1 => u.set_multicast_loop(v != 0),
        2 => u.set_multicast_ttl(v),
        _ => u.set_ttl(v),
    })
}

/// `setMembership` (`iface` empty: none).
pub fn udp_membership(s: &LHandle, mcast: &[u8], iface: &[u8], membership: u8) -> LHandle {
    started((|| {
        let g = ip_of(mcast)?;
        let i = if iface.is_empty() { None } else { Some(ip_of(iface)?) };
        udp(s).set_membership(g, i, membership)
    })())
}

pub fn udp_multicast_interface(s: &LHandle, iface: &[u8]) -> LHandle {
    started(ip_of(iface).and_then(|i| udp(s).set_multicast_interface(i)))
}

// ---------------------------------------------------------------------------
// Name resolution and interfaces

/// `DNS.getAddrInfo`: the addresses (`bytes`, 17 bytes each).
pub fn dns_get_info(host: &[u8], service: &[u8], family: u8, r: LPromise) -> LHandle {
    // Lean strings are UTF-8.
    let host = String::from_utf8_lossy(host).into_owned();
    let service = String::from_utf8_lossy(service).into_owned();
    pending(r, |c| {
        dns::get_addr_info(&host, &service, family, move |res| {
            c.result(res, |o, v| {
                for a in v {
                    o.bytes.extend_from_slice(&encode_ip17(&a));
                }
            })
        })
    })
}

/// `DNS.getNameInfo`: the host and service names (`strs`).
pub fn dns_get_name(a: &[u8], r: LPromise) -> LHandle {
    pending(r, |c| {
        dns::get_name_info(addr_of(a)?, move |res| {
            c.result(res, |o, (h, s)| {
                o.strs.push(h.into_bytes());
                o.strs.push(s.into_bytes());
            })
        })
    })
}

/// `Std.Net.interfaceAddresses`: per address, its name (`strs`) and 41
/// bytes (`bytes`): the MAC address (6), whether it is a loopback one (1),
/// the address and the netmask (17 each).
pub fn ifaces() -> LHandle {
    let o = op_new();
    match iface::interface_addresses() {
        Ok(v) => {
            let x = op(&o);
            for a in v {
                x.strs.push(a.name.into_bytes());
                x.bytes.extend_from_slice(&a.physical_address);
                x.bytes.push(a.is_loopback as u8);
                x.bytes.extend_from_slice(&encode_ip17(&a.address));
                x.bytes.extend_from_slice(&encode_ip17(&a.netmask));
            }
        }
        Err(e) => op(&o).start_err = Some(e),
    }
    o
}
