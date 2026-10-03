//! The event loop: timers, sockets, name resolution and signals, for
//! `Std.Internal.UV` (natively libuv, `src/runtime/uv/*.cpp`, with its
//! loop on a thread of its own).
//!
//! Lean's `Std.Internal.UV` externs are implemented in Lean (lean2rr's shim
//! library `L2RShim`, compiled with the program); they call the primitives
//! here, which work on plain values. An operation that completes later
//! (a timer firing, a connection accepted, data received) works like this:
//! the shim makes a promise `r` (of `Unit`), starts the operation with it,
//! and attaches a continuation to `r` (a `sync` dependent, which runs where
//! `r` is resolved); when the operation completes, its outcome is stored in
//! its `Op` and the event loop drops `r`, which resolves it (with `none`:
//! `task::Promise`'s drop) and so runs the continuation, which reads the
//! `Op` and resolves the promise the program sees with a Lean value
//! (`Except IO.Error ...`), as libuv's callback does natively.
//!
//! Promises are dropped only on the event loop's context (`sched`), as
//! natively only libuv's thread resolves them. It runs when the program
//! blocks (`sched::schedule` polls the descriptors and timers when nothing
//! else can go on) and, for timers that are due and completions already
//! known, at the program's next output (`sched::effect`).
//!
//! Sockets follow libuv's Unix implementation (`src/unix/tcp.c`,
//! `stream.c`, `udp.c` of libuv 1.48): the descriptor is created on
//! `bind`/`connect`/`listen` with the address's family, nonblocking and
//! close-on-exec; `SO_REUSEADDR` is set before a TCP bind, whose
//! `EADDRINUSE` `listen` (or `connect`) reports instead; and so on. Errors
//! are libuv's codes (negated errnos, and its own), which the shim turns
//! into `IO.Error`s as `lean_decode_uv_error` does (`uv_error_kind`,
//! `uv_strerror`).

use crate::fs::LHandle;
use crate::sched;
use crate::task::LPromise;
use std::cell::UnsafeCell;
use std::ffi::c_void;
use std::time::{Duration, Instant};

struct Global<T>(UnsafeCell<T>);
unsafe impl<T> Sync for Global<T> {}

// ---------------------------------------------------------------------------
// libc

#[repr(C)]
#[derive(Clone, Copy)]
pub struct SockAddrStorage {
    pub family: u16,
    pub data: [u8; 126],
}

const EMPTY_ADDR: SockAddrStorage = SockAddrStorage { family: 0, data: [0; 126] };

#[repr(C)]
struct PollFd {
    fd: i32,
    events: i16,
    revents: i16,
}

#[repr(C)]
struct AddrInfo {
    ai_flags: i32,
    ai_family: i32,
    ai_socktype: i32,
    ai_protocol: i32,
    ai_addrlen: u32,
    ai_addr: *mut SockAddrStorage,
    ai_canonname: *mut std::ffi::c_char,
    ai_next: *mut AddrInfo,
}

#[repr(C)]
struct SigAction {
    sa_handler: usize,
    sa_mask: [u64; 16],
    sa_flags: i32,
    sa_restorer: usize,
}

extern "C" {
    fn socket(domain: i32, ty: i32, proto: i32) -> i32;
    fn bind(fd: i32, addr: *const SockAddrStorage, len: u32) -> i32;
    fn listen(fd: i32, backlog: i32) -> i32;
    fn accept4(fd: i32, addr: *mut SockAddrStorage, len: *mut u32, flags: i32) -> i32;
    fn connect(fd: i32, addr: *const SockAddrStorage, len: u32) -> i32;
    fn getsockopt(fd: i32, level: i32, name: i32, val: *mut c_void, len: *mut u32) -> i32;
    fn setsockopt(fd: i32, level: i32, name: i32, val: *const c_void, len: u32) -> i32;
    fn getsockname(fd: i32, addr: *mut SockAddrStorage, len: *mut u32) -> i32;
    fn getpeername(fd: i32, addr: *mut SockAddrStorage, len: *mut u32) -> i32;
    fn read(fd: i32, buf: *mut c_void, n: usize) -> isize;
    fn send(fd: i32, buf: *const c_void, n: usize, flags: i32) -> isize;
    fn recvfrom(fd: i32, buf: *mut c_void, n: usize, flags: i32, addr: *mut SockAddrStorage, len: *mut u32) -> isize;
    fn sendto(fd: i32, buf: *const c_void, n: usize, flags: i32, addr: *const SockAddrStorage, len: u32) -> isize;
    fn shutdown(fd: i32, how: i32) -> i32;
    fn close(fd: i32) -> i32;
    fn poll(fds: *mut PollFd, n: u64, timeout: i32) -> i32;
    fn getaddrinfo(node: *const std::ffi::c_char, service: *const std::ffi::c_char, hints: *const AddrInfo, res: *mut *mut AddrInfo) -> i32;
    fn freeaddrinfo(res: *mut AddrInfo);
    fn getnameinfo(addr: *const SockAddrStorage, len: u32, host: *mut std::ffi::c_char, hostlen: u32, serv: *mut std::ffi::c_char, servlen: u32, flags: i32) -> i32;
    fn pipe2(fds: *mut i32, flags: i32) -> i32;
    fn sigaction(sig: i32, act: *const SigAction, old: *mut SigAction) -> i32;
}

fn errno() -> i32 {
    crate::cfile::errno_now()
}

const AF_INET: i32 = 2;
const AF_INET6: i32 = 10;
const SOCK_STREAM: i32 = 1;
const SOCK_DGRAM: i32 = 2;
const SOCK_NONBLOCK: i32 = 0o4000;
const SOCK_CLOEXEC: i32 = 0o2000000;
const SOL_SOCKET: i32 = 1;
const SO_REUSEADDR: i32 = 2;
const SO_ERROR: i32 = 4;
const SO_BROADCAST: i32 = 6;
const SO_KEEPALIVE: i32 = 9;
const IPPROTO_IP: i32 = 0;
const IPPROTO_TCP: i32 = 6;
const IPPROTO_IPV6: i32 = 41;
const TCP_NODELAY: i32 = 1;
const TCP_KEEPIDLE: i32 = 4;
const TCP_KEEPINTVL: i32 = 5;
const TCP_KEEPCNT: i32 = 6;
const IP_TTL: i32 = 2;
const IP_MULTICAST_IF: i32 = 32;
const IP_MULTICAST_TTL: i32 = 33;
const IP_MULTICAST_LOOP: i32 = 34;
const IP_ADD_MEMBERSHIP: i32 = 35;
const IP_DROP_MEMBERSHIP: i32 = 36;
const IPV6_UNICAST_HOPS: i32 = 16;
const IPV6_MULTICAST_IF: i32 = 17;
const IPV6_MULTICAST_HOPS: i32 = 18;
const IPV6_MULTICAST_LOOP: i32 = 19;
const IPV6_ADD_MEMBERSHIP: i32 = 20;
const IPV6_DROP_MEMBERSHIP: i32 = 21;
const IPV6_V6ONLY: i32 = 26;
const SHUT_WR: i32 = 1;
const MSG_NOSIGNAL: i32 = 0x4000;
const POLLIN: i16 = 1;
const POLLOUT: i16 = 4;
const POLLERR: i16 = 8;
const POLLHUP: i16 = 16;
const EINTR: i32 = 4;
const EAGAIN: i32 = 11;
const EAFNOSUPPORT: i32 = 97;
const EADDRINUSE: i32 = 98;
const ECONNABORTED: i32 = 103;
const ECONNREFUSED: i32 = 111;
const EINPROGRESS: i32 = 115;

// libuv's error codes (negated errnos, and its own).
pub const UV_EOF: i32 = -4095;
const UV_UNKNOWN: i32 = -4094;
const UV_EBADF: i32 = -9;
const UV_EINVAL: i32 = -22;
const UV_EPIPE: i32 = -32;
const UV_EDESTADDRREQ: i32 = -89;
const UV_ENOBUFS: i32 = -105;
const UV_EISCONN: i32 = -106;
const UV_ENOTCONN: i32 = -107;
const UV_EALREADY: i32 = -114;

fn uv_err(e: i32) -> i32 {
    -e
}

// ---------------------------------------------------------------------------
// Addresses. The shim passes a `SocketAddress` as bytes: the family (4 or
// 6), the port (big-endian), then the 4 or 16 bytes of the address; an
// `IPAddr` without the port.

/// A socket address from the shim's encoding, and its length.
pub fn decode_addr(b: &[u8]) -> Option<(SockAddrStorage, u32)> {
    let mut s = EMPTY_ADDR;
    match b.first() {
        Some(4) if b.len() >= 7 => {
            s.family = AF_INET as u16;
            s.data[0] = b[1];
            s.data[1] = b[2];
            s.data[2..6].copy_from_slice(&b[3..7]);
            Some((s, 16))
        }
        Some(6) if b.len() >= 19 => {
            s.family = AF_INET6 as u16;
            s.data[0] = b[1];
            s.data[1] = b[2];
            // `sin6_flowinfo` stays 0; then the address.
            s.data[6..22].copy_from_slice(&b[3..19]);
            Some((s, 28))
        }
        _ => None,
    }
}

/// The shim's encoding of a socket address (empty for another family).
pub fn encode_addr(s: &SockAddrStorage) -> Vec<u8> {
    match s.family as i32 {
        AF_INET => {
            let mut v = vec![4, s.data[0], s.data[1]];
            v.extend_from_slice(&s.data[2..6]);
            v
        }
        AF_INET6 => {
            let mut v = vec![6, s.data[0], s.data[1]];
            v.extend_from_slice(&s.data[6..22]);
            v
        }
        _ => Vec::new(),
    }
}

fn same(a: &LHandle, b: &LHandle) -> bool {
    std::ptr::eq(&**a as *const Box<dyn std::any::Any> as *const u8, &**b as *const Box<dyn std::any::Any> as *const u8)
}

// ---------------------------------------------------------------------------
// Operations

/// An operation's outcome, which the shim's continuation reads.
#[derive(Default)]
pub struct OpSt {
    /// Completed (before its start returned, or later).
    pub done: bool,
    /// Canceled: the continuation does nothing.
    pub canceled: bool,
    /// The result: a libuv error (< 0), or a value (bytes read, a signal).
    pub code: i32,
    /// An error its start reports at once (the extern throws it).
    pub sync_err: i32,
    pub bytes: Vec<u8>,
    pub handle: Option<LHandle>,
    pub addr: Vec<u8>,
    pub strs: Vec<Vec<u8>>,
}

pub fn op_new() -> LHandle {
    reussir_rt::rc::Rc::new(Box::new(UnsafeCell::new(OpSt::default())) as Box<dyn std::any::Any>)
}

pub fn op(h: &LHandle) -> &'static mut OpSt {
    let c = h.downcast_ref::<UnsafeCell<OpSt>>().expect("leanrt: not an operation");
    unsafe { &mut *c.get() }
}

/// A pending operation: its outcome and the promise to drop when it
/// completes.
struct Pending {
    op: LHandle,
    ready: LPromise,
}

impl Pending {
    fn new(o: &LHandle, ready: LPromise) -> Pending {
        Pending { op: o.clone(), ready }
    }
    fn complete(self, code: i32) {
        let o = op(&self.op);
        o.done = true;
        o.code = code;
        fire(self.ready);
    }
    fn cancel(self) {
        fire(self.cancel_here());
    }
    /// Cancel, returning the promise for the caller to drop (its
    /// continuation does nothing).
    fn cancel_here(self) -> LPromise {
        let o = op(&self.op);
        o.done = true;
        o.canceled = true;
        self.ready
    }
}

/// Promises a primitive gave up, for its caller to drop once the primitive
/// has returned (`timer_stop`): the continuation of a canceled operation,
/// then the program's promise.
pub type GivenUp = [Option<LPromise>; 2];

/// Complete operation `o` (its promise `r`) now: the continuation runs on
/// the event loop's context (as a libuv callback on its next iteration).
pub fn complete_now(o: &LHandle, r: LPromise, code: i32) {
    Pending::new(o, r).complete(code)
}

// ---------------------------------------------------------------------------
// The reactor

struct Reactor {
    /// Promises to drop (their operations have completed), in order.
    fired: Vec<LPromise>,
    /// Running timers.
    timers: Vec<LHandle>,
    /// Sockets with pending operations.
    sockets: Vec<LHandle>,
    /// Started signal watchers.
    signals: Vec<LHandle>,
    /// The signal handler's pipe (-1 before the first signal watcher).
    sig_pipe: [i32; 2],
}

static REACTOR: Global<Reactor> = Global(UnsafeCell::new(Reactor {
    fired: Vec::new(),
    timers: Vec::new(),
    sockets: Vec::new(),
    signals: Vec::new(),
    sig_pipe: [-1, -1],
}));

fn reactor() -> &'static mut Reactor {
    unsafe { &mut *REACTOR.0.get() }
}

/// Queue `r` to be dropped on the event loop's context.
fn fire(r: LPromise) {
    sched::ensure_evloop();
    reactor().fired.push(r);
    sched::wake_evloop();
}

/// Give up a promise the runtime held: it is dropped on the event loop's
/// context, like a completion (dropping the last reference resolves it with
/// `none` and runs its dependents, which must not run inside a primitive).
pub fn release(p: LPromise) {
    fire(p)
}

/// A promise an operation's start received: given up through the event
/// loop unless the operation keeps it (`take`).
struct Ready(Option<LPromise>);

impl Ready {
    fn take(&mut self) -> LPromise {
        self.0.take().expect("leanrt: promise taken twice")
    }
}

impl Drop for Ready {
    fn drop(&mut self) {
        if let Some(p) = self.0.take() {
            release(p);
        }
    }
}

/// At an effect point: what the event loop would have seen by now (ready
/// descriptors, signals, due timers), without waiting; whether something
/// is to be delivered.
pub fn poll_now() -> bool {
    let r = reactor();
    if r.sockets.is_empty() && r.signals.is_empty() {
        return false;
    }
    wait(Some(Duration::ZERO));
    has_fired()
}

/// Whether completions wait to be delivered.
pub fn has_fired() -> bool {
    !reactor().fired.is_empty()
}

/// On the event loop's context: drop the promises of completed operations,
/// which runs their continuations.
pub fn deliver() {
    loop {
        let f = std::mem::take(&mut reactor().fired);
        if f.is_empty() {
            return;
        }
        for r in f {
            drop(r);
        }
    }
}

/// Whether something is due now: completions to deliver or a timer
/// (`sched::effect`).
pub fn due(now: Instant) -> bool {
    let r = unsafe { &*REACTOR.0.get() };
    !r.fired.is_empty() || r.timers.iter().any(|t| timer(t).state == RUNNING && timer(t).due <= now)
}

/// Fire the timers that are due now (`sched::effect`).
pub fn process_due(now: Instant) {
    run_timers(now);
}

/// The scheduler has nothing else to do: wait (at most `timeout`; without
/// one, until something happens) for the timers, sockets and signals the
/// event loop watches, and handle what happens. False if it watches
/// nothing (nothing can happen here). Completions waiting to be delivered
/// make the event loop's context able to run, and then nothing is waited
/// for; while that context waits for something else (inside a `sync`
/// continuation), they wait for it, and this waits as usual.
pub fn wait(timeout: Option<Duration>) -> bool {
    let r = reactor();
    if !r.fired.is_empty() && sched::wake_evloop() {
        return true;
    }
    if r.timers.is_empty() && r.sockets.is_empty() && r.signals.is_empty() {
        return false;
    }
    let now = Instant::now();
    let mut t = timeout;
    for h in &r.timers {
        let tm = timer(h);
        if tm.state == RUNNING {
            let d = tm.due.saturating_duration_since(now);
            t = Some(t.map_or(d, |x| x.min(d)));
        }
    }
    let mut fds: Vec<PollFd> = Vec::new();
    let mut who: Vec<Option<LHandle>> = Vec::new();
    for h in r.sockets.iter() {
        let s = sock(h);
        let ev = s.interest();
        if ev != 0 && s.fd >= 0 {
            fds.push(PollFd { fd: s.fd, events: ev, revents: 0 });
            who.push(Some(h.clone()));
        }
    }
    if !r.signals.is_empty() && r.sig_pipe[0] >= 0 {
        fds.push(PollFd { fd: r.sig_pipe[0], events: POLLIN, revents: 0 });
        who.push(None);
    }
    if fds.is_empty() && t.is_none() {
        return false;
    }
    let ms = match t {
        None => -1,
        Some(d) => d.as_nanos().div_ceil(1_000_000).min(i32::MAX as u128) as i32,
    };
    let n = unsafe { poll(fds.as_mut_ptr(), fds.len() as u64, ms) };
    if n > 0 {
        for (k, pf) in fds.iter().enumerate() {
            if pf.revents == 0 {
                continue;
            }
            match &who[k] {
                Some(h) => handle_ready(h, pf.revents),
                None => read_signals(),
            }
        }
    }
    reactor().sockets.retain(|h| sock(h).has_pending());
    run_timers(Instant::now());
    true
}

// ---------------------------------------------------------------------------
// Timers (`uv/timer.cpp`) and signal watchers (`uv/signal.cpp`): the same
// state machine.

const INITIAL: u8 = 0;
const RUNNING: u8 = 1;
const FINISHED: u8 = 2;

pub struct Timer {
    timeout: u64,
    repeating: bool,
    state: u8,
    /// The promise of the current `next` (`m_promise`).
    promise: Option<LPromise>,
    /// Its operation, until the timer fires for it.
    pending: Option<Pending>,
    due: Instant,
    /// A signal watcher's signal (0 for a timer).
    signum: i32,
}

fn timer(h: &LHandle) -> &'static mut Timer {
    let c = h.downcast_ref::<UnsafeCell<Timer>>().expect("leanrt: not a timer");
    unsafe { &mut *c.get() }
}

fn new_timer(timeout: u64, repeating: bool, signum: i32) -> LHandle {
    reussir_rt::rc::Rc::new(Box::new(UnsafeCell::new(Timer {
        timeout,
        repeating,
        state: INITIAL,
        promise: None,
        pending: None,
        due: Instant::now(),
        signum,
    })) as Box<dyn std::any::Any>)
}

pub fn timer_new(timeout: u64, repeating: bool) -> LHandle {
    new_timer(timeout, repeating, 0)
}

fn promise_resolved(p: &LPromise) -> bool {
    crate::task::status(crate::task::promise_cell(p)) == 2
}

/// What `next` does (`lean_uv_timer_next`, `lean_uv_signal_next`): 0 start
/// with a new promise (`timer_start`), 1 return the current promise
/// (`timer_promise`), 2 a new promise for the next tick of a running
/// repeating timer (`timer_set`), 3 a new promise that nothing resolves.
pub fn timer_next_kind(h: &LHandle) -> u8 {
    let t = timer(h);
    let finished = match &t.promise {
        None => true,
        Some(p) => promise_resolved(p),
    };
    match (t.repeating, t.state) {
        (_, INITIAL) => 0,
        (true, RUNNING) => {
            if finished {
                2
            } else {
                1
            }
        }
        _ => {
            if t.promise.is_some() {
                1
            } else {
                3
            }
        }
    }
}

pub fn timer_promise(h: &LHandle) -> LPromise {
    timer(h).promise.clone().expect("leanrt: timer without promise")
}

/// Set the current promise `p` (resolved through `r`) of timer `h`.
fn timer_set_promise(h: &LHandle, p: LPromise, r: LPromise) -> LHandle {
    let o = op_new();
    let t = timer(h);
    if let Some(old) = t.promise.replace(p) {
        release(old);
    }
    if let Some(old) = t.pending.take() {
        old.cancel();
    }
    t.pending = Some(Pending::new(&o, r));
    o
}

/// Start timer `h` for its first `next`: promise `p`, resolved through `r`
/// (the operation returned is its outcome). A signal watcher whose signal
/// Lean does not know fails (`EINVAL`, `uv_signal_start`): its `sync_err`.
pub fn timer_start(h: &LHandle, p: LPromise, r: LPromise) -> LHandle {
    let t = timer(h);
    if t.signum < 0 {
        let o = op_new();
        op(&o).sync_err = UV_EINVAL;
        release(p);
        release(r);
        return o;
    }
    let o = timer_set_promise(h, p, r);
    let t = timer(h);
    t.state = RUNNING;
    if t.signum != 0 {
        signal_start(h);
    } else {
        // A repeating timer ticks at once, then every `timeout` ms.
        let first = if t.repeating { 0 } else { t.timeout };
        t.due = Instant::now() + Duration::from_millis(first);
        add_timer(h);
    }
    o
}

/// A new promise for the next tick of a running repeating timer.
pub fn timer_set(h: &LHandle, p: LPromise, r: LPromise) -> LHandle {
    timer_set_promise(h, p, r)
}

fn add_timer(h: &LHandle) {
    sched::ensure_evloop();
    let r = reactor();
    if !r.timers.iter().any(|x| same(x, h)) {
        r.timers.push(h.clone());
    }
}

fn remove_timer(h: &LHandle) {
    reactor().timers.retain(|x| !same(x, h));
}

/// `reset`: a running timer starts counting again (`uv_timer_start`, also
/// after a period-0 timer fired its one tick).
pub fn timer_reset(h: &LHandle) {
    let t = timer(h);
    if t.state == RUNNING && t.signum == 0 {
        t.due = Instant::now() + Duration::from_millis(t.timeout);
        add_timer(h);
    }
}

/// `stop`: the current promise is dropped unresolved, and a running timer
/// finishes. The promise (and the continuation that held it) are returned:
/// the caller drops them once the primitive has returned
/// (`l2r_shim_timer_ctl_h`), on its own context, as natively
/// `lean_uv_timer_stop` releases the promise on the calling thread (its
/// `sync` dependents run there, before `stop` returns).
pub fn timer_stop(h: &LHandle) -> GivenUp {
    let t = timer(h);
    let old = t.promise.take();
    let r = t.pending.take().map(Pending::cancel_here);
    if t.state == RUNNING {
        t.state = FINISHED;
        if t.signum != 0 {
            signal_stop(h);
        } else {
            remove_timer(h);
        }
    }
    [r, old]
}

/// `cancel`: a running repeating timer drops its promise and goes on; a
/// one-shot one stops and can be started again. The promises are returned,
/// for the caller to drop (as `timer_stop`).
pub fn timer_cancel(h: &LHandle) -> GivenUp {
    let t = timer(h);
    if t.state == RUNNING && t.promise.is_some() {
        let old = t.promise.take();
        let r = t.pending.take().map(Pending::cancel_here);
        if !t.repeating {
            t.state = INITIAL;
            if t.signum != 0 {
                signal_stop(h);
            } else {
                remove_timer(h);
            }
        }
        return [r, old];
    }
    [None, None]
}

/// A timer or signal watcher fires (`handle_timer_event`,
/// `handle_signal_event`), resolving its promise with `code`.
fn fire_timer(h: &LHandle, code: i32) {
    let t = timer(h);
    if t.repeating {
        let open = match &t.promise {
            Some(p) => !promise_resolved(p),
            None => false,
        };
        if open {
            if let Some(pd) = t.pending.take() {
                pd.complete(code);
            }
        }
    } else {
        if let Some(pd) = t.pending.take() {
            pd.complete(code);
        }
        t.state = FINISHED;
        if t.signum != 0 {
            signal_stop(h);
        } else {
            remove_timer(h);
        }
    }
}

/// Fire the timers that are due (in the order of their deadlines).
fn run_timers(now: Instant) {
    let mut due: Vec<LHandle> =
        reactor().timers.iter().filter(|h| timer(h).state == RUNNING && timer(h).due <= now).cloned().collect();
    due.sort_by_key(|h| timer(h).due);
    for h in due {
        let t = timer(&h);
        if t.state != RUNNING || t.due > now {
            continue;
        }
        // libuv reschedules a repeating timer from the time it fires
        // (`uv_timer_again`), unless its repeat is 0: started with timeout 0
        // and repeat 0, it has fired once, as a one-shot (Lean's state stays
        // running).
        if t.repeating && t.timeout == 0 {
            remove_timer(&h);
        } else {
            t.due = now + Duration::from_millis(t.timeout);
        }
        fire_timer(&h, 0);
    }
}

// ---- signals ----

static SIG_WRITE_FD: std::sync::atomic::AtomicI32 = std::sync::atomic::AtomicI32::new(-1);

extern "C" fn on_signal(signum: i32) {
    let fd = SIG_WRITE_FD.load(std::sync::atomic::Ordering::Relaxed);
    if fd >= 0 {
        let b = signum as u8;
        let saved = errno();
        crate::fs::raw_write(fd, &b as *const u8 as *const c_void, 1);
        crate::cfile::set_errno(saved);
    }
}

const SA_RESTART: i32 = 0x1000_0000;

/// A signal watcher (`Std.Internal.UV.Signal.mk`): Lean's numbers for the
/// signals it knows are Linux's; any other is invalid (`next` then fails
/// with `EINVAL`).
pub fn signal_new(n: u32, repeating: bool) -> LHandle {
    let s = match n as i32 {
        1 | 2 | 3 | 5 | 6 | 10 | 12 | 14 | 15 | 17 | 18 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 31 => n as i32,
        _ => -1,
    };
    new_timer(0, repeating, s)
}

fn signal_start(h: &LHandle) {
    let r = reactor();
    if r.sig_pipe[0] < 0 {
        // libuv's loop signal pipe, opened at startup (`rt`), as natively.
        let p = crate::rt::signal_pipe().unwrap_or_else(|| {
            let mut p = [-1i32; 2];
            unsafe { pipe2(p.as_mut_ptr(), SOCK_NONBLOCK | SOCK_CLOEXEC) };
            p
        });
        r.sig_pipe = p;
        SIG_WRITE_FD.store(p[1], std::sync::atomic::Ordering::Relaxed);
    }
    if !r.signals.iter().any(|x| same(x, h)) {
        r.signals.push(h.clone());
    }
    sched::ensure_evloop();
    let act = SigAction { sa_handler: on_signal as *const () as usize, sa_mask: [0; 16], sa_flags: SA_RESTART, sa_restorer: 0 };
    unsafe { sigaction(timer(h).signum, &act, std::ptr::null_mut()) };
}

fn signal_stop(h: &LHandle) {
    let signum = timer(h).signum;
    let r = reactor();
    r.signals.retain(|x| !same(x, h));
    if !r.signals.iter().any(|x| timer(x).signum == signum) {
        // The default disposition is back (libuv restores the old one).
        let act = SigAction { sa_handler: 0, sa_mask: [0; 16], sa_flags: 0, sa_restorer: 0 };
        unsafe { sigaction(signum, &act, std::ptr::null_mut()) };
    }
}

fn read_signals() {
    let mut buf = [0u8; 64];
    loop {
        let n = unsafe { read(reactor().sig_pipe[0], buf.as_mut_ptr() as *mut c_void, buf.len()) };
        if n <= 0 {
            break;
        }
        for &b in &buf[..n as usize] {
            let ws: Vec<LHandle> =
                reactor().signals.iter().filter(|h| timer(h).signum == b as i32 && timer(h).state == RUNNING).cloned().collect();
            for h in ws {
                fire_timer(&h, b as i32);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Sockets

const TCP: u8 = 0;
const UDP: u8 = 1;

// The handle flags of libuv that matter here.
const F_BOUND: u32 = 1;
const F_READABLE: u32 = 2;
const F_WRITABLE: u32 = 4;
const F_SHUT: u32 = 8;
const F_NODELAY: u32 = 16;
const F_KEEPALIVE: u32 = 32;
const F_UDP_CONNECTED: u32 = 64;

struct Write {
    data: Vec<u8>,
    off: usize,
    dest: Option<(SockAddrStorage, u32)>,
    pending: Pending,
}

pub struct Socket {
    kind: u8,
    fd: i32,
    flags: u32,
    /// libuv's `delayed_error` (a TCP bind's `EADDRINUSE`).
    delayed_error: i32,
    keepalive_delay: u32,
    connect: Option<Pending>,
    accept: Option<Pending>,
    /// A read and its size (0: `waitReadable`).
    read: Option<(Pending, u64)>,
    writes: std::collections::VecDeque<Write>,
    shutdown: Option<Pending>,
}

impl Socket {
    fn interest(&self) -> i16 {
        let mut ev = 0;
        if self.accept.is_some() || self.read.is_some() {
            ev |= POLLIN;
        }
        if self.connect.is_some() || !self.writes.is_empty() {
            ev |= POLLOUT;
        }
        ev
    }
    fn has_pending(&self) -> bool {
        self.connect.is_some() || self.accept.is_some() || self.read.is_some() || !self.writes.is_empty() || self.shutdown.is_some()
    }
}

impl Drop for Socket {
    fn drop(&mut self) {
        if self.fd >= 0 {
            unsafe { close(self.fd) };
        }
    }
}

fn sock(h: &LHandle) -> &'static mut Socket {
    let c = h.downcast_ref::<UnsafeCell<Socket>>().expect("leanrt: not a socket");
    unsafe { &mut *c.get() }
}

fn new_socket(kind: u8, fd: i32, flags: u32) -> LHandle {
    reussir_rt::rc::Rc::new(Box::new(UnsafeCell::new(Socket {
        kind,
        fd,
        flags,
        delayed_error: 0,
        keepalive_delay: 0,
        connect: None,
        accept: None,
        read: None,
        writes: std::collections::VecDeque::new(),
        shutdown: None,
    })) as Box<dyn std::any::Any>)
}

pub fn tcp_new() -> LHandle {
    new_socket(TCP, -1, 0)
}

pub fn udp_new() -> LHandle {
    new_socket(UDP, -1, 0)
}

/// Watch socket `h`: it has a pending operation.
fn watch(h: &LHandle) {
    sched::ensure_evloop();
    let r = reactor();
    if !r.sockets.iter().any(|x| same(x, h)) {
        r.sockets.push(h.clone());
    }
}

fn set_int(fd: i32, level: i32, name: i32, v: i32) -> i32 {
    let r = unsafe { setsockopt(fd, level, name, &v as *const i32 as *const c_void, 4) };
    if r != 0 {
        uv_err(errno())
    } else {
        0
    }
}

/// `uv__tcp_keepalive`.
fn keepalive_fd(fd: i32, on: bool, delay: u32) -> i32 {
    let e = set_int(fd, SOL_SOCKET, SO_KEEPALIVE, on as i32);
    if e != 0 || !on {
        return e;
    }
    for (name, v) in [(TCP_KEEPIDLE, delay as i32), (TCP_KEEPINTVL, 1), (TCP_KEEPCNT, 10)] {
        let e = set_int(fd, IPPROTO_TCP, name, v);
        if e != 0 {
            return e;
        }
    }
    0
}

/// libuv's `maybe_new_socket`: a descriptor of `family` for a socket that
/// has none (with the options set on the handle before), and `flags`.
fn ensure_fd(s: &mut Socket, family: i32, flags: u32) -> i32 {
    if s.fd >= 0 {
        s.flags |= flags;
        return 0;
    }
    let ty = if s.kind == TCP { SOCK_STREAM } else { SOCK_DGRAM };
    let fd = unsafe { socket(family, ty | SOCK_NONBLOCK | SOCK_CLOEXEC, 0) };
    if fd < 0 {
        return uv_err(errno());
    }
    s.fd = fd;
    s.flags |= flags;
    if s.kind == TCP {
        if s.flags & F_NODELAY != 0 {
            let e = set_int(fd, IPPROTO_TCP, TCP_NODELAY, 1);
            if e != 0 {
                return e;
            }
        }
        if s.flags & F_KEEPALIVE != 0 {
            let e = keepalive_fd(fd, true, s.keepalive_delay);
            if e != 0 {
                return e;
            }
        }
    }
    0
}

/// `uv_tcp_bind` (no flags).
pub fn tcp_bind(h: &LHandle, a: &[u8]) -> i32 {
    let s = sock(h);
    let Some((sa, len)) = decode_addr(a) else { return UV_EINVAL };
    let fam = sa.family as i32;
    let e = ensure_fd(s, fam, 0);
    if e != 0 {
        return e;
    }
    let e = set_int(s.fd, SOL_SOCKET, SO_REUSEADDR, 1);
    if e != 0 {
        return e;
    }
    if fam == AF_INET6 {
        let e = set_int(s.fd, IPPROTO_IPV6, IPV6_V6ONLY, 0);
        if e != 0 {
            return e;
        }
    }
    let r = unsafe { bind(s.fd, &sa, len) };
    let er = errno();
    if r == -1 && er != EADDRINUSE {
        return if er == EAFNOSUPPORT { UV_EINVAL } else { uv_err(er) };
    }
    s.delayed_error = if r == -1 { uv_err(er) } else { 0 };
    s.flags |= F_BOUND;
    0
}

/// `uv_listen` on a TCP socket.
pub fn tcp_listen(h: &LHandle, backlog: i32) -> i32 {
    let s = sock(h);
    if s.delayed_error != 0 {
        return s.delayed_error;
    }
    let e = ensure_fd(s, AF_INET, 0);
    if e != 0 {
        return e;
    }
    if unsafe { listen(s.fd, backlog) } != 0 {
        return uv_err(errno());
    }
    s.flags |= F_BOUND;
    0
}

/// `uv_tcp_connect`: `sync_err` if it fails at once.
pub fn tcp_connect(h: &LHandle, a: &[u8], r: LPromise) -> LHandle {
    let o = op_new();
    let mut r = Ready(Some(r));
    let s = sock(h);
    let Some((sa, len)) = decode_addr(a) else {
        op(&o).sync_err = UV_EINVAL;
        return o;
    };
    if s.connect.is_some() {
        op(&o).sync_err = UV_EALREADY;
        return o;
    }
    let p = Pending::new(&o, r.take());
    if s.delayed_error != 0 {
        let e = std::mem::replace(&mut s.delayed_error, 0);
        p.complete(e);
        return o;
    }
    let e = ensure_fd(s, sa.family as i32, F_READABLE | F_WRITABLE);
    if e != 0 {
        op(&o).sync_err = e;
        return o;
    }
    let rc = loop {
        let rc = unsafe { connect(s.fd, &sa, len) };
        if rc == -1 && errno() == EINTR {
            continue;
        }
        break rc;
    };
    if rc == -1 {
        let er = errno();
        if er == ECONNREFUSED {
            // Reported on the next tick.
            p.complete(uv_err(er));
            return o;
        }
        if er != EINPROGRESS {
            op(&o).sync_err = uv_err(er);
            return o;
        }
    }
    s.connect = Some(p);
    watch(h);
    o
}

/// `uv_write` of `data` (the shim joins the buffers).
pub fn tcp_send(h: &LHandle, data: Vec<u8>, r: LPromise) -> LHandle {
    let o = op_new();
    let mut r = Ready(Some(r));
    let s = sock(h);
    if s.fd < 0 {
        op(&o).sync_err = UV_EBADF;
        return o;
    }
    if s.flags & F_WRITABLE == 0 {
        op(&o).sync_err = UV_EPIPE;
        return o;
    }
    s.writes.push_back(Write { data, off: 0, dest: None, pending: Pending::new(&o, r.take()) });
    if s.connect.is_none() {
        flush_writes(h);
    }
    if s.has_pending() {
        watch(h);
    }
    o
}

/// Write what can be written of the queued writes, completing them; then
/// a pending shutdown (`uv__drain`).
fn flush_writes(h: &LHandle) {
    let s = sock(h);
    while let Some(w) = s.writes.front_mut() {
        let rest = &w.data[w.off..];
        let n = if s.kind == UDP {
            let (ap, al) = match &w.dest {
                Some((a, l)) => (a as *const SockAddrStorage, *l),
                None => (std::ptr::null(), 0),
            };
            unsafe { sendto(s.fd, rest.as_ptr() as *const c_void, rest.len(), MSG_NOSIGNAL, ap, al) }
        } else if rest.is_empty() {
            0
        } else {
            unsafe { send(s.fd, rest.as_ptr() as *const c_void, rest.len(), MSG_NOSIGNAL) }
        };
        if n < 0 {
            let er = errno();
            if er == EAGAIN || er == EINTR {
                return;
            }
            // This write fails, and the ones queued after it.
            let code = uv_err(er);
            while let Some(w) = s.writes.pop_front() {
                w.pending.complete(code);
            }
            break;
        }
        w.off += n as usize;
        if w.off >= w.data.len() || s.kind == UDP {
            let w = s.writes.pop_front().unwrap();
            w.pending.complete(0);
        }
    }
    if s.writes.is_empty() {
        if let Some(p) = s.shutdown.take() {
            let rc = unsafe { shutdown(s.fd, SHUT_WR) };
            let code = if rc != 0 { uv_err(errno()) } else { 0 };
            s.flags |= F_SHUT;
            s.flags &= !F_WRITABLE;
            p.complete(code);
        }
    }
}

/// `uv_read_start` (or `uv_udp_recv_start`) for one read of at most `size`
/// bytes; `size` 0 waits until the socket is readable (`waitReadable`).
pub fn sock_recv(h: &LHandle, size: u64, r: LPromise) -> LHandle {
    let o = op_new();
    let mut r = Ready(Some(r));
    let s = sock(h);
    if s.read.is_some() {
        op(&o).sync_err = UV_EALREADY;
        return o;
    }
    if s.kind == TCP {
        if s.flags & F_READABLE == 0 {
            op(&o).sync_err = UV_ENOTCONN;
            return o;
        }
    } else {
        let e = udp_deferred_bind(s, AF_INET);
        if e != 0 {
            op(&o).sync_err = e;
            return o;
        }
    }
    s.read = Some((Pending::new(&o, r.take()), size));
    watch(h);
    o
}

/// `cancelRecv`: a pending read is dropped (its promise stays unresolved).
pub fn sock_cancel_recv(h: &LHandle) {
    if let Some((p, _)) = sock(h).read.take() {
        p.cancel();
    }
}

/// `uv_accept` at once: the new socket, `None` if no connection waits.
fn accept_now(s: &mut Socket) -> Result<Option<LHandle>, i32> {
    if s.fd < 0 {
        return Ok(None);
    }
    loop {
        let fd = unsafe { accept4(s.fd, std::ptr::null_mut(), std::ptr::null_mut(), SOCK_NONBLOCK | SOCK_CLOEXEC) };
        if fd >= 0 {
            return Ok(Some(new_socket(TCP, fd, F_READABLE | F_WRITABLE)));
        }
        let er = errno();
        if er == EINTR || er == ECONNABORTED {
            continue;
        }
        if er == EAGAIN {
            return Ok(None);
        }
        return Err(uv_err(er));
    }
}

/// `accept`: done at once when a connection waits (or the accept fails),
/// otherwise when one arrives.
pub fn tcp_accept(h: &LHandle, r: LPromise) -> LHandle {
    let o = op_new();
    let mut r = Ready(Some(r));
    let s = sock(h);
    if s.accept.is_some() {
        op(&o).sync_err = UV_EALREADY;
        return o;
    }
    match accept_now(s) {
        Ok(Some(c)) => {
            let x = op(&o);
            x.done = true;
            x.handle = Some(c);
        }
        Ok(None) => {
            s.accept = Some(Pending::new(&o, r.take()));
            watch(h);
        }
        Err(e) => {
            let x = op(&o);
            x.done = true;
            x.code = e;
        }
    }
    o
}

/// `tryAccept`: the new socket (`handle`), nothing, or an error (`code`).
pub fn tcp_try_accept(h: &LHandle) -> LHandle {
    let o = op_new();
    let s = sock(h);
    if s.accept.is_some() {
        op(&o).sync_err = UV_EALREADY;
        return o;
    }
    let x = op(&o);
    x.done = true;
    match accept_now(s) {
        Ok(c) => x.handle = c,
        Err(e) => x.code = e,
    }
    o
}

pub fn tcp_cancel_accept(h: &LHandle) {
    if let Some(p) = sock(h).accept.take() {
        p.cancel();
    }
}

/// `uv_shutdown`: after the pending writes.
pub fn tcp_shutdown(h: &LHandle, r: LPromise) -> LHandle {
    let o = op_new();
    let mut r = Ready(Some(r));
    let s = sock(h);
    if s.shutdown.is_some() {
        op(&o).sync_err = UV_EALREADY;
        return o;
    }
    if s.flags & F_WRITABLE == 0 || s.flags & F_SHUT != 0 {
        op(&o).sync_err = UV_ENOTCONN;
        return o;
    }
    s.shutdown = Some(Pending::new(&o, r.take()));
    // `uv_shutdown`: no more writes from now on (a `send` fails with
    // `EPIPE`); the queued ones go first.
    s.flags &= !F_WRITABLE;
    if s.connect.is_none() {
        flush_writes(h);
    }
    if s.has_pending() {
        watch(h);
    }
    o
}

/// `getsockname` (`peer` false) or `getpeername`: the address, or an error
/// (`code`).
pub fn sock_name(h: &LHandle, peer: bool) -> LHandle {
    let o = op_new();
    let s = sock(h);
    let x = op(&o);
    x.done = true;
    if s.kind == TCP && s.delayed_error != 0 {
        x.code = s.delayed_error;
        return o;
    }
    if s.fd < 0 {
        x.code = UV_EBADF;
        return o;
    }
    let mut sa = EMPTY_ADDR;
    let mut len = std::mem::size_of::<SockAddrStorage>() as u32;
    let rc = unsafe {
        if peer {
            getpeername(s.fd, &mut sa, &mut len)
        } else {
            getsockname(s.fd, &mut sa, &mut len)
        }
    };
    if rc != 0 {
        x.code = uv_err(errno());
    } else {
        x.addr = encode_addr(&sa);
    }
    o
}

pub fn tcp_nodelay(h: &LHandle) -> i32 {
    let s = sock(h);
    if s.fd >= 0 {
        let e = set_int(s.fd, IPPROTO_TCP, TCP_NODELAY, 1);
        if e != 0 {
            return e;
        }
    }
    s.flags |= F_NODELAY;
    0
}

pub fn tcp_keepalive(h: &LHandle, enable: i32, delay: u32) -> i32 {
    let s = sock(h);
    if s.fd >= 0 {
        let e = keepalive_fd(s.fd, enable != 0, delay);
        if e != 0 {
            return e;
        }
    }
    if enable != 0 {
        s.flags |= F_KEEPALIVE;
    } else {
        s.flags &= !F_KEEPALIVE;
    }
    s.keepalive_delay = delay;
    0
}

/// `uv__udp_maybe_deferred_bind`: an unbound UDP socket is bound to the
/// unspecified address of `family`, port 0.
fn udp_deferred_bind(s: &mut Socket, family: i32) -> i32 {
    if s.flags & F_BOUND != 0 {
        return 0;
    }
    let a: Vec<u8> = if family == AF_INET6 {
        let mut v = vec![6, 0, 0];
        v.extend_from_slice(&[0; 16]);
        v
    } else {
        vec![4, 0, 0, 0, 0, 0, 0]
    };
    udp_bind_core(s, &a, false)
}

fn udp_bind_core(s: &mut Socket, a: &[u8], reuse: bool) -> i32 {
    let Some((sa, len)) = decode_addr(a) else { return UV_EINVAL };
    let e = ensure_fd(s, sa.family as i32, 0);
    if e != 0 {
        return e;
    }
    if reuse {
        let e = set_int(s.fd, SOL_SOCKET, SO_REUSEADDR, 1);
        if e != 0 {
            return e;
        }
    }
    if unsafe { bind(s.fd, &sa, len) } != 0 {
        let er = errno();
        return if er == EAFNOSUPPORT { UV_EINVAL } else { uv_err(er) };
    }
    s.flags |= F_BOUND;
    0
}

/// `uv_udp_bind` with `UV_UDP_REUSEADDR`.
pub fn udp_bind(h: &LHandle, a: &[u8]) -> i32 {
    udp_bind_core(sock(h), a, true)
}

/// `uv_udp_connect`.
pub fn udp_connect(h: &LHandle, a: &[u8]) -> i32 {
    let s = sock(h);
    let Some((sa, len)) = decode_addr(a) else { return UV_EINVAL };
    if s.flags & F_UDP_CONNECTED != 0 {
        return UV_EISCONN;
    }
    let e = udp_deferred_bind(s, sa.family as i32);
    if e != 0 {
        return e;
    }
    loop {
        let rc = unsafe { connect(s.fd, &sa, len) };
        if rc == -1 && errno() == EINTR {
            continue;
        }
        if rc != 0 {
            return uv_err(errno());
        }
        break;
    }
    s.flags |= F_UDP_CONNECTED;
    0
}

/// `uv_udp_send` to `a` (empty: to the connected peer).
pub fn udp_send(h: &LHandle, data: Vec<u8>, a: &[u8], r: LPromise) -> LHandle {
    let o = op_new();
    let mut r = Ready(Some(r));
    let s = sock(h);
    let dest = if a.is_empty() { None } else { decode_addr(a) };
    if dest.is_some() && s.flags & F_UDP_CONNECTED != 0 {
        op(&o).sync_err = UV_EISCONN;
        return o;
    }
    if dest.is_none() && s.flags & F_UDP_CONNECTED == 0 {
        op(&o).sync_err = UV_EDESTADDRREQ;
        return o;
    }
    if let Some((sa, _)) = &dest {
        let e = udp_deferred_bind(s, sa.family as i32);
        if e != 0 {
            op(&o).sync_err = e;
            return o;
        }
    }
    s.writes.push_back(Write { data, off: 0, dest, pending: Pending::new(&o, r.take()) });
    flush_writes(h);
    if s.has_pending() {
        watch(h);
    }
    o
}

fn is_v6(fd: i32) -> bool {
    let mut sa = EMPTY_ADDR;
    let mut len = std::mem::size_of::<SockAddrStorage>() as u32;
    unsafe { getsockname(fd, &mut sa, &mut len) };
    sa.family as i32 == AF_INET6
}

/// UDP socket options: `setBroadcast` (0), `setMulticastLoop` (1),
/// `setMulticastTTL` (2), `setTTL` (3), with value `v`.
pub fn udp_option(h: &LHandle, which: u8, v: u32) -> i32 {
    let s = sock(h);
    if (which == 2 && v > 255) || (which == 3 && !(1..=255).contains(&v)) {
        return UV_EINVAL;
    }
    if s.fd < 0 {
        return UV_EBADF;
    }
    let fd = s.fd;
    let v6 = is_v6(fd);
    let (l6, l4) = (IPPROTO_IPV6, IPPROTO_IP);
    match which {
        0 => set_int(fd, SOL_SOCKET, SO_BROADCAST, (v != 0) as i32),
        1 => {
            if v6 {
                set_int(fd, l6, IPV6_MULTICAST_LOOP, (v != 0) as i32)
            } else {
                set_int(fd, l4, IP_MULTICAST_LOOP, (v != 0) as i32)
            }
        }
        2 => {
            if v > 255 {
                return UV_EINVAL;
            }
            if v6 {
                set_int(fd, l6, IPV6_MULTICAST_HOPS, v as i32)
            } else {
                set_int(fd, l4, IP_MULTICAST_TTL, v as i32)
            }
        }
        _ => {
            if !(1..=255).contains(&v) {
                return UV_EINVAL;
            }
            if v6 {
                set_int(fd, l6, IPV6_UNICAST_HOPS, v as i32)
            } else {
                set_int(fd, l4, IP_TTL, v as i32)
            }
        }
    }
}

/// `setMembership` (leave 0, join 1): `mcast` and `iface` are IP addresses
/// (the shim's encoding, the family then the bytes; `iface` empty: any).
pub fn udp_membership(h: &LHandle, mcast: &[u8], iface: &[u8], membership: u8) -> i32 {
    let s = sock(h);
    // libuv binds an unbound socket first (with `UV_UDP_REUSEADDR`).
    if s.flags & F_BOUND == 0 {
        let a: Vec<u8> = if mcast.first() == Some(&6) {
            let mut v = vec![6, 0, 0];
            v.extend_from_slice(&[0; 16]);
            v
        } else {
            vec![4, 0, 0, 0, 0, 0, 0]
        };
        let e = udp_bind_core(s, &a, true);
        if e != 0 {
            return e;
        }
    }
    if membership > 1 {
        return UV_EINVAL;
    }
    let join = membership == 1;
    let r = match mcast.first() {
        Some(4) if mcast.len() >= 5 => {
            let mut m = [0u8; 8];
            m[0..4].copy_from_slice(&mcast[1..5]);
            if iface.first() == Some(&4) && iface.len() >= 5 {
                m[4..8].copy_from_slice(&iface[1..5]);
            }
            let name = if join { IP_ADD_MEMBERSHIP } else { IP_DROP_MEMBERSHIP };
            unsafe { setsockopt(s.fd, IPPROTO_IP, name, m.as_ptr() as *const c_void, 8) }
        }
        Some(6) if mcast.len() >= 17 => {
            let mut m = [0u8; 20];
            m[0..16].copy_from_slice(&mcast[1..17]);
            let name = if join { IPV6_ADD_MEMBERSHIP } else { IPV6_DROP_MEMBERSHIP };
            unsafe { setsockopt(s.fd, IPPROTO_IPV6, name, m.as_ptr() as *const c_void, 20) }
        }
        _ => return UV_EINVAL,
    };
    if r != 0 {
        uv_err(errno())
    } else {
        0
    }
}

/// `setMulticastInterface`.
pub fn udp_multicast_interface(h: &LHandle, iface: &[u8]) -> i32 {
    let s = sock(h);
    if s.fd < 0 {
        return UV_EBADF;
    }
    let r = match iface.first() {
        Some(4) if iface.len() >= 5 => unsafe { setsockopt(s.fd, IPPROTO_IP, IP_MULTICAST_IF, iface[1..5].as_ptr() as *const c_void, 4) },
        Some(6) => {
            let idx: i32 = 0;
            unsafe { setsockopt(s.fd, IPPROTO_IPV6, IPV6_MULTICAST_IF, &idx as *const i32 as *const c_void, 4) }
        }
        _ => return UV_EINVAL,
    };
    if r != 0 {
        uv_err(errno())
    } else {
        0
    }
}

/// Socket `h` is ready (`revents`): carry its pending operations on.
fn handle_ready(h: &LHandle, revents: i16) {
    let s = sock(h);
    if s.connect.is_some() && revents & (POLLOUT | POLLERR | POLLHUP) != 0 {
        let mut err: i32 = 0;
        let mut len: u32 = 4;
        unsafe { getsockopt(s.fd, SOL_SOCKET, SO_ERROR, &mut err as *mut i32 as *mut c_void, &mut len) };
        if err != EINPROGRESS {
            let p = s.connect.take().unwrap();
            p.complete(if err != 0 { uv_err(err) } else { 0 });
        }
    }
    if s.accept.is_some() && revents & (POLLIN | POLLERR | POLLHUP) != 0 {
        match accept_now(s) {
            Ok(Some(c)) => {
                let p = s.accept.take().unwrap();
                op(&p.op).handle = Some(c);
                p.complete(0);
            }
            Ok(None) => {}
            Err(e) => s.accept.take().unwrap().complete(e),
        }
    }
    if s.read.is_some() && revents & (POLLIN | POLLERR | POLLHUP) != 0 {
        let size = s.read.as_ref().unwrap().1;
        if size == 0 {
            // `waitReadable`: libuv reads with an empty buffer.
            s.read.take().unwrap().0.complete(UV_ENOBUFS);
        } else {
            let mut buf = vec![0u8; size.min(1 << 30) as usize];
            let mut sa = EMPTY_ADDR;
            let mut len = std::mem::size_of::<SockAddrStorage>() as u32;
            let n = unsafe {
                if s.kind == TCP {
                    read(s.fd, buf.as_mut_ptr() as *mut c_void, buf.len())
                } else {
                    recvfrom(s.fd, buf.as_mut_ptr() as *mut c_void, buf.len(), 0, &mut sa, &mut len)
                }
            };
            let er = errno();
            if n >= 0 || (er != EAGAIN && er != EINTR) {
                let (p, _) = s.read.take().unwrap();
                if n < 0 {
                    p.complete(uv_err(er));
                } else if n == 0 && s.kind == TCP {
                    p.complete(UV_EOF);
                } else {
                    buf.truncate(n as usize);
                    let x = op(&p.op);
                    x.bytes = buf;
                    if s.kind == UDP {
                        x.addr = encode_addr(&sa);
                    }
                    p.complete(n as i32);
                }
            }
        }
    }
    if (!s.writes.is_empty() || s.shutdown.is_some()) && s.connect.is_none() && revents & (POLLOUT | POLLERR | POLLHUP) != 0 {
        flush_writes(h);
    }
}

// ---------------------------------------------------------------------------
// Name resolution (`uv/dns.cpp`): `getaddrinfo`/`getnameinfo` run at once
// (natively on libuv's thread pool) and complete through the event loop.

/// libuv's code for a `getaddrinfo`/`getnameinfo` error
/// (`uv__getaddrinfo_translate_error`).
fn eai_code(e: i32) -> i32 {
    match e {
        -9 => -3000,   // EAI_ADDRFAMILY
        -3 => -3001,   // EAI_AGAIN
        -1 => -3002,   // EAI_BADFLAGS
        -101 => -3003, // EAI_CANCELED
        -4 => -3004,   // EAI_FAIL
        -6 => -3005,   // EAI_FAMILY
        -10 => -3006,  // EAI_MEMORY
        -5 => -3007,   // EAI_NODATA
        -2 => -3008,   // EAI_NONAME
        -12 => -3009,  // EAI_OVERFLOW
        -8 => -3010,   // EAI_SERVICE
        -7 => -3011,   // EAI_SOCKTYPE
        -11 => uv_err(errno()), // EAI_SYSTEM
        _ => UV_UNKNOWN,
    }
}

/// `getAddrInfo host service family`: the addresses (`bytes`, 17 each: the
/// family, then 16 bytes). libuv first converts the host (`uv__idna_toascii`)
/// into a 256-byte buffer: an empty host, or one that does not fit, is
/// `UV_EINVAL` at once (the names Lean lets through are ASCII, copied as
/// they are).
pub fn dns_get_info(host: &[u8], service: &[u8], family: u8, r: LPromise) -> LHandle {
    let o = op_new();
    let mut r = Ready(Some(r));
    if host.is_empty() || host.len() >= 256 {
        op(&o).sync_err = UV_EINVAL;
        return o;
    }
    let hints = AddrInfo {
        ai_flags: 0,
        ai_family: match family {
            1 => AF_INET,
            2 => AF_INET6,
            _ => 0,
        },
        ai_socktype: 0,
        ai_protocol: 0,
        ai_addrlen: 0,
        ai_addr: std::ptr::null_mut(),
        ai_canonname: std::ptr::null_mut(),
        ai_next: std::ptr::null_mut(),
    };
    let mut hz = host.to_vec();
    hz.push(0);
    let mut sz = service.to_vec();
    sz.push(0);
    let mut res: *mut AddrInfo = std::ptr::null_mut();
    let rc = unsafe { getaddrinfo(hz.as_ptr() as *const std::ffi::c_char, sz.as_ptr() as *const std::ffi::c_char, &hints, &mut res) };
    let p = Pending::new(&o, r.take());
    if rc != 0 {
        p.complete(eai_code(rc));
        return o;
    }
    let mut out = Vec::new();
    let mut ai = res;
    while !ai.is_null() {
        let a = unsafe { &*ai };
        if !a.ai_addr.is_null() {
            let sa = unsafe { &*a.ai_addr };
            match sa.family as i32 {
                AF_INET => {
                    out.push(4u8);
                    out.extend_from_slice(&sa.data[2..6]);
                    out.extend_from_slice(&[0u8; 12]);
                }
                AF_INET6 => {
                    out.push(6u8);
                    out.extend_from_slice(&sa.data[6..22]);
                }
                _ => {}
            }
        }
        ai = a.ai_next;
    }
    unsafe { freeaddrinfo(res) };
    op(&o).bytes = out;
    p.complete(0);
    o
}

/// `getNameInfo addr`: the host and service names (`strs`).
pub fn dns_get_name(a: &[u8], r: LPromise) -> LHandle {
    let o = op_new();
    let mut r = Ready(Some(r));
    let p = Pending::new(&o, r.take());
    let Some((sa, len)) = decode_addr(a) else {
        p.complete(UV_EINVAL);
        return o;
    };
    let mut host = [0 as std::ffi::c_char; 1025];
    let mut serv = [0 as std::ffi::c_char; 32];
    let rc = unsafe { getnameinfo(&sa, len, host.as_mut_ptr(), host.len() as u32, serv.as_mut_ptr(), serv.len() as u32, 0) };
    if rc != 0 {
        p.complete(eai_code(rc));
        return o;
    }
    let hs = unsafe { std::ffi::CStr::from_ptr(host.as_ptr()) }.to_bytes().to_vec();
    let ss = unsafe { std::ffi::CStr::from_ptr(serv.as_ptr()) }.to_bytes().to_vec();
    op(&o).strs = vec![hs, ss];
    p.complete(0);
    o
}

// ---------------------------------------------------------------------------
// Errors

/// libuv's `uv_strerror` (its own codes, and negated errnos).
pub fn uv_strerror(code: i32) -> Vec<u8> {
    let m: &str = match code {
        UV_EOF => "end of file",
        UV_UNKNOWN => "unknown error",
        -4080 => "invalid Unicode character",
        -3000 => "address family not supported",
        -3001 => "temporary failure",
        -3002 => "bad ai_flags value",
        -3003 => "request canceled",
        -3004 => "permanent failure",
        -3005 => "ai_family not supported",
        -3006 => "out of memory",
        -3007 => "no address",
        -3008 => "unknown node or service",
        -3009 => "argument buffer overflow",
        -3010 => "service not available for socket type",
        -3011 => "socket type not supported",
        -3013 => "invalid value for hints",
        -3014 => "resolved protocol is unknown",
        _ => return crate::fs::uv_strerror_bytes(-code),
    };
    m.as_bytes().to_vec()
}

/// The `IO.Error` builder `lean_decode_uv_error` uses for libuv code
/// `code` without a file name (the kinds of runtime/README.md's table).
pub fn uv_error_kind(code: i32) -> u32 {
    if code >= 0 || code <= -3000 {
        return 0;
    }
    crate::fs::uv_kind(-code)
}

// ---------------------------------------------------------------------------
// Addresses (`uv/net_addr.cpp`)

extern "C" {
    fn inet_pton(af: i32, src: *const std::ffi::c_char, dst: *mut c_void) -> i32;
    fn inet_ntop(af: i32, src: *const c_void, dst: *mut std::ffi::c_char, size: u32) -> *const std::ffi::c_char;
    fn getifaddrs(ifap: *mut *mut IfAddrs) -> i32;
    fn freeifaddrs(ifa: *mut IfAddrs);
}

/// `uv_inet_pton` (`IPv4Addr.ofString`, `IPv6Addr.ofString`): the address
/// bytes, empty if `s` is not an address of the family (or contains a NUL
/// byte, as Lean checks first). libuv drops an IPv6 zone (`%eth0`).
pub fn pton(s: &[u8], v6: bool) -> Vec<u8> {
    if s.contains(&0) {
        return Vec::new();
    }
    let mut src = s.to_vec();
    if v6 {
        if let Some(p) = src.iter().position(|&c| c == b'%') {
            if p > 45 {
                return Vec::new();
            }
            src.truncate(p);
        }
    }
    src.push(0);
    let mut out = [0u8; 16];
    let af = if v6 { AF_INET6 } else { AF_INET };
    if unsafe { inet_pton(af, src.as_ptr() as *const std::ffi::c_char, out.as_mut_ptr() as *mut c_void) } != 1 {
        return Vec::new();
    }
    out[..if v6 { 16 } else { 4 }].to_vec()
}

/// `uv_inet_ntop` of an IP address (the shim's encoding: the family, then
/// the bytes).
pub fn ntop(a: &[u8]) -> Vec<u8> {
    let (af, n) = if a.first() == Some(&6) { (AF_INET6, 16) } else { (AF_INET, 4) };
    let mut src = [0u8; 16];
    let m = n.min(a.len().saturating_sub(1));
    src[..m].copy_from_slice(&a[1..1 + m]);
    let mut dst = [0 as std::ffi::c_char; 64];
    let p = unsafe { inet_ntop(af, src.as_ptr() as *const c_void, dst.as_mut_ptr(), 64) };
    if p.is_null() {
        return Vec::new();
    }
    unsafe { std::ffi::CStr::from_ptr(dst.as_ptr()) }.to_bytes().to_vec()
}

#[repr(C)]
struct IfAddrs {
    ifa_next: *mut IfAddrs,
    ifa_name: *const std::ffi::c_char,
    ifa_flags: u32,
    ifa_addr: *const SockAddrStorage,
    ifa_netmask: *const SockAddrStorage,
    ifa_ifu: *const c_void,
    ifa_data: *const c_void,
}

const IFF_UP: u32 = 1;
const IFF_LOOPBACK: u32 = 8;
const IFF_RUNNING: u32 = 0x40;
const PF_PACKET: u16 = 17;

/// libuv's `uv__ifaddr_exclude` (`phys`: for the physical addresses).
fn iface_excluded(e: &IfAddrs, phys: bool) -> bool {
    if e.ifa_flags & IFF_UP == 0 || e.ifa_flags & IFF_RUNNING == 0 || e.ifa_addr.is_null() {
        return true;
    }
    let packet = unsafe { (*e.ifa_addr).family } == PF_PACKET;
    if phys {
        !packet
    } else {
        packet
    }
}

fn ip17(sa: *const SockAddrStorage) -> [u8; 17] {
    let mut out = [0u8; 17];
    if sa.is_null() {
        out[0] = 4;
        return out;
    }
    let s = unsafe { &*sa };
    if s.family as i32 == AF_INET6 {
        out[0] = 6;
        out[1..17].copy_from_slice(&s.data[6..22]);
    } else if s.family as i32 == AF_INET {
        out[0] = 4;
        out[1..5].copy_from_slice(&s.data[2..6]);
    }
    out
}

/// `uv_interface_addresses` as `lean_uv_interface_addresses` uses it: per
/// IPv4 or IPv6 address of an interface that is up and running, its name
/// (`strs`) and 41 bytes (`bytes`): the MAC address, whether it is a
/// loopback interface, the address and the mask (17 bytes each). The code
/// is an error if `getifaddrs` fails.
pub fn ifaces() -> LHandle {
    let o = op_new();
    let x = op(&o);
    x.done = true;
    let mut addrs: *mut IfAddrs = std::ptr::null_mut();
    if unsafe { getifaddrs(&mut addrs) } != 0 {
        x.code = uv_err(errno());
        return o;
    }
    let mut ents: Vec<(Vec<u8>, [u8; 6], bool, [u8; 17], [u8; 17])> = Vec::new();
    let mut p = addrs;
    while !p.is_null() {
        let e = unsafe { &*p };
        if !iface_excluded(e, false) {
            let name = unsafe { std::ffi::CStr::from_ptr(e.ifa_name) }.to_bytes().to_vec();
            ents.push((name, [0; 6], e.ifa_flags & IFF_LOOPBACK != 0, ip17(e.ifa_addr), ip17(e.ifa_netmask)));
        }
        p = e.ifa_next;
    }
    let mut p = addrs;
    while !p.is_null() {
        let e = unsafe { &*p };
        if !iface_excluded(e, true) {
            let name = unsafe { std::ffi::CStr::from_ptr(e.ifa_name) }.to_bytes();
            let sll = unsafe { &*e.ifa_addr };
            for ent in ents.iter_mut() {
                let n = name.len();
                // Alias interfaces share the physical address.
                if ent.0.starts_with(name) && (ent.0.len() == n || ent.0[n] == b':') {
                    ent.1.copy_from_slice(&sll.data[10..16]);
                }
            }
        }
        p = e.ifa_next;
    }
    unsafe { freeifaddrs(addrs) };
    for (name, mac, lo, a, m) in ents {
        if a[0] != 4 && a[0] != 6 {
            continue;
        }
        x.strs.push(name);
        x.bytes.extend_from_slice(&mac);
        x.bytes.push(lo as u8);
        x.bytes.extend_from_slice(&a);
        x.bytes.extend_from_slice(&m);
    }
    x.code = x.strs.len() as i32;
    o
}
