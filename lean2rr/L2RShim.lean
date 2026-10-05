import Std.Internal.UV
import Std.Net.Addr
import Std.Time.DateTime.Timestamp
import Std.Time.Zoned.Database.Windows

/-!
# lean2rr's shim for `Std.Internal.UV`

Native Lean implements `Std.Internal.UV` (the loop, timers, signals, TCP
and UDP sockets, name resolution, `Std.Net`'s address conversions and the
system queries) in C over libuv (`src/runtime/uv/*.cpp`), building Lean
values (`IO.Promise`, `Except IO.Error ...`, `SocketAddress`) in C. lean2rr's
runtime runs these externs with the shared crate lean-runtime (its event
loop, timers and signals, `sched::uv`; its sockets, name resolution and
interfaces, `net`; its system queries, `io::uvsys`), whose rules (libuv's
state machines and system calls, the checks, the errors, when a promise
resolves) are the only ones; but it cannot build Lean values, so these
externs are implemented here, in Lean, over primitives that take and
return plain values (numbers, strings, byte arrays, runtime handles,
promises: `runtime/leanrt/src/net.rs`, `sys.rs`). This file only turns
those values into Lean's. Each definition is exported under the extern's C
symbol, so lean2rr, which compiles an extern's `@[export]` implementation
instead of calling the runtime (translation plan §5.8), compiles these with
the program. lean2rr loads this module next to the program's when it is
built (`LEAN_PATH`), and treats it as part of the toolchain (no startup
work).

An operation's outcome is an `Op`: its start's error (the extern throws
it), and, for an operation that completes later, its completion's error
or value. An operation that completes later works the same way
everywhere: a promise `r` (of `Unit`) goes to the runtime with the
operation; when the operation completes, the runtime stores its outcome in
its `Op` and drops its reference to `r`, which resolves it and runs the
continuation attached to it here (`whenDone`), a `sync` dependent that
resolves the promise the program sees, as libuv's callback does natively
(see `net.rs`).

The shim also replaces a few Lean definitions whose native behaviour
depends on Lean's reference counting in a way the translation does not
reproduce (the end of this file).
-/

namespace L2RShim

open Std.Internal.UV Std.Net

/-- An operation's outcome (`leanrt::net::OpSt`). -/
opaque OpImpl : NonemptyType.{0}
def Op : Type := OpImpl.type
instance : Nonempty Op := OpImpl.property

/-! ## Primitives (`runtime/prelude.rr`, `l2r_shim_*`) -/

@[extern "lean_shim_op_canceled"] opaque opCanceled (o : @& Op) : BaseIO Bool
@[extern "lean_shim_op_code"] opaque opCode (o : @& Op) : BaseIO UInt32
@[extern "lean_shim_op_sync_err"] opaque opSyncErr (o : @& Op) : BaseIO UInt32
@[extern "lean_shim_op_bytes"] opaque opBytes (o : @& Op) : BaseIO ByteArray
@[extern "lean_shim_op_addr"] opaque opAddr (o : @& Op) : BaseIO ByteArray
@[extern "lean_shim_op_str"] opaque opStr (o : @& Op) (i : UInt32) : BaseIO String
@[extern "lean_shim_op_str_count"] opaque opStrCount (o : @& Op) : BaseIO UInt32
@[extern "lean_shim_op_has_handle"] opaque opHasHandle (o : @& Op) : BaseIO Bool
@[extern "lean_shim_op_handle"] opaque opSocket (o : @& Op) : BaseIO TCP.Socket
/-- An error of the operation, its start's (`which` 0) or its completion's
(1): the `IO.Error` builder (`leanrt::fs::kind_of`; `0xFFFFFFFF`: no
error), its code, file name and details. -/
@[extern "lean_shim_op_err_kind"] opaque opErrKind (o : @& Op) (which : UInt8) : BaseIO UInt32
@[extern "lean_shim_op_err_code"] opaque opErrCode (o : @& Op) (which : UInt8) : BaseIO UInt32
@[extern "lean_shim_op_err_file"] opaque opErrFile (o : @& Op) (which : UInt8) : BaseIO String
@[extern "lean_shim_op_err_details"] opaque opErrDetails (o : @& Op) (which : UInt8) : BaseIO String
/-- `Timer.next`/`Signal.next`: whether the loop took the promise passed;
otherwise the one it already had. -/
@[extern "lean_shim_op_fresh"] opaque opFresh (o : @& Op) : BaseIO Bool
@[extern "lean_shim_op_promise"] opaque opTimerPromise (o : @& Op) : BaseIO (IO.Promise Unit)
@[extern "lean_shim_op_promise"] opaque opSignalPromise (o : @& Op) : BaseIO (IO.Promise Int)

/-- `IO.Error` kind of a libuv code (`leanrt::net::uv_error_kind`: the
system queries report libuv codes). -/
@[extern "lean_shim_uv_kind"] opaque uvKind (code : UInt32) : UInt32
/-- `uv_strerror`. -/
@[extern "lean_shim_uv_strerror"] opaque uvStrerror (code : UInt32) : String

@[extern "lean_shim_loop_configure"] opaque primLoopConfigure (accumulate blockSigProf : Bool) : BaseIO Unit

@[extern "lean_shim_timer_new"] opaque primTimerNew (timeout : UInt64) (repeating : Bool) : BaseIO Timer
@[extern "lean_shim_timer_next"] opaque primTimerNext (t : @& Timer) (p r : IO.Promise Unit) : BaseIO Op
/-- 0 `reset`, 1 `stop`, 2 `cancel`. -/
@[extern "lean_shim_timer_ctl"] opaque primTimerCtl (t : @& Timer) (which : UInt8) : BaseIO Unit
@[extern "lean_shim_signal_new"] opaque primSignalNew (signum : UInt32) (repeating : Bool) : BaseIO Signal
@[extern "lean_shim_signal_next"] opaque primSignalNext (s : @& Signal) (p : IO.Promise Int) (r : IO.Promise Unit) : BaseIO Op
/-- 1 `stop`, 2 `cancel`. -/
@[extern "lean_shim_signal_ctl"] opaque primSignalCtl (s : @& Signal) (which : UInt8) : BaseIO Op

@[extern "lean_shim_tcp_new"] opaque primTcpNew : BaseIO TCP.Socket
@[extern "lean_shim_tcp_bind"] opaque primTcpBind (s : @& TCP.Socket) (addr : @& ByteArray) : BaseIO Op
@[extern "lean_shim_tcp_listen"] opaque primTcpListen (s : @& TCP.Socket) (backlog : UInt32) : BaseIO Op
@[extern "lean_shim_tcp_connect"] opaque primTcpConnect (s : @& TCP.Socket) (addr : @& ByteArray) (r : IO.Promise Unit) : BaseIO Op
@[extern "lean_shim_tcp_send"] opaque primTcpSend (s : @& TCP.Socket) (data : Array ByteArray) (r : IO.Promise Unit) : BaseIO Op
@[extern "lean_shim_tcp_recv"] opaque primTcpRecv (s : @& TCP.Socket) (size : UInt64) (r : IO.Promise Unit) : BaseIO Op
@[extern "lean_shim_tcp_wait_readable"] opaque primTcpWaitReadable (s : @& TCP.Socket) (r : IO.Promise Unit) : BaseIO Op
@[extern "lean_shim_tcp_cancel_recv"] opaque primTcpCancelRecv (s : @& TCP.Socket) : BaseIO Unit
@[extern "lean_shim_tcp_accept"] opaque primTcpAccept (s : @& TCP.Socket) (r : IO.Promise Unit) : BaseIO Op
@[extern "lean_shim_tcp_try_accept"] opaque primTcpTryAccept (s : @& TCP.Socket) : BaseIO Op
@[extern "lean_shim_tcp_cancel_accept"] opaque primTcpCancelAccept (s : @& TCP.Socket) : BaseIO Unit
@[extern "lean_shim_tcp_shutdown"] opaque primTcpShutdown (s : @& TCP.Socket) (r : IO.Promise Unit) : BaseIO Op
@[extern "lean_shim_tcp_name"] opaque primTcpName (s : @& TCP.Socket) (peer : Bool) : BaseIO Op
@[extern "lean_shim_tcp_nodelay"] opaque primTcpNoDelay (s : @& TCP.Socket) : BaseIO Op
@[extern "lean_shim_tcp_keepalive"] opaque primTcpKeepAlive (s : @& TCP.Socket) (enable delay : UInt32) : BaseIO Op

@[extern "lean_shim_udp_new"] opaque primUdpNew : BaseIO UDP.Socket
@[extern "lean_shim_udp_bind"] opaque primUdpBind (s : @& UDP.Socket) (addr : @& ByteArray) : BaseIO Op
@[extern "lean_shim_udp_connect"] opaque primUdpConnect (s : @& UDP.Socket) (addr : @& ByteArray) : BaseIO Op
@[extern "lean_shim_udp_send"] opaque primUdpSend (s : @& UDP.Socket) (data : Array ByteArray) (addr : @& ByteArray) (r : IO.Promise Unit) : BaseIO Op
@[extern "lean_shim_udp_recv"] opaque primUdpRecv (s : @& UDP.Socket) (size : UInt64) (r : IO.Promise Unit) : BaseIO Op
@[extern "lean_shim_udp_wait_readable"] opaque primUdpWaitReadable (s : @& UDP.Socket) (r : IO.Promise Unit) : BaseIO Op
@[extern "lean_shim_udp_cancel_recv"] opaque primUdpCancelRecv (s : @& UDP.Socket) : BaseIO Unit
@[extern "lean_shim_udp_name"] opaque primUdpName (s : @& UDP.Socket) (peer : Bool) : BaseIO Op
/-- 0 `setBroadcast`, 1 `setMulticastLoop`, 2 `setMulticastTTL`, 3 `setTTL`. -/
@[extern "lean_shim_udp_option"] opaque primUdpOption (s : @& UDP.Socket) (which : UInt8) (v : UInt32) : BaseIO Op
@[extern "lean_shim_udp_membership"] opaque primUdpMembership (s : @& UDP.Socket) (mcast iface : @& ByteArray) (membership : UInt8) : BaseIO Op
@[extern "lean_shim_udp_multicast_interface"] opaque primUdpMulticastInterface (s : @& UDP.Socket) (iface : @& ByteArray) : BaseIO Op

@[extern "lean_shim_dns_get_info"] opaque primDnsGetInfo (host service : @& String) (family : UInt8) (r : IO.Promise Unit) : BaseIO Op
@[extern "lean_shim_dns_get_name"] opaque primDnsGetName (addr : @& ByteArray) (r : IO.Promise Unit) : BaseIO Op

/-- `uv_inet_pton` of the family (`v6`): the address bytes, empty if `s`
is not an address. -/
@[extern "lean_shim_pton"] opaque primPton (s : @& String) (v6 : Bool) : ByteArray
/-- `uv_inet_ntop` of an address (the family, 4 or 6, then its bytes). -/
@[extern "lean_shim_ntop"] opaque primNtop (a : @& ByteArray) : String
/-- `uv_interface_addresses`: per interface address, its name (`opStr`)
and 41 bytes (`interfaceAddresses`). -/
@[extern "lean_shim_ifaces"] opaque primIfaces : BaseIO Op

/-! ## Errors -/

/-- The `IO.Error` built by the `lean_mk_io_error_*` builder number `kind`
(the order of lean2rr's `ioErrorBuilderSyms`, `leanrt::fs::kind_of`) from
the error's code, file name and details, as Lean's `decode_io_error` and
`lean_decode_uv_error` build it. -/
def ioErrorOf (kind code : UInt32) (file details : String) : IO.Error :=
  match kind with
  | 1 => .mkInterrupted file code details
  | 2 => .mkInvalidArgument code details
  | 3 => .mkInvalidArgumentFile file code details
  | 4 => .mkNoFileOrDirectory file code details
  | 5 => .mkPermissionDenied code details
  | 6 => .mkPermissionDeniedFile file code details
  | 7 => .mkResourceExhausted code details
  | 8 => .mkResourceExhaustedFile file code details
  | 9 => .mkInappropriateType code details
  | 10 => .mkInappropriateTypeFile file code details
  | 11 => .mkNoSuchThing code details
  | 12 => .mkNoSuchThingFile file code details
  | 13 => .mkAlreadyExists code details
  | 14 => .mkAlreadyExistsFile file code details
  | 15 => .mkHardwareFault code details
  | 16 => .mkUnsatisfiedConstraints code details
  | 17 => .mkIllegalOperation code details
  | 18 => .mkResourceVanished code details
  | 19 => .mkProtocolError code details
  | 20 => .mkTimeExpired code details
  | 21 => .mkResourceBusy code details
  | 22 => .mkUnsupportedOperation code details
  | 23 => .userError details
  | _ => .mkOtherError code details

/-- The error of operation `o`'s start (`which` 0) or completion (1). -/
def opError (o : Op) (which : UInt8) : BaseIO (Option IO.Error) := do
  let k ← opErrKind o which
  if k == 0xFFFFFFFF then return none
  return some (ioErrorOf k (← opErrCode o which) (← opErrFile o which) (← opErrDetails o which))

/-- An operation's start failed: throw its error. -/
def checkStart (o : Op) : IO Unit := do
  if let some e ← opError o 0 then throw e

/-- The outcome of a completed operation: its error, or `ok`'s value. -/
def opResult (o : Op) (ok : BaseIO α) : BaseIO (Except IO.Error α) := do
  match ← opError o 1 with
  | some e => return .error e
  | none => return .ok (← ok)

/-- The error number `lean_decode_uv_error` stores for libuv code `code`:
since Lean 4.34, `-code`, the positive errno (`2` for `UV_ENOENT`). -/
def uvErrno (code : UInt32) : UInt32 := 0 - code

/-- `lean_decode_uv_error(code, nullptr)` of the system queries, which
report libuv codes: the builder and the message are lean-runtime's
(`uvKind`, `uvStrerror`), with the errno `uvErrno code`. -/
def uvError (code : UInt32) : IO.Error :=
  ioErrorOf (uvKind code) (uvErrno code) "" (uvStrerror code)

/-- Throw libuv error `code` unless it is 0 (the system queries). -/
def check (code : UInt32) : IO Unit :=
  if code == 0 then pure () else throw (uvError code)

/-- Run `k` when operation `o` completes (`r` is its promise), unless it
is canceled: a `sync` dependent of `r`, which the runtime resolves (see the
module comment). -/
def whenDone (r : IO.Promise Unit) (o : Op) (k : BaseIO Unit) : BaseIO Unit := do
  discard <| BaseIO.mapTask (t := r.result?) (sync := true) fun _ => do
    unless ← opCanceled o do k

/-! ## Addresses: the runtime's encoding (the family, 4 or 6, then a
socket address's port, big-endian, then the address bytes) -/

def ipBytes : IPAddr → ByteArray
  | .v4 a => ⟨#[4] ++ a.octets.toArray⟩
  | .v6 a => ⟨a.segments.toArray.foldl (fun (acc : Array UInt8) (s : UInt16) => (acc.push (s >>> 8).toUInt8).push s.toUInt8) #[6]⟩

def socketAddrBytes (sa : SocketAddress) : ByteArray :=
  let p := sa.port
  let ip := ipBytes sa.ipAddr
  ⟨#[ip.get! 0, (p >>> 8).toUInt8, p.toUInt8] ++ (ip.extract 1 ip.size).data⟩

def v4Of (b : ByteArray) (i : Nat) : IPv4Addr :=
  .ofParts (b.get! i) (b.get! (i + 1)) (b.get! (i + 2)) (b.get! (i + 3))

def v6Of (b : ByteArray) (i : Nat) : IPv6Addr :=
  let seg (k : Nat) : UInt16 := ((b.get! (i + 2 * k)).toUInt16 <<< 8) ||| (b.get! (i + 2 * k + 1)).toUInt16
  .ofParts (seg 0) (seg 1) (seg 2) (seg 3) (seg 4) (seg 5) (seg 6) (seg 7)

def ipOf (b : ByteArray) (i : Nat) : IPAddr :=
  if b.get! i == 4 then .v4 (v4Of b (i + 1)) else .v6 (v6Of b (i + 1))

def socketAddrOf (b : ByteArray) : SocketAddress :=
  let port : UInt16 := ((b.get! 1).toUInt16 <<< 8) ||| (b.get! 2).toUInt16
  if b.get! 0 == 4 then .v4 { addr := v4Of b 3, port } else .v6 { addr := v6Of b 3, port }

/-- An operation's address (`getsockname`, `getpeername`). -/
def addrResult (o : Op) : IO SocketAddress := do
  checkStart o
  return socketAddrOf (← opAddr o)

/-- A new promise `p` resolved by `k` when operation `o` completes (`r`
its promise), after `o`'s start succeeded. -/
def completion [Nonempty α] (r : IO.Promise Unit) (o : Op) (k : IO.Promise α → BaseIO Unit) : IO (IO.Promise α) := do
  checkStart o
  let p ← IO.Promise.new
  whenDone r o (k p)
  return p

/-! ## Timers (`uv/timer.cpp`, lean-runtime's `sched::uv::Timer`) -/

@[export lean_uv_timer_mk]
def timerMk (timeout : UInt64) (repeating : Bool) : IO Timer :=
  primTimerNew timeout repeating

@[export lean_uv_timer_next]
def timerNext (t : Timer) : IO (IO.Promise Unit) := do
  let p ← IO.Promise.new
  let r ← IO.Promise.new
  let o ← primTimerNext t p r
  if ← opFresh o then
    whenDone r o (p.resolve ())
    return p
  opTimerPromise o

@[export lean_uv_timer_reset]
def timerReset (t : Timer) : IO Unit := primTimerCtl t 0

@[export lean_uv_timer_stop]
def timerStop (t : Timer) : IO Unit := primTimerCtl t 1

@[export lean_uv_timer_cancel]
def timerCancel (t : Timer) : IO Unit := primTimerCtl t 2

/-! ## Signals (`uv/signal.cpp`, lean-runtime's `sched::uv::Signal`) -/

@[export lean_uv_signal_mk]
def signalMk (signum : Int32) (repeating : Bool) : IO Signal :=
  primSignalNew signum.toUInt32 repeating

@[export lean_uv_signal_next]
def signalNext (s : Signal) : IO (IO.Promise Int) := do
  let p ← IO.Promise.new
  let r ← IO.Promise.new
  let o ← primSignalNext s p r
  checkStart o
  if ← opFresh o then
    whenDone r o do p.resolve (Int.ofNat (← opCode o).toNat)
    return p
  opSignalPromise o

@[export lean_uv_signal_stop]
def signalStop (s : Signal) : IO Unit := do checkStart (← primSignalCtl s 1)

@[export lean_uv_signal_cancel]
def signalCancel (s : Signal) : IO Unit := do checkStart (← primSignalCtl s 2)

/-! ## The loop (`uv/event_loop.cpp`) -/

@[export lean_uv_event_loop_configure]
def loopConfigure (o : Loop.Options) : BaseIO Unit :=
  primLoopConfigure o.accumulateIdleTime o.blockSigProfSignal

/-! ## TCP (`uv/tcp.cpp`, lean-runtime's `net::tcp`) -/

@[export lean_uv_tcp_new]
def tcpNew : IO TCP.Socket := primTcpNew

@[export lean_uv_tcp_connect]
def tcpConnect (s : TCP.Socket) (addr : SocketAddress) : IO (IO.Promise (Except IO.Error Unit)) := do
  let r ← IO.Promise.new
  let o ← primTcpConnect s (socketAddrBytes addr) r
  completion r o fun p => do p.resolve (← opResult o (pure ()))

@[export lean_uv_tcp_send]
def tcpSend (s : TCP.Socket) (data : Array ByteArray) : IO (IO.Promise (Except IO.Error Unit)) := do
  let r ← IO.Promise.new
  let o ← primTcpSend s data r
  completion r o fun p => do p.resolve (← opResult o (pure ()))

@[export lean_uv_tcp_recv]
def tcpRecv (s : TCP.Socket) (size : UInt64) : IO (IO.Promise (Except IO.Error (Option ByteArray))) := do
  let r ← IO.Promise.new
  let o ← primTcpRecv s size r
  completion r o fun p => do
    p.resolve (← opResult o do if (← opCode o) == 1 then pure none else pure (some (← opBytes o)))

@[export lean_uv_tcp_wait_readable]
def tcpWaitReadable (s : TCP.Socket) : IO (IO.Promise (Except IO.Error Bool)) := do
  let r ← IO.Promise.new
  let o ← primTcpWaitReadable s r
  completion r o fun p => do p.resolve (← opResult o do pure ((← opCode o) == 1))

@[export lean_uv_tcp_cancel_recv]
def tcpCancelRecv (s : TCP.Socket) : IO Unit := primTcpCancelRecv s

@[export lean_uv_tcp_bind]
def tcpBind (s : TCP.Socket) (addr : SocketAddress) : IO Unit := do
  checkStart (← primTcpBind s (socketAddrBytes addr))

@[export lean_uv_tcp_listen]
def tcpListen (s : TCP.Socket) (backlog : UInt32) : IO Unit := do
  checkStart (← primTcpListen s backlog)

@[export lean_uv_tcp_accept]
def tcpAccept (s : TCP.Socket) : IO (IO.Promise (Except IO.Error TCP.Socket)) := do
  let r ← IO.Promise.new
  let o ← primTcpAccept s r
  completion r o fun p => do p.resolve (← opResult o (opSocket o))

@[export lean_uv_tcp_try_accept]
def tcpTryAccept (s : TCP.Socket) : IO (Except IO.Error (Option TCP.Socket)) := do
  let o ← primTcpTryAccept s
  checkStart o
  -- No connection waiting: the operation has no socket.
  if !(← opHasHandle o) then return .ok none
  return .ok (some (← opSocket o))

@[export lean_uv_tcp_cancel_accept]
def tcpCancelAccept (s : TCP.Socket) : IO Unit := primTcpCancelAccept s

@[export lean_uv_tcp_shutdown]
def tcpShutdown (s : TCP.Socket) : IO (IO.Promise (Except IO.Error Unit)) := do
  let r ← IO.Promise.new
  let o ← primTcpShutdown s r
  completion r o fun p => do p.resolve (← opResult o (pure ()))

@[export lean_uv_tcp_getpeername]
def tcpGetPeerName (s : TCP.Socket) : IO SocketAddress := do
  addrResult (← primTcpName s true)

@[export lean_uv_tcp_getsockname]
def tcpGetSockName (s : TCP.Socket) : IO SocketAddress := do
  addrResult (← primTcpName s false)

@[export lean_uv_tcp_nodelay]
def tcpNoDelay (s : TCP.Socket) : IO Unit := do
  checkStart (← primTcpNoDelay s)

@[export lean_uv_tcp_keepalive]
def tcpKeepAlive (s : TCP.Socket) (enable : Int8) (delay : UInt32) : IO Unit := do
  checkStart (← primTcpKeepAlive s enable.toInt32.toUInt32 delay)

/-! ## UDP (`uv/udp.cpp`, lean-runtime's `net::udp`) -/

@[export lean_uv_udp_new]
def udpNew : IO UDP.Socket := primUdpNew

@[export lean_uv_udp_bind]
def udpBind (s : UDP.Socket) (addr : SocketAddress) : IO Unit := do
  checkStart (← primUdpBind s (socketAddrBytes addr))

@[export lean_uv_udp_connect]
def udpConnect (s : UDP.Socket) (addr : SocketAddress) : IO Unit := do
  checkStart (← primUdpConnect s (socketAddrBytes addr))

@[export lean_uv_udp_send]
def udpSend (s : UDP.Socket) (data : Array ByteArray) (addr : Option SocketAddress) :
    IO (IO.Promise (Except IO.Error Unit)) := do
  let r ← IO.Promise.new
  let a := match addr with
    | some sa => socketAddrBytes sa
    | none => .empty
  let o ← primUdpSend s data a r
  completion r o fun p => do p.resolve (← opResult o (pure ()))

@[export lean_uv_udp_recv]
def udpRecv (s : UDP.Socket) (size : UInt64) :
    IO (IO.Promise (Except IO.Error (ByteArray × Option SocketAddress))) := do
  let r ← IO.Promise.new
  let o ← primUdpRecv s size r
  completion r o fun p => do
    p.resolve (← opResult o do
      let a ← opAddr o
      pure (← opBytes o, if a.size == 0 then none else some (socketAddrOf a)))

@[export lean_uv_udp_wait_readable]
def udpWaitReadable (s : UDP.Socket) : IO (IO.Promise (Except IO.Error Unit)) := do
  let r ← IO.Promise.new
  let o ← primUdpWaitReadable s r
  completion r o fun p => do p.resolve (← opResult o (pure ()))

@[export lean_uv_udp_cancel_recv]
def udpCancelRecv (s : UDP.Socket) : IO Unit := primUdpCancelRecv s

@[export lean_uv_udp_getpeername]
def udpGetPeerName (s : UDP.Socket) : IO SocketAddress := do
  addrResult (← primUdpName s true)

@[export lean_uv_udp_getsockname]
def udpGetSockName (s : UDP.Socket) : IO SocketAddress := do
  addrResult (← primUdpName s false)

@[export lean_uv_udp_set_broadcast]
def udpSetBroadcast (s : UDP.Socket) (on : Bool) : IO Unit := do
  checkStart (← primUdpOption s 0 (if on then 1 else 0))

@[export lean_uv_udp_set_multicast_loop]
def udpSetMulticastLoop (s : UDP.Socket) (on : Bool) : IO Unit := do
  checkStart (← primUdpOption s 1 (if on then 1 else 0))

@[export lean_uv_udp_set_multicast_ttl]
def udpSetMulticastTTL (s : UDP.Socket) (ttl : UInt32) : IO Unit := do
  checkStart (← primUdpOption s 2 ttl)

@[export lean_uv_udp_set_membership]
def udpSetMembership (s : UDP.Socket) (mcast : IPAddr) (iface : Option IPAddr) (membership : UInt8) : IO Unit := do
  let i := match iface with
    | some a => ipBytes a
    | none => .empty
  checkStart (← primUdpMembership s (ipBytes mcast) i membership)

@[export lean_uv_udp_set_multicast_interface]
def udpSetMulticastInterface (s : UDP.Socket) (iface : IPAddr) : IO Unit := do
  checkStart (← primUdpMulticastInterface s (ipBytes iface))

@[export lean_uv_udp_set_ttl]
def udpSetTTL (s : UDP.Socket) (ttl : UInt32) : IO Unit := do
  checkStart (← primUdpOption s 3 ttl)

/-! ## Name resolution (`uv/dns.cpp`, lean-runtime's `net::dns`) -/

@[export lean_uv_dns_get_info]
def dnsGetInfo (host service : String) (family : UInt8) : IO (IO.Promise (Except IO.Error (Array IPAddr))) := do
  let r ← IO.Promise.new
  let o ← primDnsGetInfo host service family r
  completion r o fun p => do
    p.resolve (← opResult o do
      let b ← opBytes o
      pure ((List.range (b.size / 17)).toArray.map fun k => ipOf b (17 * k)))

@[export lean_uv_dns_get_name]
def dnsGetName (addr : SocketAddress) : IO (IO.Promise (Except IO.Error (String × String))) := do
  let r ← IO.Promise.new
  let o ← primDnsGetName (socketAddrBytes addr) r
  completion r o fun p => do p.resolve (← opResult o do pure (← opStr o 0, ← opStr o 1))

/-! ## Addresses (`uv/net_addr.cpp`, lean-runtime's `semantics::net`, `net::iface`) -/

@[export lean_uv_pton_v4]
def ptonV4 (s : String) : Option IPv4Addr :=
  let b := primPton s false
  if b.size == 4 then some (v4Of b 0) else none

@[export lean_uv_ntop_v4]
def ntopV4 (a : IPv4Addr) : String := primNtop (ipBytes (.v4 a))

@[export lean_uv_pton_v6]
def ptonV6 (s : String) : Option IPv6Addr :=
  let b := primPton s true
  if b.size == 16 then some (v6Of b 0) else none

@[export lean_uv_ntop_v6]
def ntopV6 (a : IPv6Addr) : String := primNtop (ipBytes (.v6 a))

/-- A MAC address from 6 bytes. -/
def macOf (b : ByteArray) (i : Nat) : MACAddr :=
  ⟨#v[b.get! i, b.get! (i + 1), b.get! (i + 2), b.get! (i + 3), b.get! (i + 4), b.get! (i + 5)]⟩

/-- `Std.Net.interfaceAddresses`. The runtime's operation has, per
interface address, its name (`opStr`) and 41 bytes: the MAC address (6),
whether it is internal (1), the address and the mask (17 each: the family,
then 16 bytes). -/
@[export lean_uv_interface_addresses]
def interfaceAddresses : IO (Array InterfaceAddress) := do
  let o ← primIfaces
  checkStart o
  let b ← opBytes o
  let n := b.size / 41
  let mut out := #[]
  for k in [0:n] do
    let i := 41 * k
    out := out.push {
      name := ← opStr o k.toUInt32
      physicalAddress := macOf b i
      isLoopback := b.get! (i + 6) != 0
      address := ipOf b (i + 7)
      netMask := ipOf b (i + 24) }
  return out

/-! ## The system (`uv/system.cpp`) -/

namespace Sys
open Std.Internal.UV.System

@[extern "lean_shim_sys_title_set"] opaque primTitleSet (s : @& String) : BaseIO UInt32
/-- 0 `uptime`, 1 `cpuInfo`, 2 `cwd`, 3 `osHomedir`, 4 `osTmpdir`,
5 `osGetPasswd`, 6 `osEnviron`, 7 `osGetHostname`, 8 `osUname`,
9 `getrusage`, 10 `exePath`, 11 `getProcessTitle`: an operation with the
result. -/
@[extern "lean_shim_sys_query"] opaque primQuery (which : UInt8) : BaseIO Op
@[extern "lean_shim_sys_group"] opaque primGroup (gid : UInt64) : BaseIO Op
@[extern "lean_shim_sys_getenv"] opaque primGetenv (name : @& String) : BaseIO Op
@[extern "lean_shim_sys_priority"] opaque primGetPriority (pid : UInt64) : BaseIO Op
/-- 0 `osGetPid`, 1 `osGetPpid`, 2 `hrtime`, 3 `freeMemory`,
4 `totalMemory`, 5 `constrainedMemory`, 6 `availableMemory`. -/
@[extern "lean_shim_sys_word"] opaque primWord (which : UInt8) : BaseIO UInt64
@[extern "lean_shim_sys_chdir"] opaque primChdir (p : @& String) : BaseIO UInt32
@[extern "lean_shim_sys_setenv"] opaque primSetenv (n v : @& String) (set : Bool) : BaseIO UInt32
@[extern "lean_shim_sys_setpriority"] opaque primSetPriority (pid prio : UInt64) : BaseIO UInt32
@[extern "lean_shim_sys_random"] opaque primRandom (size : UInt64) (r : IO.Promise Unit) : BaseIO Op

/-- The little-endian word at byte `i`. -/
def word (b : ByteArray) (i : Nat) : UInt64 :=
  (List.range 8).foldl (fun acc k => acc ||| ((b.get! (i + k)).toUInt64 <<< (8 * k).toUInt64)) 0

/-- `mk_embedded_nul_error`. -/
def nulError (s : String) : IO.Error :=
  .mkInvalidArgumentFile s 22 "string contains NUL bytes"

def hasNul (s : String) : Bool := s.toUTF8.data.contains 0

/-- An operation's result: its error, or its first string. -/
def str0 (o : Op) : IO String := do
  check (← opCode o)
  opStr o 0

@[export lean_uv_get_process_title]
def getProcessTitle : IO String := do str0 (← primQuery 11)

@[export lean_uv_set_process_title]
def setProcessTitle (t : String) : IO Unit := do
  if hasNul t then throw (nulError t)
  check (← primTitleSet t)

@[export lean_uv_uptime]
def uptime : IO UInt64 := do
  let o ← primQuery 0
  check (← opCode o)
  return word (← opBytes o) 0

@[export lean_uv_os_getpid]
def osGetPid : IO UInt64 := primWord 0

@[export lean_uv_os_getppid]
def osGetPpid : IO UInt64 := primWord 1

@[export lean_uv_cpu_info]
def cpuInfo : IO (Array CPUInfo) := do
  let o ← primQuery 1
  check (← opCode o)
  let b ← opBytes o
  let n := b.size / 48
  let mut out := #[]
  for k in [0:n] do
    let i := 48 * k
    out := out.push {
      model := ← opStr o k.toUInt32
      speed := word b i
      times := { user := word b (i + 8), nice := word b (i + 16), sys := word b (i + 24),
                 idle := word b (i + 32), irq := word b (i + 40) } }
  return out

@[export lean_uv_cwd]
def cwd : IO String := do str0 (← primQuery 2)

@[export lean_uv_chdir]
def chdir (p : String) : IO Unit := do
  if hasNul p then throw (nulError p)
  let c ← primChdir p
  if c != 0 then
    -- `lean_decode_uv_error(result, path)`: the file name variants.
    let d := uvStrerror c
    let e := uvErrno c
    throw <| match uvKind c with
      | 1 => .mkInterrupted p e d
      | 2 => .mkInvalidArgumentFile p e d
      | 4 => .mkNoFileOrDirectory p e d
      | 5 => .mkPermissionDeniedFile p e d
      | 7 => .mkResourceExhaustedFile p e d
      | 9 => .mkInappropriateTypeFile p e d
      | 11 => .mkNoSuchThingFile p e d
      | 13 => .mkAlreadyExistsFile p e d
      | _ => uvError c

@[export lean_uv_os_homedir]
def osHomedir : IO String := do str0 (← primQuery 3)

@[export lean_uv_os_tmpdir]
def osTmpdir : IO String := do str0 (← primQuery 4)

@[export lean_uv_os_get_passwd]
def osGetPasswd : IO PasswdInfo := do
  let o ← primQuery 5
  check (← opCode o)
  let b ← opBytes o
  let shell ← opStr o 1
  let home ← opStr o 2
  return { username := ← opStr o 0, uid := some (word b 0), gid := some (word b 8),
           shell := some shell, homedir := some home }

@[export lean_uv_os_get_group]
def osGetGroup (gid : UInt64) : IO (Option GroupInfo) := do
  let o ← primGroup gid
  let c ← opCode o
  if c == (0 : UInt32) - 2 then return none
  if c != 0 then
    -- `lean_decode_uv_error(result, "group")`.
    let d := uvStrerror c
    let e := uvErrno c
    throw <| match uvKind c with
      | 2 => .mkInvalidArgumentFile "group" e d
      | 5 => .mkPermissionDeniedFile "group" e d
      | 7 => .mkResourceExhaustedFile "group" e d
      | 11 => .mkNoSuchThingFile "group" e d
      | _ => uvError c
  let n := (← opBytes o)
  let mut members := #[]
  for k in [1:(← opStrCount o).toNat] do
    members := members.push (← opStr o k.toUInt32)
  return some { groupname := ← opStr o 0, gid := word n 0, members }

@[export lean_uv_os_environ]
def osEnviron : IO (Array (String × String)) := do
  let o ← primQuery 6
  let mut out := #[]
  for k in [0:(← opStrCount o).toNat / 2] do
    out := out.push (← opStr o (2 * k).toUInt32, ← opStr o (2 * k + 1).toUInt32)
  return out

@[export lean_uv_os_getenv]
def osGetenv (name : String) : IO (Option String) := do
  if hasNul name then return none
  let o ← primGetenv name
  if (← opCode o) != 0 then return none
  return some (← opStr o 0)

@[export lean_uv_os_setenv]
def osSetenv (name value : String) : IO Unit := do
  if hasNul name then throw (nulError name)
  if hasNul value then throw (nulError value)
  check (← primSetenv name value true)

@[export lean_uv_os_unsetenv]
def osUnsetenv (name : String) : IO Unit := do
  if hasNul name then throw (nulError name)
  check (← primSetenv name "" false)

@[export lean_uv_os_gethostname]
def osGetHostname : IO String := do str0 (← primQuery 7)

@[export lean_uv_os_getpriority]
def osGetPriority (pid : UInt64) : IO Int64 := do
  let o ← primGetPriority pid
  check (← opCode o)
  return (word (← opBytes o) 0).toInt64

@[export lean_uv_os_setpriority]
def osSetPriority (pid : UInt64) (prio : Int64) : IO Unit := do
  check (← primSetPriority pid prio.toUInt64)

@[export lean_uv_os_uname]
def osUname : IO UnameInfo := do
  let o ← primQuery 8
  check (← opCode o)
  return { sysname := ← opStr o 0, release := ← opStr o 1, version := ← opStr o 2, machine := ← opStr o 3 }

@[export lean_uv_hrtime]
def hrtime : IO UInt64 := primWord 2

@[export lean_uv_random]
def random (size : UInt64) : IO (IO.Promise (Except IO.Error ByteArray)) := do
  let r ← IO.Promise.new
  let o ← primRandom size r
  check (← opSyncErr o)
  let p ← IO.Promise.new
  whenDone r o do
    let c ← opCode o
    if c != 0 then p.resolve (.error (uvError c)) else p.resolve (.ok (← opBytes o))
  return p

@[export lean_uv_getrusage]
def getrusage : IO RUsage := do
  let o ← primQuery 9
  check (← opCode o)
  let b ← opBytes o
  let w (k : Nat) := word b (8 * k)
  return { userTime := w 0, systemTime := w 1, maxRSS := w 2, ixRSS := w 3, idRSS := w 4,
           isRSS := w 5, minFlt := w 6, majFlt := w 7, nSwap := w 8, inBlock := w 9,
           outBlock := w 10, msgSent := w 11, msgRecv := w 12, signals := w 13,
           voluntaryCS := w 14, involuntaryCS := w 15 }

@[export lean_uv_exepath]
def exePath : IO String := do str0 (← primQuery 10)

@[export lean_uv_get_free_memory]
def freeMemory : IO UInt64 := primWord 3

@[export lean_uv_get_total_memory]
def totalMemory : IO UInt64 := primWord 4

@[export lean_uv_get_constrained_memory]
def constrainedMemory : IO UInt64 := primWord 5

@[export lean_uv_get_available_memory]
def availableMemory : IO UInt64 := primWord 6

end Sys

/-! ## Time (`src/runtime/io.cpp`) -/

/-- The system clock in nanoseconds since the Unix epoch
(`leanrt::io::realtime_nanos`). -/
@[extern "lean_shim_realtime_nanos"] opaque realtimeNanos : BaseIO Int

/-- `Std.Time.Timestamp.now`: natively the system clock's nanoseconds since
the epoch, split into seconds and nanoseconds by truncating division, as
`Duration.ofNanoseconds` splits them. -/
@[export lean_get_current_time]
def currentTime : IO Std.Time.Timestamp := do
  return Std.Time.Timestamp.ofNanosecondsSinceUnixEpoch ⟨← realtimeNanos⟩

/-- `Std.Time.Database.Windows.getNextTransition`: Windows only; elsewhere
the C function fails with this error. -/
@[export lean_windows_get_next_transition]
def windowsNextTransition (_ : String) (_ : Int64) (_ : Bool) :
    IO (Option (Int64 × Std.Time.TimeZone)) :=
  throw (IO.Error.mkInvalidArgument 22 "failed to get timezone, its windows only.")

/-- `Std.Time.Database.Windows.getLocalTimeZoneIdentifierAt`: Windows only;
elsewhere the C function fails with this error. -/
@[export lean_get_windows_local_timezone_id_at]
def windowsLocalTimeZoneId (_ : Int64) : IO String :=
  throw (IO.Error.mkInvalidArgument 22 "timezone retrieval is Windows-only")

/-! ## Sharing (`src/runtime/sharecommon.cpp`)

Natively `ShareCommon.Object.eq` compares two objects' headers and bodies
byte by byte (the same constructor and the same fields: scalars equal,
pointers to the same objects) and `hash` hashes them, for the tables of
`ShareCommon.State`. lean2rr's runtime implements `shareCommon` itself as
the identity (it shares nothing; translation plan §5.8), and lean2rr's
objects have no Lean layout to compare, so here objects are compared and
hashed by `ptrAddrUnsafe`, which does not emulate identity (plan §9): at
most the same cell is equal, `false` (natively possibly `true`) for two
distinct objects with the same fields. -/

@[export lean_sharecommon_eq]
unsafe def shareCommonEq (a b : ShareCommon.Object) : Bool :=
  ptrAddrUnsafe a == ptrAddrUnsafe b

@[export lean_sharecommon_hash]
unsafe def shareCommonHash (a : ShareCommon.Object) : UInt64 :=
  hash (ptrAddrUnsafe a).toUInt64

/-! ## Definitions the shim replaces

A definition exported as `l2r_override_<its mangled name>` replaces the
Lean definition wherever the program calls it (`Mono.redirectTarget`). -/

/-- `IO.hasFinished promise.result?`, the promise released after the
question (`leanrt::task::promise_is_resolved`). -/
@[extern "lean_shim_promise_is_resolved"]
opaque primPromiseIsResolved {α : Type} (promise : @& IO.Promise α) : BaseIO Bool

/-- `IO.Promise.isResolved`. Natively its parameter is borrowed (Lean's
borrow inference: `result?` borrows it), so the caller releases the promise
after the question; were this the last reference, which resolves the
promise with `none`, the answer is still the state before. Compiled as
written, the promise would be released inside `result?`, before the
question. -/
@[export l2r_override_IO_Promise_isResolved]
def promiseIsResolved {α : Type} (promise : IO.Promise α) : BaseIO Bool :=
  primPromiseIsResolved promise

end L2RShim
