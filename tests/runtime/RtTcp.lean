import Std.Async
import Std.Net.Addr
/-! Runtime test: TCP sockets on localhost (`Std.Async.TCP`, over
`Std.Internal.UV.TCP`). A server task and clients in one program, in the
`Async` style and in a blocking style (a task that waits for `accept` or
`recv` lets the others run); end of file after `shutdown`; errors as native
Lean reports them: connection refused, address in use (reported by
`listen`), a second `recv` while one is pending, `send` on a socket that is
not connected, the peer name of an unconnected socket. Ports are chosen by
the system (port 0) and read back with `getSockName`. -/
open Std.Async
open Std.Net

def localhost (port : UInt16) : SocketAddress := SocketAddressV4.mk (.ofParts 127 0 0 1) port

def str (b : Option ByteArray) : String := ((String.fromUTF8? =<< b).getD "<none>")

def echoServer (s : TCP.Socket.Server) (n : Nat) : Async Unit := do
  for _ in [0:n] do
    let c ← s.accept
    let m ← c.recv? 1024
    c.send (String.toUTF8 s!"echo {str m}")
    c.shutdown

def main : IO Unit := do
  let s ← TCP.Socket.Server.mk
  s.bind (localhost 0)
  s.listen 16
  let port := (← s.getSockName).port
  IO.println s!"listening on a port: {decide (port > 0)}"
  -- Async style: a server task and two clients
  let st ← (echoServer s 2).toIO
  for name in ["joe", "mike"] do
    let c ← TCP.Socket.Client.mk
    (← c.connect (localhost port) |>.toBaseIO).block
    IO.println s!"peer port matches: {(← c.getPeerName).port == port}"
    c.noDelay
    (c.send (String.toUTF8 name)).block
    IO.println s!"client got {str (← (c.recv? 1024).block)}"
    IO.println s!"then {str (← (c.recv? 1024).block)}"
  st.block
  -- blocking style: the server is a task that blocks on accept and recv
  let srv ← IO.asTask (prio := .dedicated) do
    let c ← s.accept.block
    let m ← (c.recv? 1024).block
    IO.println s!"server got {str m}"
    (c.send (String.toUTF8 "pong")).block
    let m2 ← (c.recv? 1024).block
    IO.println s!"server got {str m2} after the client's shutdown"
  let c ← TCP.Socket.Client.mk
  (← c.connect (localhost port) |>.toBaseIO).block
  (c.send (String.toUTF8 "ping")).block
  IO.println s!"client got {str (← (c.recv? 1024).block)}"
  c.shutdown.block
  IO.ofExcept (← IO.wait srv)
  -- errors
  let c2 ← TCP.Socket.Client.mk
  try
    (← c2.connect (localhost 1) |>.toBaseIO).block
    IO.println "connected?"
  catch e => IO.println s!"refused: {e}"
  let s2 ← TCP.Socket.Server.mk
  s2.bind (localhost port)
  IO.println "second bind: ok"
  try
    s2.listen 16
    IO.println "second listen: ok?"
  catch e => IO.println s!"second listen: {e}"
  let u ← Std.Internal.UV.TCP.Socket.new
  try
    discard <| u.getPeerName
  catch e => IO.println s!"peer of a new socket: {e}"
  try
    discard <| u.send #[String.toUTF8 "x"]
  catch e => IO.println s!"send on a new socket: {e}"
  try
    discard <| u.recv? 10
  catch e => IO.println s!"recv on a new socket: {e}"
  -- a second recv while one is pending, and cancelRecv
  let acc ← IO.asTask (prio := .dedicated) do
    let c ← s.accept.block
    IO.sleep 50
    (c.send (String.toUTF8 "late")).block
  let c3 ← TCP.Socket.Client.mk
  (← c3.connect (localhost port) |>.toBaseIO).block
  let raw : Std.Internal.UV.TCP.Socket := c3.native
  let p ← raw.recv? 100
  try
    discard <| raw.recv? 100
  catch e => IO.println s!"second recv: {e}"
  match ← IO.wait p.result! with
  | .ok b => IO.println s!"first recv: {str b}"
  | .error e => IO.println s!"first recv failed: {e}"
  IO.ofExcept (← IO.wait acc)
  -- tryAccept with nobody connecting
  match ← s.native.tryAccept with
  | .ok none => IO.println "tryAccept: none"
  | .ok (some _) => IO.println "tryAccept: a socket?"
  | .error e => IO.println s!"tryAccept: {e}"
