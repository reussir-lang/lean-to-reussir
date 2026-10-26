import Std.Internal.UV
import Std.Net.Addr
/-! Runtime test (leanrt hunt after D8, H3): `for` loops whose body can use a
timer, a UDP socket, `System.FilePath.metadata` or a child process stay
loops. The prelude's timer and socket textures passed the address of their
handle to leanrt functions that are not inlined (`leanrt::net::timer_next(&t,
..)`, `timer_ctl`, `udp_send`, ...); inlined into the loop's function, the
escaping stack slot kept the loop's self tail call a real call (see "An
escaping stack slot blocks tail calls" in the workaround docs): the `timer`
part overflowed a 1 MiB stack, native Lean runs it in 8 MB. The textures now
call by-value wrappers (`net::owned`, also `proc::owned` and `fs::owned`;
the `udp`, `metadata` and `process` parts did not overflow before, as their
textures did not end up in the loop's function, and stay as coverage;
`texture-escape-check.sh` checks the rule on the prelude). Arguments: the
part, the number of steps and how many of the first steps use the
resource; the `.pipe` runs every part for 2*10^5 steps on a 1 MiB stack,
three of them with the resource. -/
open Std.Internal.UV Std.Net

def localhost (port : UInt16) : SocketAddress := SocketAddressV4.mk (.ofParts 127 0 0 1) port

def timer (n real : Nat) : IO Nat := do
  let t ← Timer.mk 1 false
  let mut acc := 0
  for k in [0:n] do
    if k < real then
      let p ← t.next
      let _ ← IO.wait p.result!
      t.reset
      acc := acc + 1
    acc := (acc + k) % 1000003
  return acc

def udp (n real : Nat) : IO Nat := do
  let a ← UDP.Socket.new
  a.bind (localhost 0)
  let b ← UDP.Socket.new
  b.bind (localhost 0)
  let pb := (← b.getSockName).port
  let mut acc := 0
  for k in [0:n] do
    if k < real then
      let p ← a.send #[String.toUTF8 s!"d{k}"] (some (localhost pb))
      let _ ← IO.wait p.result!
      let q ← b.recv 10
      match ← IO.wait q.result! with
      | .ok (m, _) => acc := acc + m.size
      | .error e => IO.println s!"recv: {e}"
    acc := (acc + k) % 1000003
  return acc

def metadata (n real : Nat) : IO Nat := do
  let mut acc := 0
  for k in [0:n] do
    if k < real then
      let md ← System.FilePath.metadata "/"
      if md.type == .dir then acc := acc + 1
    acc := (acc + k) % 1000003
  return acc

def process (n real : Nat) : IO Nat := do
  let mut acc := 0
  for k in [0:n] do
    if k < real then
      let o ← IO.Process.output { cmd := "sh", args := #["-c", "printf ab; exit 2"] }
      acc := acc + o.exitCode.toNat + o.stdout.length
      let child ← IO.Process.spawn { cmd := "true" }
      acc := acc + (← child.wait).toNat
    acc := (acc + k) % 1000003
  return acc

def main (args : List String) : IO Unit := do
  let part := args.headD "timer"
  let n := (args.getD 1 "10").toNat!
  let real := (args.getD 2 "3").toNat!
  let acc ← match part with
    | "timer" => timer n real
    | "udp" => udp n real
    | "metadata" => metadata n real
    | _ => process n real
  IO.println s!"{part}: acc={acc}"
