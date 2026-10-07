import Std.Internal.UV
open Std.Internal.UV

/-! Runtime test (hunt HSK-03, switch step 16): a deep recursion in a
`sync` dependent of a timer's promise, which natively runs on libuv's loop
thread. That thread is made before `LEAN_STACK_SIZE_KB` is read, so it
always has 1 GiB of stack; here the variable gives 16 MiB. lean-runtime's
event loop context followed the variable and overflowed; since its
fixes-16 it has at least 1 GiB. -/

-- Non-tail recursion that allocates nothing.
def deep : Nat → Nat
  | 0 => 0
  | n + 1 => deep n * 3 % 1000003 + 1

def main (args : List String) : IO Unit := do
  let d := (args[0]?.bind String.toNat?).getD 1000
  let tm ← Timer.mk 20 false
  let p ← tm.next
  let r := p.result!.map (sync := true) fun _ => deep d
  IO.println s!"loop {r.get}"
