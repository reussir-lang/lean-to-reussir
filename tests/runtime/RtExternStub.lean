/-!
A failed binding runs the extern's Lean definition, where natively the call
runs the function its C symbol names (review REB-02). `addM`'s C symbol is
the `@[export]` of `addImpl`, but `addM` takes a `Meters` where `addImpl`
takes a `Nat`: the binding's type test fails, so its stub definition runs
(natively `addImpl`, 7 for 3 and 4; here 12), and lean2rr warns on its own
stderr, naming the binding and the failed test (`RtExternStub.l2r-log`).
`myDecEq`'s symbol is the runtime's `lean_nat_dec_eq`: an extern of the
program is never bound to Lean's runtime, so its stub definition (`false`)
runs as well, without a warning (natively the runtime answers), and the
note marks it "(natively Lean's runtime function)", as it does `dec`, whose
symbol `lean_decode_lossy_utf8` is the runtime's function of a declaration
in a module the program does not import (review REB-13). `myDrop2`'s
symbol `lean_string_drop` is also the `@[export]` of Init's
`String.Internal.dropImpl`: an extern of the program is not bound to Lean's
library's `@[export]`s either (review REB-14), so its stub runs, marked
"(natively Lean's library function)". All these calls are on a path that
does not run, so the outputs agree.
-/

structure Meters where
  val : Nat

@[export rt_stub_add]
def addImpl (a b : Nat) : Nat := a + b

@[extern "rt_stub_add"]
def addM (a b : Meters) : Meters := ⟨a.val * b.val⟩

@[extern "lean_nat_dec_eq"]
def myDecEq (a b : Nat) : Bool := false

@[extern "lean_decode_lossy_utf8"]
def dec (a : @& ByteArray) : String := "stub"

@[extern "lean_string_drop"]
def myDrop2 (s : String) (n : Nat) : String := "stub"

def main (args : List String) : IO Unit := do
  let n := args.length
  if n > 100 then
    IO.println ((addM ⟨n + 3⟩ ⟨4⟩).val, myDecEq (n + 2) 2)
    IO.println (dec "ab".toUTF8, myDrop2 "hello" 2)
  IO.println (addImpl n 1)
