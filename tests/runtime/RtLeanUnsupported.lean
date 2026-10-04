import Lean
open Lean

/-!
`import Lean` code that mentions the `Lean` package's C++ functions
(Lean's kernel, `evalConst`, `.olean` files, shared libraries, and the
`Expr` internals `mkNatLit` reaches) without calling them: natively they
are linked, and the program prints `start` and `end`. lean2rr does not
implement them yet (runtime/README.md, request 32): it rejects the program
and names each of them. Expected to fail until lean2rr's runtime has them
(they are Lean's library: never replaced by their Lean bodies); the calls
are behind a condition that is false.
-/

unsafe def unused (n : Nat) : IO Unit := do
  let env ← mkEmptyEnvironment
  match Kernel.whnf env {} (mkNatLit n) with
  | .ok e => IO.println s!"whnf {e}"
  | .error _ => IO.println "kernel error"
  IO.println s!"isDefEq {Kernel.isDefEqGuarded env {} (mkNatLit n) (mkNatLit 1)}"
  match env.evalConst Nat {} `foo with
  | .ok v => IO.println s!"eval {v}"
  | .error e => IO.println s!"eval error {e}"
  let (d, r) ← CompactedRegion.read (α := Nat) "foo.olean" #[]
  IO.println s!"{d}"
  r.free
  let lib ← Dynlib.load "libfoo.so"
  IO.println s!"{(lib.get? "bar").isSome}"

def main (args : List String) : IO Unit := do
  IO.println "start"
  if args.length > 100 then
    unsafe unused args.length
  IO.println s!"end {args.length}"
