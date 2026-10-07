/-! Runtime test: calls that Lean's mono `cse` merges across types whose
result types are equal in LCNF because `lcAny` hides the type argument
(`if b then List α else Unit` is `lcAny`). `len` and `fst`, used as function
values at `α := Nat` and at `α := String`, have the type
`Bool → lcAny → Nat` at both, and `mkFn`'s result is `lcAny` at both. Stage 1
aligned the String call to the Nat instance, which reads its input at its
own types: `fst@Nat` unboxed a String element of the list as a `Nat`, and
`mkFn@Nat`'s closure `Nat → Nat`, read at `String → String`, had no
conversion ("INTERNAL PANIC: unreachable code has been reached"; review of
the dependent-type work, shared case A833; `len` passed because it reads only
the list's length). `Mono.serves` now refuses equal types that mention
`lcAny`, and the calls go to the instance at `lcAny` (the uniform code),
which serves both uses: each call runs once, as natively. -/

namespace Len
@[noinline] def mk {α : Type} (b : Bool) (x : α) : if b then List α else Unit :=
  match b with | true => [x] | false => ()
@[noinline] def len {α : Type} (b : Bool) (v : if b then List α else Unit) : Nat :=
  match b, v with | true, xs => xs.length | false, _ => 0
@[noinline] def useN (f : (b : Bool) → (if b then List Nat else Unit) → Nat) : Nat := f true (mk true 1)
@[noinline] def useS (f : (b : Bool) → (if b then List String else Unit) → Nat) : Nat := f true (mk true "a")
def run : String := s!"{useN len} {useS len}"
end Len

namespace Fst
@[noinline] def mk {α : Type} (b : Bool) (x : α) : if b then List α else Unit :=
  match b with | true => [x] | false => ()
@[noinline] def k {α : Type} (x : α) : List α := [x, x]
@[noinline] def fst {α : Type} (b : Bool) (v : if b then List α else Unit) : Nat :=
  match b, v with | true, x :: _ => (k x).length | _, _ => 0
@[noinline] def useN (f : (b : Bool) → (if b then List Nat else Unit) → Nat) : Nat := f true (mk true 1)
@[noinline] def useS (f : (b : Bool) → (if b then List String else Unit) → Nat) : Nat := f true (mk true "a")
def run : String := s!"{useN fst} {useS fst}"
end Fst

namespace Res
@[noinline] def mkFn {α : Type} (b : Bool) (n : Nat) : if b then Option (α → α) else Unit :=
  dbgTrace s!"mkFn {n}" fun _ => match b with | true => some id | false => ()
@[noinline] def runN (v : if true then Option (Nat → Nat) else Unit) : Nat :=
  match v with | some f => f 1 | none => 0
@[noinline] def runS (v : if true then Option (String → String) else Unit) : String :=
  match v with | some f => f "r" | none => ""
def run (n : Nat) : String := s!"{runN (mkFn true n)} {runS (mkFn true n)}"
end Res

def main (args : List String) : IO Unit := do
  IO.println s!"len {Len.run}"
  IO.println s!"fst {Fst.run}"
  IO.println s!"res {Res.run args.length}"
