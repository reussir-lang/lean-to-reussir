/-! Runtime test: case `A833` of the shared dependent-type corpus (programs
built by another translator's team and checked against native Lean). It
checks: A dependent arrow (`useFn (f : (b : Bool) → (if b then List Nat else
List (List Nat)) → Nat)`) keeps the arity of its binders, its inner domain
keyed, so `lenP` passed as `f` is L8's eta ... -/
namespace UF
@[noinline] def pickL {α : Type} (b : Bool) (x : α) : if b then List α else List (List α) :=
  match b with | true => [x, x, x] | false => [[x], [x]]
@[noinline] def lenP {α : Type} (b : Bool) (v : if b then List α else List (List α)) : Nat :=
  match b, v with
  | true, xs => xs.length
  | false, xss => xss.length + 10
@[noinline] def useFn (f : (b : Bool) → (if b then List Nat else List (List Nat)) → Nat) (b : Bool) (n : Nat) : Nat :=
  f b (pickL b n)
@[noinline] def useFnS (f : (b : Bool) → (if b then List String else List (List String)) → Nat) (b : Bool) : Nat :=
  f b (pickL b "q")
@[noinline] def applyAll (f : (b : Bool) → (if b then List Nat else List (List Nat)) → Nat) (n : Nat) : List Nat :=
  [f true (pickL true n), f false (pickL false n)]
end UF
def main (args : List String) : IO Unit := do
  let n := args.length
  IO.println s!"{[UF.useFn UF.lenP true n, UF.useFn UF.lenP false n, UF.useFnS UF.lenP true, UF.useFnS (UF.lenP (α := String)) false]} {UF.applyAll UF.lenP n}"
