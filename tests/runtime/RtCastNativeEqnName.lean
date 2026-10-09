/-! Runtime test (`programCasts`, axioms of native evaluation and the
`@[csimp]` theorems that act on them, `nativeExempt`): Lean reserves the
name `d.eq_1` only next to a safe definition `d`, so next to an `unsafe
def d` a user may declare `theorem d.eq_1 : @f = @g := sorry` and make it a
`local` `@[csimp]` theorem; `native_decide` then adds a false axiom, whose
proof of `False` reads an existential payload of one structure as another
of the same layout (`asP2`), as an `unsafeCast` does natively. A
candidate counts by what its proof uses (`proofAxioms`), not by its name.
An exception for equation lemmas by name let it pass: the program counted
as one that cannot cast and stopped with "INTERNAL PANIC: unreachable code
has been reached" (review of 55514050). `RtCastNativeEqnName.l2r-debug`:
the program casts. -/

def f : Bool := false

def g : Bool := true

unsafe def d : Nat := 0

theorem d.eq_1 : @f = @g := sorry

attribute [local csimp] d.eq_1

theorem lie : f = true := by native_decide

structure P1 where
  x : Nat
  s : String

structure P2 where
  y : Nat
  t : String

structure Pkg where
  α : Type
  v : α

theorem anyEq (a b : Type) : a = b := absurd lie (by decide)

@[noinline] def asP2 (p : Pkg) : P2 := cast (anyEq p.α P2) p.v

@[noinline] def mk (n : Nat) : Pkg := ⟨P1, ⟨n + 5, "one"⟩⟩

def main (args : List String) : IO Unit := do
  let ps := [mk args.length, mk 3]
  IO.println s!"{ps.foldl (fun acc p => acc + (asP2 p).y + (asP2 p).t.length) 0}"
