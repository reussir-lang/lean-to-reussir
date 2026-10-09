/-! Runtime test (`programCasts`, axioms of native evaluation and the
`@[csimp]` theorems that act on them, `nativeExempt`): `f_eq`, proved by
`sorry`, replaces `f` (`false`) by `g` (`true`) in compiled code, so
`theorem f_eq.lie : f = true := by native_decide` gets a false axiom,
`f_eq.lie._native.native_decide.ax_1_1`. Its proof of `False` reads an
existential payload of one structure as another of the same layout
(`asP2`), as an `unsafeCast` does natively. A `@[csimp]` theorem comes
after an axiom when the axiom is its own (the declaration in the axiom's
name, `nativeAxiomDecl?`, is the theorem) or its proof uses the axiom. The
test was once a name prefix, which `f_eq.lie` passes: the program counted
as one that cannot cast and stopped with "INTERNAL PANIC: unreachable code
has been reached" (review of 55514050). `RtCastNativePrefix.l2r-debug`:
the program casts. -/

def f : Bool := false

def g : Bool := true

@[csimp] theorem f_eq : @f = @g := sorry

theorem f_eq.lie : f = true := by native_decide

structure P1 where
  x : Nat
  s : String

structure P2 where
  y : Nat
  t : String

structure Pkg where
  α : Type
  v : α

theorem anyEq (a b : Type) : a = b := absurd f_eq.lie (by decide)

@[noinline] def asP2 (p : Pkg) : P2 := cast (anyEq p.α P2) p.v

@[noinline] def mk (n : Nat) : Pkg := ⟨P1, ⟨n + 5, "one"⟩⟩

def main (args : List String) : IO Unit := do
  let ps := [mk args.length, mk 3]
  IO.println s!"{ps.foldl (fun acc p => acc + (asP2 p).y + (asP2 p).t.length) 0}"
