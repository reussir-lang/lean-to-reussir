/-! Runtime test (review CLR-01): a cast through a `Box` whose conversion
needs a function value at another representation (a wrapper, plan §5.1).
`asF2` reads a package holding `F1 {t, f : Nat → T1}` as
`F2 {t, f : Nat → T2}`: converting `f` needs the wrapper `w<Nat → T1>` of
`Nat → T2` and the conversion `l2r_fconv_…` between them. The only other
code that would register that wrapper, the unboxing of `G T1` as `G T2` in
`deadRead`, is lowered but never runs (`deadRead` is a field of `Holder`
that nothing applies), so with `conv-liveness` its helper is never
generated. The cast converts all the same, natively `F 3`: it used to
panic with the pass on, because a cast was kept only when its wrapper was
registered already. -/
structure Pkg where
  α : Type
  v : α

inductive T1 | leaf | node (l : T1) (x : Nat) (r : T1)
inductive T2 | leaf | node (l : T2) (y : Int) (r : T2)

structure G (α : Type) where
  t : Nat
  f : Nat → α

structure F1 where
  t : Nat
  f : Nat → T1
structure F2 where
  t : Nat
  f : Nat → T2

def T2.sum : T2 → Nat
  | .leaf => 0
  | .node l y r => l.sum + y.toNat + r.sum

@[noinline] def deadPkg (k : Nat) : Pkg := ⟨G T1, ⟨k, fun n => .node .leaf (n + k) .leaf⟩⟩
@[noinline] def useG (g : G T2) : Nat := g.t + (g.f 3).sum
@[noinline] unsafe def deadRead (p : Pkg) : Nat := useG (unsafeCast p.v : G T2)

structure Holder where
  n : Nat
  h : Pkg → Nat

@[noinline] def pkgTag (_p : Pkg) : Nat := 7

@[noinline] def useHolder (x : Holder) : Nat := x.n + 1

@[noinline] def pkgF (k : Nat) : Pkg := ⟨F1, ⟨k, fun n => .node .leaf (n + k) .leaf⟩⟩
@[noinline] unsafe def asF2 (p : Pkg) : Nat := match (unsafeCast p.v : F2) with
  | ⟨t, f⟩ => t + (f 3).sum

unsafe def main (args : List String) : IO Unit := do
  let k := args.length
  IO.println s!"holder {useHolder ⟨k, deadRead⟩}"
  IO.println s!"dead pkg {pkgTag (deadPkg k)}"
  IO.println s!"F {asF2 (pkgF k)}"
