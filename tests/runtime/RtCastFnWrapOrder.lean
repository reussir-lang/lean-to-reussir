/-! Runtime test (review CLR-01): `RtCastFnWrapLive` with the use of
`deadRead` after the cast instead of before it. That order was enough for
the cast to be kept when a cast needing a wrapper was kept only if the
wrapper was registered already; whether it converts now depends on the
types only (natively `F 3`). -/
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
  IO.println s!"dead pkg {pkgTag (deadPkg k)}"
  IO.println s!"F {asF2 (pkgF k)}"
  if k > 100 then IO.println s!"live read {deadRead (deadPkg k)}"
