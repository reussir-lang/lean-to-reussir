/-! Runtime test (a bug hunt of the names lean2rr recognizes, 2026-10-27):
a program's own structures named `L2RFlat.Tuple2` and `L2RFlat.Tuple3`,
the names that optimization `flatten-structs` gave its tuple pseudo-type
for the fields of a structure result. lean2rr took the program's type for
the pseudo-type (`flatTupleArity?` matched the name) and failed (`a flat
tuple built at type T_L2RFlat_Tuple2_… (internal error)`). Now the
pseudo-type is `_l2r_flat_tuple.<k>`, a name no program can declare. The
program's structures are built, returned, stored in a list and matched,
next to a structure result that the pass does spread (`step`). Natively
the program is valid Lean. -/

structure L2RFlat.Tuple2 where
  a : Nat
  b : String

structure L2RFlat.Tuple3 (α : Type) where
  x : α
  y : UInt64
  z : Bool

structure SumAcc where
  sum : Nat
  last : UInt64

@[noinline] def mkT (n : Nat) : L2RFlat.Tuple2 := ⟨n, toString (n + 1)⟩

@[noinline] def mkT3 (n : Nat) : L2RFlat.Tuple3 String := ⟨s!"v{n}", n.toUInt64 * 3, n % 2 == 0⟩

@[noinline] def step (acc : SumAcc) (i : Nat) : SumAcc := ⟨acc.sum + i, acc.last + i.toUInt64⟩

def main (args : List String) : IO Unit := do
  let n := args.length + 7
  let t := mkT n
  IO.println s!"{t.a} {t.b}"
  let ts := (List.range 3).map fun i => mkT (n + i)
  IO.println s!"{ts.map (·.a)} {ts.map (·.b)}"
  let u := mkT3 n
  IO.println s!"{u.x} {u.y} {u.z}"
  let mut acc : SumAcc := ⟨0, 0⟩
  for i in [0:n] do
    acc := step acc i
  IO.println s!"{acc.sum} {acc.last}"
