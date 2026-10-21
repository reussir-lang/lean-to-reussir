/-! Runtime test: `dbgTraceIfShared` at Reussir record types (clean step
C7: lean2rr calls the record texture, and leanrt answers from the record's
handle word, `leanrt::is_shared_record`). A shared tree node, a shared
`some`, a shared list cell and a shared constructor of a type without a
nullary variant are reported, as natively; a unique one is not. A nullary
constructor of a type with a nullary variant (`Tree.leaf`, `[]`, `none`) is
a scalar natively (`box(0)`) and never reported, also when the program
holds it twice; lean2rr encodes it as an immediate: the `tbi` form by
default on aarch64, the `immortal` form with rrc's
`--nullary-variant-encoding arch-independent` (`L2R_RRC_FLAGS`; the test
passes either way). A constructor of an enumeration (all constructors
nullary) is a scalar in both. -/

inductive Tree where
  | leaf
  | node (l : Tree) (v : Nat) (r : Tree)

inductive Shape where
  | circle (r : Nat)
  | rect (w h : Nat)

inductive Color where
  | red
  | green

@[noinline] def mkTree : Nat → Tree
  | 0 => .leaf
  | k + 1 => .node (mkTree k) (k + 1) .leaf

@[noinline] def size : Tree → Nat
  | .leaf => 0
  | .node l _ r => size l + 1 + size r

@[noinline] def area : Shape → Nat
  | .circle r => 3 * r * r
  | .rect w h => w * h

@[noinline] def mkShape (n : Nat) : Shape :=
  if n % 2 == 0 then .rect (n + 2) 3 else .circle n

@[noinline] def code : Color → Nat
  | .red => 1
  | .green => 2

@[noinline] def mkColor (n : Nat) : Color := if n == 0 then .green else .red

def main (args : List String) : IO Unit := do
  let n := args.length
  -- A shared node and a unique one.
  let t := mkTree (n + 3)
  let t2 := t
  let t' := dbgTraceIfShared "shared node" t
  IO.println (size t' + size t2)
  let u := mkTree (n + 2)
  let u' := dbgTraceIfShared "unique node" u
  IO.println (size u')
  -- A nullary constructor (made at run time, then a literal), once and twice.
  let lf := mkTree n
  let lf' := dbgTraceIfShared "leaf once" lf
  IO.println (size lf')
  let lt := mkTree n
  let lt2 := lt
  let lt' := dbgTraceIfShared "leaf twice" lt
  IO.println (size lt' + size lt2)
  let ll := dbgTraceIfShared "leaf literal" Tree.leaf
  IO.println (size ll)
  -- Option: `some` shared and unique, `none` once and twice.
  let o : Option Nat := if n == 0 then some (n + 7) else none
  let o2 := o
  let o' := dbgTraceIfShared "shared some" o
  IO.println (o'.getD 0 + o2.getD 0)
  let p : Option Nat := if n == 0 then some (n + 8) else none
  let p' := dbgTraceIfShared "unique some" p
  IO.println (p'.getD 0)
  let z : Option Nat := if n == 0 then none else some n
  let z2 := z
  let z' := dbgTraceIfShared "none twice" z
  IO.println (z'.getD 5 + z2.getD 5)
  -- Lists: a shared cell, `[]` once and twice.
  let xs := List.replicate (n + 2) n
  let xs2 := xs
  let xs' := dbgTraceIfShared "shared cell" xs
  IO.println (xs'.length + xs2.length)
  let e : List Nat := List.replicate n 0
  let e2 := e
  let e' := dbgTraceIfShared "nil twice" e
  IO.println (e'.length + e2.length)
  -- A type without a nullary variant: shared and unique.
  let s := mkShape n
  let s2 := s
  let s' := dbgTraceIfShared "shared shape" s
  IO.println (area s' + area s2)
  let r := mkShape (n + 1)
  let r' := dbgTraceIfShared "unique shape" r
  IO.println (area r')
  -- An enumeration: a scalar, once and twice.
  let c := mkColor n
  let c2 := c
  let c' := dbgTraceIfShared "color" c
  IO.println (code c' + code c2)
