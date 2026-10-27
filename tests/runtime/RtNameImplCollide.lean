/-! Runtime test (a bug hunt of the names lean2rr recognizes, 2026-10-27):
a program's own types named `T._impl` next to a `T` without computed
fields. Lean names the implementation of a type with computed fields
`T._impl` and recognizes such a type by `T.casesOn`'s `implemented_by`;
lean2rr recognized one by the name alone, so `Foo` was lowered as
`Foo._impl` and the build failed (`constructor Foo.mk not in type
T_Foo__impl_…`). Now every place asks `computedImpl?`. Covered: a structure
and a structure `Foo._impl`; an enumeration whose `_impl` is a structure,
both in arrays (the compact array kinds: an enumeration is stored by its
index); an inductive with two constructors whose `_impl` is an
enumeration, in a list and an array. Natively the program is valid Lean. -/

structure Foo where
  a : Nat
  b : String

structure Foo._impl where
  x : UInt8
  y : UInt8

inductive Color where
  | red | green | blue
  deriving Repr, BEq

structure Color._impl where
  n : Nat
  s : String

inductive Shape where
  | circle (r : Nat)
  | rect (w h : Nat)

inductive Shape._impl where
  | p | q | r
  deriving Repr

@[noinline] def mkFoo (n : Nat) : Foo := ⟨n, toString (n * 2)⟩
@[noinline] def mkImpl (n : Nat) : Foo._impl := ⟨n.toUInt8, (n + 1).toUInt8⟩

@[noinline] def colors (n : Nat) : Array Color := Id.run do
  let mut a := #[]
  for i in [0:n] do
    a := a.push (match i % 3 with | 0 => .red | 1 => .green | _ => .blue)
  return a

@[noinline] def colorImpls (n : Nat) : Array Color._impl :=
  (List.range n).toArray.map fun i => ⟨i, s!"c{i}"⟩

def Shape.area : Shape → Nat
  | .circle r => 3 * r * r
  | .rect w h => w * h

def Shape._impl.tag : Shape._impl → Nat
  | .p => 1
  | .q => 2
  | .r => 3

@[noinline] def shapes (n : Nat) : List Shape :=
  (List.range n).map fun i => if i % 2 == 0 then .circle i else .rect i (i + 1)

@[noinline] def shapeImpls (n : Nat) : Array Shape._impl :=
  (List.range n).toArray.map fun i => match i % 3 with | 0 => .p | 1 => .q | _ => .r

def main (args : List String) : IO Unit := do
  let n := args.length + 5
  let f := mkFoo n
  IO.println s!"{f.a} {f.b}"
  let i := mkImpl n
  IO.println s!"{i.x} {i.y}"
  let cs := colors n
  IO.println s!"{repr cs} {cs.size} {(cs.filter (· == .green)).size}"
  let ci := colorImpls n
  IO.println s!"{ci.foldl (fun acc c => acc + c.n) 0} {String.intercalate "," (ci.toList.map (·.s))}"
  IO.println s!"{(shapes n).map Shape.area}"
  let si := shapeImpls n
  IO.println s!"{repr si} {si.foldl (fun acc s => acc + s.tag) 0}"
