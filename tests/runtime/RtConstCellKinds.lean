/-! Runtime test: constants and closed terms of each kind of program type,
which lean2rr sets through its enum `L2RConstCell` (`onceCell`: a slot
gets the word of the variant's field), read many times and updated: a
record, an inductive with a nullary and a non-nullary constructor (a
constant that is the nullary one, an immediate word, and one that is not),
an enumeration (stored in an `ElemBox`), a one-field structure of a
scalar, a function value, an array of records, a reference made by
`initialize` (the startup chain's store), a thunk, and a toolchain type
(`Std.Format`). A value read from a constant is never unique: an update
copies it, and the constant keeps its value. -/

structure P where
  a : Nat
  b : String
  deriving Repr, Inhabited

inductive E where
  | leaf
  | node (l : E) (v : Nat) (r : E)
  deriving Repr

-- An enumeration: stored in an `ElemBox`, itself set through the enum.
inductive Color where
  | red | green | blue
  deriving Repr

-- A one-field structure of a scalar: a `[value]` struct for lean2rr.
structure W where
  w : UInt64
  deriving Repr

def range (n : Nat) : List Nat := List.range n

def p : P := { a := (range 10).foldl (· + ·) 0, b := String.ofList ((range 3).map fun i => Char.ofNat (97 + i)) }

def eLeaf : E := if (range 4).length > 3 then .leaf else .node .leaf 0 .leaf

def eNode : E := (range 3).foldl (fun t i => .node t i .leaf) .leaf

def col : Color := if (range 2).length > 1 then .blue else .red

def w : W := { w := ((range 7).foldl (· + ·) 0).toUInt64 * 1000 }

def f : Nat → Nat := (range 5).foldl (fun g i => fun x => g x + i) id

def ps : Array P := (range 4).toArray.map fun i => { a := i, b := toString i }

def th : Thunk Nat := Thunk.mk fun _ => (range 20).foldl (· + ·) 0

def fmt : Std.Format := .group (.nest 2 (.text "a" ++ .line ++ .text (toString (range 3))))

initialize counter : IO.Ref Nat ← IO.mkRef ((range 6).foldl (· + ·) 0)

def depth : E → Nat
  | .leaf => 0
  | .node l _ r => max (depth l) (depth r) + 1

@[noinline] def bump (q : P) (i : Nat) : P := { q with a := q.a + i }

def loop : Nat → Nat → Nat
  | 0, acc => acc
  | n + 1, acc => loop n (acc + p.a + depth eNode + depth eLeaf + w.w.toNat + f n + (ps[n % 4]!).a + th.get)

def main : IO Unit := do
  IO.println (repr p)
  IO.println (repr eLeaf)
  IO.println (repr eNode)
  IO.println (repr w)
  IO.println (repr col)
  IO.println (f 10)
  IO.println (ps.map (·.b))
  IO.println th.get
  IO.println fmt
  IO.println (loop 1000 0)
  -- Updates copy: the constants keep their values.
  let q := bump p 5
  let ps2 := ps.set! 0 { a := 99, b := "x" }
  IO.println s!"{q.a} {p.a} {(ps2[0]!).a} {(ps[0]!).a}"
  counter.modify (· + 1)
  IO.println (← counter.get)
  counter.modify (· + 1)
  IO.println (← counter.get)
