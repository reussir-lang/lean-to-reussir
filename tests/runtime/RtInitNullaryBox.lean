/-! Runtime test (review of clean step A1's C8): constants whose values are
nullary variants or hold them, set through a box of the value
(docs/implementation/startup/constants.md, "A constant of a program type is
set through a box of its value"): `initialize` constants stored by the
startup chain (`l2r_init_put_<k>`) and read through their once-cells (an
`Option` that is `none` and one that is `some`, an empty `List`, an
enumeration, a `[value]` struct over an `Option`), and closed constants (a
function value that is a nullary variant, `[value]` structs whose field is
`none`, a `match` and an `if` whose results are nullary variants), read
once and in a loop. A nullary variant is stored as the box's immediate word
and built from its index at the read. -/

inductive Color where
  | red | green | blue
  deriving Repr, Inhabited

-- A recursive one-field type: a [value] struct over a shared enum with a
-- nullary variant (Option H).
inductive H where
  | mk : Option H → H

instance : Inhabited H := ⟨.mk none⟩

partial def H.depth : H → Nat
  | .mk none => 0
  | .mk (some h) => h.depth + 1

def range (n : Nat) : List Nat := List.range n

-- initialize constants (startup store l2r_init_put_k, read via initConst)
initialize gNone : Option Nat ← pure ((range 3).find? (· > 10))
initialize gNil : List Nat ← pure ((range 3).filter (· > 10))
initialize gCol : Color ← pure (if (range 2).length > 1 then .green else .red)
initialize gH : H ← pure (.mk none)
initialize gSome : Option Nat ← pure ((range 30).find? (· > 10))

-- closed constants
def fSucc : Nat → Nat := Nat.succ
def hNone : H := .mk ((range 3).find? (· > 10) |>.map fun _ => .mk none)
def hNone2 : H := .mk none
def br : Option Nat := match (range 3).length with
  | 3 => none
  | n => some n
def lst : List Nat := if (range 3).length == 3 then [] else [1]

def loop : Nat → Nat → Nat
  | 0, acc => acc
  | n + 1, acc => loop n (acc + gNone.getD 1 + gNil.length
      + (match gCol with | .green => 2 | _ => 0)
      + gH.depth + gSome.getD 0 + fSucc n + hNone.depth + hNone2.depth + br.getD 5 + lst.length)

def main : IO Unit := do
  IO.println (repr gNone)
  IO.println gNil
  IO.println (repr gCol)
  IO.println gH.depth
  IO.println (repr gSome)
  IO.println (fSucc 1)
  IO.println hNone.depth
  IO.println hNone2.depth
  IO.println (repr br)
  IO.println lst
  IO.println (loop 1000 0)
