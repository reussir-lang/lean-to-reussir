/-! Runtime test: values of a parameter's type that only go back into
boxes keep their boxes (lean2rr: `boxedOnlyVars`, `boxUnboxed?`). A
`List.reverse`, an accumulator copy, an `Array.push` of a pair's field, an
`Array.get!` result consed onto a list, and a pair's field used as
`get!`'s default pass the field's box on instead of unboxing it and boxing
it again: at types held as immediates (`Nat`, `Bool`, `UInt8`, an
enumeration), as leanrt's kinds (`String`, a big `Nat`, `Array`), as cells
(`Float`, a `UInt64` from 2^63) and as the program's records and enums (a
structure, an inductive with a constructor without fields, `Option`). The
default of `get!` reaches the read extern as a box (the read's index
binding must not take it for the `Nat` index). -/

structure P where
  name : String
  n : Nat
deriving Repr, Inhabited

inductive Shape where
  | dot
  | circle (r : Nat)
  | rect (w h : Nat)
deriving Repr, Inhabited

inductive Color where
  | red | green | blue
deriving Repr, Inhabited

@[noinline] def rev {α : Type} (xs : List α) : List α := xs.reverse

@[noinline] def copy {α : Type} : List α → List α → List α
  | [], acc => acc.reverse
  | x :: xs, acc => copy xs (x :: acc)

@[noinline] def seconds {α β : Type} : List (α × β) → Array β → Array β
  | [], acc => acc
  | (_, b) :: r, acc => seconds r (acc.push b)

@[noinline] def grab {α : Type} [Inhabited α] (a : Array α) : Nat → List α → List α
  | 0, acc => acc
  | i + 1, acc => grab a i (a[i]! :: acc)

@[noinline] def getOr (p : Nat × Array Nat) (i : Nat) : Nat :=
  let (d, arr) := p
  haveI : Inhabited Nat := ⟨d⟩
  arr[i]!

@[noinline] def getOrS (p : String × Array String) (i : Nat) : String :=
  let (d, arr) := p
  haveI : Inhabited String := ⟨d⟩
  arr[i]!

def both {α : Type} [Repr α] (xs : List α) : IO Unit := do
  IO.println s!"{repr (rev xs)} {repr (copy xs [])}"

def main : IO Unit := do
  both ["a", "bc", ""]
  both [1, 2, 2 ^ 70, 3]
  both [true, false, false]
  both [(7 : UInt8), 200, 0]
  both [(2 ^ 64 - 1 : UInt64), 5, 2 ^ 63, 2 ^ 63 - 1]
  both [(1.5 : Float), -0.0, 2.0e300, 0.1]
  both [P.mk "x" 1, P.mk "y" (2 ^ 65)]
  both [Shape.dot, .circle 2, .rect 1 2, .dot]
  both [Color.blue, .red, .green]
  both [some 1, none, some (2 ^ 64)]
  both [#[1, 2], #[], #[3]]
  IO.println (seconds [(1, "one"), (2, "two")] #["zero"])
  IO.println (seconds [("a", (2.5 : Float)), ("b", 1.0e-3)] #[])
  IO.println (seconds [((), (2 ^ 64 - 2 : UInt64)), ((), 9)] #[])
  IO.println (repr (seconds [(0, P.mk "p" 3), (1, P.mk "q" 4)] #[]))
  IO.println (grab #["u", "v", "w"] 3 ["end"])
  IO.println (grab #[(1.25 : Float), 3.5] 2 [])
  IO.println (repr (grab #[Shape.rect 3 4, .dot] 2 []))
  IO.println (getOr (42, #[1, 2, 3]) 1)
  IO.println (getOr (42, #[1, 2, 3]) 7)
  IO.println (getOr (2 ^ 80, #[]) 0)
  IO.println (getOrS ("dflt", #["s"]) 0)
  IO.println (getOrS ("dflt", #["s"]) 3)
