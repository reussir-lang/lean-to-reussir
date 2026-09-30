/-! Runtime test: `cases` and projections directly on `unsafeCast` values
(adv3 RP3-4, RP3-5). Mono erases the cast, so the matched value still has
its own type: another inductive with the same constructor shapes (matched
through its corresponding constructors, fields by position), a structure,
or a `Nat`/`UInt8`/`Bool` used as an enumeration (by index, as natively).
No alternative may be dropped. -/

inductive L1 where
  | nil
  | cons (h : Nat) (t : L1)

inductive L2 where
  | nil
  | cons (h : Nat) (t : L2)

def L1.ofList : List Nat → L1
  | [] => .nil
  | x :: xs => .cons x (L1.ofList xs)

def L2.toList : L2 → List Nat
  | .nil => []
  | .cons h t => h :: t.toList

@[noinline] unsafe def headOr (x : L1) : Nat :=
  match (unsafeCast x : L2) with
  | .cons h _ => h
  | .nil => 0

-- a default arm, and the tail returned at the cast type
@[noinline] unsafe def castDrop (x : L1) : L2 :=
  match (unsafeCast x : L2) with
  | .cons 0 t => t
  | y => y

-- walks the cast list: each step matches a value of the source type
@[noinline] unsafe def sumCast (x : L1) : Nat :=
  match (unsafeCast x : L2) with
  | .cons h t => h + sumCast (unsafeCast t)
  | .nil => 0

inductive C1 where | a | b | c
inductive C2 where | x | y | z
inductive C4 where | p | q | r | s

@[noinline] unsafe def name (v : C1) : String :=
  match (unsafeCast v : C2) with
  | .x => "x" | .y => "y" | .z => "z"

@[noinline] unsafe def name4 (v : C1) : String :=
  match (unsafeCast v : C4) with
  | .p => "p" | .q => "q" | .r => "r" | .s => "s"

@[noinline] unsafe def natToC (n : Nat) : String :=
  match (unsafeCast n : C1) with
  | .a => "a" | .b => "b" | .c => "c"

@[noinline] unsafe def u8ToC (n : UInt8) : String :=
  match (unsafeCast n : C1) with
  | .a => "a" | .b => "b" | .c => "c"

@[noinline] unsafe def boolToC (b : Bool) : String :=
  match (unsafeCast b : C2) with
  | .x => "x" | .y => "y" | .z => "z"

@[noinline] unsafe def cToBool (v : C1) : Bool :=
  match (unsafeCast v : Bool) with
  | true => true
  | false => false

inductive MyOpt (α : Type) where
  | none
  | some (a : α)

@[noinline] unsafe def getD (o : Option Nat) : Nat :=
  match (unsafeCast o : MyOpt Nat) with
  | .some a => a
  | .none => 100

@[noinline] unsafe def getS (o : Option String) : String :=
  match (unsafeCast o : MyOpt String) with
  | .some a => a ++ "!"
  | .none => "none"

structure S1 where
  a : Nat
  b : String

structure S2 where
  x : Nat
  y : String

@[noinline] unsafe def matchS (s : S1) : Nat :=
  match (unsafeCast s : S2) with
  | ⟨x, y⟩ => x + y.length

@[noinline] unsafe def projS (s : S1) : String := (unsafeCast s : S2).y

@[noinline] unsafe def projX (s : S1) : Nat := (unsafeCast s : S2).x * 2

-- a structure whose field is itself of another, isomorphic type
structure P1 where
  n : Nat
  l : L1

structure P2 where
  n : Nat
  l : L2

@[noinline] unsafe def pSum (p : P1) : Nat :=
  match (unsafeCast p : P2) with
  | ⟨n, l⟩ => n + l.toList.foldl (· + ·) 0

unsafe def main (args : List String) : IO Unit := do
  let k := args.length
  IO.println s!"{headOr (.cons (5 + k) .nil)} {headOr .nil}"
  let l := L1.ofList [0, 3 + k, 4]
  IO.println s!"{(castDrop l).toList} {(castDrop (L1.ofList [5])).toList} {(castDrop .nil).toList}"
  IO.println s!"{sumCast (L1.ofList (List.range (100 + k)))}"
  IO.println s!"{name .a} {name .b} {name .c}"
  IO.println s!"{name4 .a} {name4 .c}"
  IO.println s!"{natToC k} {natToC (2 + k)} {u8ToC (1 + k.toUInt8)} {u8ToC 2}"
  IO.println s!"{boolToC (k == 0)} {boolToC (k != 0)} {cToBool .a} {cToBool .b}"
  IO.println s!"{getD (some (7 + k))} {getD none} {getS (some "s")} {getS none}"
  let s : S1 := ⟨3 + k, "abc"⟩
  IO.println s!"{matchS s} {projS s} {projX s}"
  IO.println s!"{pSum ⟨1 + k, L1.ofList [1, 2, 3]⟩}"
