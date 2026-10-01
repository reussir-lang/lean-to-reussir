/-! Runtime test: results of polymorphically recursive functions (adv2
PrgPoly1). Mono makes one typed instance per type the program uses
(`FSeq.flatten` at `Nat`) and one uniform instance at `lcAny` for the
recursion below it (at `Nat × Nat`, `(Nat × Nat) × (Nat × Nat)`, …), which
calls itself at `lcAny × lcAny`. The typed instance binds the uniform
instance's result at `List (Nat × Nat)`; at the deeper levels the same
function returns lists of pairs of pairs. Stage 3 must not take that one
caller's type as the uniform instance's result type (the value returned
would be converted to `List (Nat × Nat)` at every depth, and unboxing a pair
of pairs as a `Nat` panics). Each function is used at one type only, so that
the typed instance is the uniform instance's only other caller. A result
type that does not depend on the type argument (`Nat`, `String`) holds at
every depth. -/

inductive Digit (α : Type) where
  | one (a : α) | two (a b : α)

inductive FSeq : Type → Type 1 where
  | empty {α} : FSeq α
  | single {α} (a : α) : FSeq α
  | deep {α} (l : Digit α) (m : FSeq (α × α)) (r : Digit α) : FSeq α

-- result `FSeq α`: the self call binds it at `FSeq (α × α)`
def FSeq.cons {α} (x : α) : FSeq α → FSeq α
  | .empty => .single x
  | .single y => .deep (.one x) .empty (.one y)
  | .deep (.one a) m r => .deep (.two x a) m r
  | .deep (.two a b) m r => .deep (.one x) (FSeq.cons (a, b) m) r

-- result `Nat`: the same at every depth
def FSeq.count {α} : FSeq α → Nat
  | .empty => 0
  | .single _ => 1
  | .deep l m r =>
    let d : Digit α → Nat := fun | .one _ => 1 | .two _ _ => 2
    d l + 2 * m.count + d r

-- result `List α`, consumed by `flatMap` after the self call
def FSeq.flatten {α} : FSeq α → List α
  | .empty => []
  | .single a => [a]
  | .deep l m r =>
    let d : Digit α → List α := fun | .one a => [a] | .two a b => [a, b]
    d l ++ (m.flatten.flatMap fun (a, b) => [a, b]) ++ d r

-- result `Option α`, matched after the self call
def FSeq.last? {α} : FSeq α → Option α
  | .empty => none
  | .single a => some a
  | .deep _ m r =>
    match r with
    | .one a => some a
    | .two _ b => match m.last? with
      | some (_, c) => some c
      | none => some b

inductive Nest : Type → Type 1 where
  | nil {α} : Nest α
  | cons {α} (x : α) (rest : Nest (α × α)) : Nest α

def Nest.build {α} (x : α) : Nat → Nest α
  | 0 => .nil
  | n+1 => .cons x (Nest.build (x, x) n)

-- result `List α`, returned through `map`
def Nest.heads {α} (f : α → α) : Nest α → List α
  | .nil => []
  | .cons x r => f x :: (r.heads (fun (a, b) => (f a, f b))).map Prod.fst

-- result `String`: the same at every depth
def Nest.toStr {α} (f : α → String) : Nest α → String
  | .nil => "."
  | .cons x r => f x ++ " :: " ++ r.toStr (fun (a, b) => "(" ++ f a ++ "," ++ f b ++ ")")

def main (args : List String) : IO Unit := do
  let k := args.length + 5
  let s := (List.range (1000 + k)).foldl (fun s i => s.cons i) (FSeq.empty : FSeq Nat)
  IO.println s!"{s.count} {s.flatten.take 10} {s.flatten.length} {s.flatten.foldl (· + ·) 0}"
  IO.println s!"{s.last?} {(FSeq.empty : FSeq Nat).last?}"
  IO.println s!"{(Nest.build (1 : Nat) k).heads (· + 1)}"
  IO.println ((Nest.build "a" 3).toStr id)
