/-!
Recursive `@[extern]` definitions of the program (review rv8/ext round 1,
ExtRec): mutual structural recursion with a partner that is not an extern,
a `partial` definition with a `where` helper, `partial_fixpoint`, `let rec`,
well-founded recursion with a lexicographic measure, type-class arguments,
and an extern whose definition calls other externs. lean2rr compiles their
Lean definitions (the `_unsafe_rec` copy Lean compiles for recursive ones);
natively the C code in `RtExternRec.ffi.c` runs.
-/

mutual
@[extern "rc_even"]
def isEven : Nat → Bool
  | 0 => true
  | n + 1 => isOdd n
def isOdd : Nat → Bool
  | 0 => false
  | n + 1 => isEven n
end

@[extern "rc_digits"]
partial def digits (n : Nat) : List Nat := go n []
where go (n : Nat) (acc : List Nat) : List Nat :=
  if n < 10 then n :: acc else go (n / 10) (n % 10 :: acc)

@[extern "rc_search"]
def search (n : Nat) : Option Nat :=
  if n * n > 50 then some n else search (n + 1)
partial_fixpoint

@[extern "rc_sumto"]
def sumTo (n : Nat) : Nat :=
  let rec go (i acc : Nat) : Nat := match i with
    | 0 => acc
    | i + 1 => go i (acc + i + 1)
  go n 0

@[extern "rc_gsum"]
def gsum {α : Type} [Add α] [OfNat α 0] (xs : @& List α) : α := xs.foldl (· + ·) 0

@[extern "rc_chain"]
def chain (n : Nat) : Nat := sumTo n + (if isEven n then 1 else 0)

@[extern "rc_ack"]
def ack : Nat → Nat → Nat
  | 0, n => n + 1
  | m + 1, 0 => ack m 1
  | m + 1, n + 1 => ack m (ack (m + 1) n)
termination_by m n => (m, n)

def main : IO Unit := do
  IO.println s!"even {isEven 10} {isEven 7} odd {isOdd 7}"
  IO.println s!"digits {digits 90210}"
  IO.println s!"search {search 0}"
  IO.println s!"sumTo {sumTo 100}"
  IO.println s!"gsum {gsum [1, 2, 3]} {gsum [1.5, 2.25]}"
  IO.println s!"chain {chain 10} {[3, 4].map chain}"
  IO.println s!"ack {ack 2 3}"
