/-! Runtime test: a cycle of tail calls in a program that casts (a user
`implemented_by` with an `unsafe` implementation) and opens a file, where
lean2rr emulates Lean's borrowed parameters by type. `d`'s parameter
`n : Nat` goes on to `e`'s parameter `c : F b`, a value of a type that
depends on a value (`lcAny` in mono code), which `e` only compares (Lean
borrows it), and `e` passes it back: natively both are borrowed, nothing is
released after either call, and the cycle runs in constant stack: 10^6
steps on an 8 MB stack (`.pipe`; the inputs come from the arguments, so the
code cannot fold them). flatten-structs rewrites `d` (its base case passes
a pair to `gsum`, which the pass splits). Counting every parameter of a
rewritten declaration as owned (`borrowInfo`) made `d` keep `n` until `e`
returned (the type rule: an `lcAny` parameter may hold a resource), so each
step was a call and the stack overflowed (round 2 of the review of
xlate-regress); only a parameter whose own type may hold one (a closure, a
thunk, a task) counts as owned there, and only an argument whose own type
may hold one is kept. -/

def F : Bool → Type
  | true => Nat
  | false => String

@[noinline] def gsum (s : Nat × Nat) : Nat := s.1 + s.2

mutual
@[noinline] partial def d (n : Nat) (m : Nat) (k : UInt64) : Nat :=
  if k == 0 then gsum (m + 1, 1) else e true n m (k - 1)
@[noinline] partial def e (b : Bool) (c : F b) (m : Nat) (k : UInt64) : Nat :=
  match b, c with
  | true, (c : Nat) => if c == 7 then 7 else d m m (k - 1)
  | false, (_ : String) => 0
end

unsafe def bumpImpl (n : Nat) : Nat := n + 1
@[implemented_by bumpImpl] def bump (n : Nat) : Nat := n + 1

def main (args : List String) : IO Unit := do
  IO.println s!"cast {bump 1}"
  IO.FS.writeFile "rtbcfc.txt" "x"
  let k := (args.headD "1000000").toNat!.toUInt64
  IO.println s!"cycle {d (args.length + 3) (args.length + 2) k}"
  IO.print (← IO.FS.readFile "rtbcfc.txt")
  IO.FS.removeFile "rtbcfc.txt"
