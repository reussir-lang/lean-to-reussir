/-! Runtime test (review of the memoized resource question, 2026-10-26): a
dense mutual block of eight inductives, each with a constructor per member
taking `Dj → List Dj → Option Dj → Di`, in a program that makes a resource
(a file handle) and passes a `D0` to a borrowed parameter. The lowering of
the call asks whether a `D0` may hold a resource (Lower/Borrow's
`mayHoldResource`); a search along every simple path through the block,
with a cycle cut on the path only, took exponential time (about 20 times
longer per member: 41 s at seven members, minutes at eight), and still did
when it kept a `false` only where the search below met no type above it on
the path (22 s at seven). A reachability with one visited set per question
is linear: the program translates in well under a second. -/
mutual
inductive D0 where
  | leaf : Nat → D0
  | c0 : D0 → List D0 → Option D0 → D0
  | c1 : D1 → List D1 → Option D1 → D0
  | c2 : D2 → List D2 → Option D2 → D0
  | c3 : D3 → List D3 → Option D3 → D0
  | c4 : D4 → List D4 → Option D4 → D0
  | c5 : D5 → List D5 → Option D5 → D0
  | c6 : D6 → List D6 → Option D6 → D0
  | c7 : D7 → List D7 → Option D7 → D0
inductive D1 where
  | leaf : Nat → D1
  | c0 : D0 → List D0 → Option D0 → D1
  | c1 : D1 → List D1 → Option D1 → D1
  | c2 : D2 → List D2 → Option D2 → D1
  | c3 : D3 → List D3 → Option D3 → D1
  | c4 : D4 → List D4 → Option D4 → D1
  | c5 : D5 → List D5 → Option D5 → D1
  | c6 : D6 → List D6 → Option D6 → D1
  | c7 : D7 → List D7 → Option D7 → D1
inductive D2 where
  | leaf : Nat → D2
  | c0 : D0 → List D0 → Option D0 → D2
  | c1 : D1 → List D1 → Option D1 → D2
  | c2 : D2 → List D2 → Option D2 → D2
  | c3 : D3 → List D3 → Option D3 → D2
  | c4 : D4 → List D4 → Option D4 → D2
  | c5 : D5 → List D5 → Option D5 → D2
  | c6 : D6 → List D6 → Option D6 → D2
  | c7 : D7 → List D7 → Option D7 → D2
inductive D3 where
  | leaf : Nat → D3
  | c0 : D0 → List D0 → Option D0 → D3
  | c1 : D1 → List D1 → Option D1 → D3
  | c2 : D2 → List D2 → Option D2 → D3
  | c3 : D3 → List D3 → Option D3 → D3
  | c4 : D4 → List D4 → Option D4 → D3
  | c5 : D5 → List D5 → Option D5 → D3
  | c6 : D6 → List D6 → Option D6 → D3
  | c7 : D7 → List D7 → Option D7 → D3
inductive D4 where
  | leaf : Nat → D4
  | c0 : D0 → List D0 → Option D0 → D4
  | c1 : D1 → List D1 → Option D1 → D4
  | c2 : D2 → List D2 → Option D2 → D4
  | c3 : D3 → List D3 → Option D3 → D4
  | c4 : D4 → List D4 → Option D4 → D4
  | c5 : D5 → List D5 → Option D5 → D4
  | c6 : D6 → List D6 → Option D6 → D4
  | c7 : D7 → List D7 → Option D7 → D4
inductive D5 where
  | leaf : Nat → D5
  | c0 : D0 → List D0 → Option D0 → D5
  | c1 : D1 → List D1 → Option D1 → D5
  | c2 : D2 → List D2 → Option D2 → D5
  | c3 : D3 → List D3 → Option D3 → D5
  | c4 : D4 → List D4 → Option D4 → D5
  | c5 : D5 → List D5 → Option D5 → D5
  | c6 : D6 → List D6 → Option D6 → D5
  | c7 : D7 → List D7 → Option D7 → D5
inductive D6 where
  | leaf : Nat → D6
  | c0 : D0 → List D0 → Option D0 → D6
  | c1 : D1 → List D1 → Option D1 → D6
  | c2 : D2 → List D2 → Option D2 → D6
  | c3 : D3 → List D3 → Option D3 → D6
  | c4 : D4 → List D4 → Option D4 → D6
  | c5 : D5 → List D5 → Option D5 → D6
  | c6 : D6 → List D6 → Option D6 → D6
  | c7 : D7 → List D7 → Option D7 → D6
inductive D7 where
  | leaf : Nat → D7
  | c0 : D0 → List D0 → Option D0 → D7
  | c1 : D1 → List D1 → Option D1 → D7
  | c2 : D2 → List D2 → Option D2 → D7
  | c3 : D3 → List D3 → Option D3 → D7
  | c4 : D4 → List D4 → Option D4 → D7
  | c5 : D5 → List D5 → Option D5 → D7
  | c6 : D6 → List D6 → Option D6 → D7
  | c7 : D7 → List D7 → Option D7 → D7
end

@[noinline] def depth (t : @& D0) : Nat := match t with | .leaf n => n | _ => 1

@[noinline] def useIt (t : @& D0) (h : @& IO.FS.Handle) : IO Unit := h.putStrLn s!"{depth t}"

def main (args : List String) : IO Unit := do
  let h ← IO.FS.Handle.mk "/dev/null" .write
  let t := D0.c1 (D1.leaf args.length) [] none
  useIt t h
  IO.println s!"{depth t}"
