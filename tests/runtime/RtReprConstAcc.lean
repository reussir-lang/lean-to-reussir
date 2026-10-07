/-! Runtime test: closed terms that the instance of a helper shares across
all its callers: a fold's initial accumulator (`#[]`, `Array.mkEmpty 0`)
and a default list (design review of the layout redesign, correctness,
DRC-08). A constant is made once and read by every call; its layout must
be the one each reader expects. -/
@[noinline] def collect (xs : List Nat) : Array Nat :=
  xs.foldl (fun acc x => acc.push (x * 2)) #[]

@[noinline] def withDefault (o : Option (List Nat)) : List Nat :=
  o.getD [1, 2, 3]

def main (args : List String) : IO Unit := do
  let n := (args.headD "3").toNat!
  IO.println s!"{collect (List.range n)} {withDefault none} {withDefault (some [n])}"
