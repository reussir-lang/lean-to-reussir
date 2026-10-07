/-! Runtime test: results of two-constructor types (optimization
`flatten-structs`): `EST.Out` (every `IO` result), `Except`, `Option`,
`ForInStep`, nested in structures and in each other, returned as a tag and
the fields of both constructors (placeholders for the constructor the
value does not have). The outputs must equal native's in every shape:
- an interpreter in `ReaderT Ctx (ExceptT String (StateT Nat IO))` with
  `throw`, `tryCatch`, early `return`, `for` with `break`, and an error arm
  that returns the callee's result of another type unchanged;
- `IO` errors raised by the runtime (a missing file) and caught;
- `Option` results matched, and stored whole (rebuilt from the tag and
  fields: a `cases` on the tag);
- a closed constant result (`pure 0`, `none`), returned as a known
  constructor;
- a type whose placeholder is not finite (`Except Empty Nat`: not split);
- a loop whose state goes out in `ForInStep.yield`. -/

structure Ctx where
  limit : Nat
  name : String

abbrev M := ReaderT Ctx (ExceptT String (StateT Nat IO))

@[noinline] def step (k : Nat) : M Nat := do
  let ctx ← read
  modify (· + 1)
  if k > ctx.limit then throw s!"{ctx.name}: {k} over {ctx.limit}"
  if k % 7 == 3 then return k * 2
  pure (k + 1)

@[noinline] def run (ks : List Nat) : M Nat := do
  let mut acc := 0
  for k in ks do
    if k == 999 then break
    let v ← tryCatch (step k) fun e => do
      if e.length > 40 then throw e
      pure 0
    acc := acc + v
  return acc

@[noinline] def runAll (n : Nat) (lim : Nat) : IO String := do
  let r ← ((run ((List.range n).map (· * 3))).run { limit := lim, name := "ctx" }).run 0
  match r with
  | (.ok v, s) => return s!"ok {v} steps {s}"
  | (.error e, s) => return s!"error {e} steps {s}"

@[noinline] def readMissing (path : String) : IO (Option Nat) := do
  try
    let s ← IO.FS.readFile path
    return some s.length
  catch _ => return none

@[noinline] def findFirst (p : Nat → Bool) : List Nat → Option Nat
  | [] => none
  | x :: xs => if p x then some (x * 10) else findFirst p xs

@[noinline] def decode (k : Nat) : Except String Nat :=
  if k % 5 == 0 then .error s!"bad {k}" else if k % 5 == 1 then pure 0 else .ok (k * k)

@[noinline] def sumDecoded (n : Nat) : Nat × Nat := Id.run do
  let mut ok := 0
  let mut bad := 0
  for k in [0:n] do
    match decode k with
    | .ok v => ok := ok + v
    | .error _ => bad := bad + 1
  return (ok, bad)

@[noinline] def emptyErr (k : Nat) : Except Empty Nat := .ok (k + 1)

@[noinline] def countWhile (xs : List Nat) (lim : Nat) : Nat × Nat := Id.run do
  let mut s := 0
  let mut c := 0
  for x in xs do
    if s + x > lim then break
    s := s + x
    c := c + 1
  return (s, c)

def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 300
  IO.println (← runAll n (n * 2))
  IO.println (← runAll n (n / 2))
  IO.println (← runAll 5 1)
  IO.println s!"missing {← readMissing "/nonexistent/l2r-flatten-test"}"
  let found := (List.range 20).map fun k => findFirst (· > k * 3) (List.range 50)
  IO.println s!"found {found.take 5} {findFirst (· > 100) (List.range 50)}"
  let mut hits := 0
  for k in [0:n] do
    match findFirst (· > k % 60) (List.range 50) with
    | some v => hits := hits + v
    | none => hits := hits + 1
  IO.println s!"hits {hits}"
  let stored := [decode 3, decode 5, decode 6]
  IO.println s!"stored {stored.map fun | .ok v => toString v | .error e => e}"
  IO.println s!"decoded {sumDecoded n}"
  IO.println s!"emptyErr {match emptyErr n with | .ok v => v | .error e => nomatch e}"
  IO.println s!"countWhile {countWhile (List.range n) (n * 4)}"
