/-! Runtime test: `Nat.repr`/`Int.repr`. Natively `Nat.repr n` for `n < 128`
returns the string held by the closed term `Nat.reprArray` (the same object
every time, so it is shared: `dbgTraceIfShared` reports it); larger values
build a fresh string. Checks the digits around the boundaries (127/128,
2^63, 2^64), that updates of a shared result copy it, and
`dbgTraceIfShared`. -/

@[noinline] def rep (n : Nat) : String := toString n
@[noinline] def irep (n : Int) : String := toString n

def main (args : List String) : IO Unit := do
  let k := args.length
  for n in [0, 1, 9, 10, 99, 100, 126, 127, 128, 129, 255, 1000] do
    IO.println s!"{n}: {rep (n + k)} {irep (n + k)} {irep (-(n + k : Int))} {(n + k).repr} {Nat.repr (n + k) |>.length}"
  for n in [9223372036854775807, 9223372036854775808, 18446744073709551615, 18446744073709551616, 2^100] do
    IO.println s!"big {rep n} {irep n} {irep (-n)}"
  -- the result is shared below 128: updates copy it
  let a := rep (5 + k)
  let b := a.push '!'
  let c := (String.Pos.Raw.mk 0).set (rep (5 + k)) 'Q'
  let d := rep (5 + k) ++ "x"
  IO.println s!"cow {a} {b} {c} {d} {rep (5 + k)} {a.length} {b.length}"
  -- many results kept alive at once, then dropped
  let arr := (List.range 300).toArray.map (fun i => rep ((i + k) % 130))
  IO.println s!"arr {arr.size} {arr[0]!} {arr[127]!} {arr[128]!} {arr[129]!} {arr.foldl (fun n s => n + s.length) 0}"
  let mut acc := ""
  for i in [0:2000] do
    acc := acc ++ rep ((i + k) % 10)
  IO.println s!"acc {acc.length} {acc.take 25 |>.copy}"
  -- dbgTraceIfShared: the table's string is shared, a fresh result is exclusive
  let e := dbgTraceIfShared "small" (rep (3 + k))
  let f := dbgTraceIfShared "large" (rep (300 + k))
  IO.println s!"traced {e} {f}"
