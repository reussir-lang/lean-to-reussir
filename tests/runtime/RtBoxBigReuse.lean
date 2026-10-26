/-! Runtime test (memory): big `Nat` and `Int` values boxed and taken apart
in a loop: each iteration boxes a big `Nat` three times in a list (one
value twice, as shared boxes), a big `Int` twice in a list made by a
function that is not inlined (`listI`; a list's head is a box, where an
`Option Int` is a flat value and Lean's compiler removes an option taken
apart at once), takes the `Int`s out and uses them, maps the `Nat` list
(unboxed, computed, boxed again), sums and drops it all. A big value's box is a leanrt
cell that takes the owned rcgmp handle (`l2r_any_of_big`): a box
that kept one reference too many would keep every value alive, so the
peak memory, flat natively, would grow with the count
(tests/runtime/alloc-check.sh, RtBoxBigReuse.alloc). Argument: count
(default 1000). -/

@[noinline] def big (k : Nat) : Nat := 2^64 + k
@[noinline] def bigI (k : Nat) : Int := -(2^64 : Int) - k
@[noinline] def listI (k : Nat) : List Int := let v := bigI k; [v, v - 1]

def loop (n : Nat) : Nat := Id.run do
  let mut acc := 0
  for i in [0:n] do
    let x := big i
    let l := [x, x, x * 2 + 1]
    let y := (listI i).foldl (fun a v => a + v.natAbs) 0
    let l2 := l.map (· + y % 3)
    acc := (acc + l2.foldl (· + ·) 0) % 1000000007
  return acc

def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 1000
  IO.println s!"loop {n}: {loop n}"
