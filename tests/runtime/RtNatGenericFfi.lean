/-! Runtime test: `Nat` and `Int` values where the runtime holds them
through its generic functions: computed constants (a once-cell each),
`dbgTraceIfShared` at `Nat` (a polymorphic extern whose `α` is `Nat`),
references, thunks and tasks of `Nat`, and arrays of `Nat` and `Int`
(typed arrays: `RVec<Nat>`; the runtime's FFI
functions hold Reussir's owned handles at `Nat`/`Int`, Reussir's patch
R2: `isFfiTypeArgTy`). Small and big values, each released and
shared. -/

@[noinline] def grow (n : Nat) : Nat := n * n + 1

/-- Computed constants (not literals): a once-cell each. -/
def cSmall : Nat := grow 1000
def cBig : Nat := grow (2 ^ 70)
def cMid : Nat := grow 2147483648
def cNeg : Int := -((grow (2 ^ 65) : Nat) : Int)
def cPair : Nat × Int := (grow 3, -(grow (2 ^ 64) : Int))

def main (args : List String) : IO Unit := do
  let k := args.length
  IO.println s!"constants {cSmall} {cBig} {cMid} {cNeg} {cPair.1} {cPair.2}"
  IO.println s!"again {cSmall + k} {cBig + k} {cMid % 1000} {cNeg / 7} {cPair.2 % 1000}"
  -- `dbgTraceIfShared` at `Nat`: a small value (a scalar natively) and a
  -- unique big one are not reported.
  let s := dbgTraceIfShared "small" (k + 5)
  let b := dbgTraceIfShared "big" (grow (2 ^ 80 + k))
  IO.println s!"traced {s} {b % 1000003}"
  -- Arrays of `Nat` and `Int`: built, updated in place and shared.
  let mut xs : Array Nat := #[]
  for i in [0:40] do
    xs := xs.push (if i % 3 == 0 then 2 ^ (60 + i) + i else i * i)
  let ys := xs
  xs := xs.set! 5 (2 ^ 100)
  xs := xs.modify 6 (· + 2 ^ 64)
  IO.println s!"xs {xs.size} {xs[5]!} {xs[6]!} {ys[5]!} {ys[6]!} sum {xs.foldl (· + ·) 0} {ys.foldl (· + ·) 0}"
  let zs := xs.map (· * 3)
  IO.println s!"zs {zs[0]!} {zs[39]!} {(zs.qsort (· > ·))[0]!} {zs.contains (2 ^ 100 * 3)} {xs.reverse[0]!}"
  let is : Array Int := xs.map (fun (n : Nat) => (n : Int) - 2 ^ 62)
  IO.println s!"is {is[0]!} {is[3]!} {is[5]!} {is.foldl (· + ·) 0} {(is.filter (· < 0)).size}"
  let nested : Array (Array Nat) := #[xs, ys, #[k, 2 ^ 70]]
  IO.println s!"nested {nested[2]![1]!} {nested[0]![5]!} {(nested.map (·.size)).toList}"
  let popped := xs.pop
  IO.println s!"popped {popped.size} {popped.back!} {xs.back!}"
  -- References, thunks and tasks of `Nat`.
  let r ← IO.mkRef (2 ^ 90 + k)
  r.modify (· + 1)
  let old ← r.swap (k + 1)
  IO.println s!"ref {old} {← r.get}"
  let t : Thunk Nat := Thunk.mk fun _ => grow (2 ^ 66 + k)
  IO.println s!"thunk {t.get} {t.get % 7}"
  let task := Task.spawn fun _ => grow (2 ^ 67 + k)
  IO.println s!"task {task.get % 1000000007}"
  let it : Thunk Int := Thunk.mk fun _ => -(grow (2 ^ 68) : Int)
  IO.println s!"int thunk {it.get}"
