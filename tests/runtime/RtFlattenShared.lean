/-! Runtime test: optimization `flatten-structs` never rebuilds an object
the program shares or inspects (review of the pass, findings 1-3). Without
arguments it prints identities and traces; with a mode (`find`, `store`,
`fn`) and n it makes n calls, for `RtFlattenShared.alloc` (no allocation per
call where native makes none):
- `find`: a loop whose exit goes through a join point that one jump gives
  the loop's parameter unchanged; with no step the result is the caller's
  pair itself (natively `same=true`), never a copy;
- `store`: a loop that returns its parameter unchanged on an empty list,
  whose result another declaration reads field by field, stored whole by a
  caller: the caller's object, not a copy per call;
- `fn`: a function returning a matched (shared) pair inside an `Option`,
  read field by field by one caller and called through a function value
  (its wrapper) by another: the pair is shared, not copied;
- `dbgTraceIfShared` of a value built in two branches and read again
  afterwards: shared natively (the message is printed), so it is never
  replaced by a fresh copy;
- a shared object one level below a rebuilt one (re-review): `inner` (a
  loop that passes its state's inner pair on unchanged), `elems` (a join
  point fed by fresh pairs holding a matched array element, stored at every
  step), `opt` (a result whose inner level is a matched value, read field by
  field by one caller and stored whole by another): the inner object is
  shared, not copied. -/

@[noinline] partial def find (s : Nat × Nat) (n : Nat) : Nat × Nat :=
  let t := if n % 3 == 1 then (s.1 + 1, s.2) else s
  if n == 0 then t else find t (n - 1)

@[noinline] def useTwice (n : Nat) : Nat :=
  let p := if n % 2 == 0 then (n, n + 1) else (n + 1, n)
  let q := dbgTraceIfShared "p shared" p
  q.1 + p.2

structure Best where
  key : Nat
  score : Nat
  hits : Nat

@[noinline] def scanBucket : List (Nat × Nat) → Best → Best
  | [], b => b
  | (k, s) :: rest, b =>
    if s > b.score then scanBucket rest { key := k, score := s, hits := b.hits + 1 }
    else scanBucket rest b

@[noinline] def bestScore (xs : List (Nat × Nat)) : Nat := (scanBucket xs ⟨0, 0, 0⟩).score

@[noinline] def storeAll (b0 : Best) (n : Nat) : Array Best := Id.run do
  let mut out := Array.mkEmpty n
  for i in [0:n] do
    out := out.push (scanBucket (if i % 1000 == 999 then [(i, 5)] else []) b0)
  return out

@[noinline] def findAll (p : Nat × Nat) (n : Nat) : Array (Nat × Nat) := Id.run do
  let mut out := Array.mkEmpty n
  for _ in [0:n] do
    out := out.push (find p 0)
  return out

@[noinline] def pick (xs : List (Nat × Nat)) : Option (Nat × Nat) :=
  let p := xs.headD (0, 0)
  match p with
  | (a, b) => if a < b then some p else none

@[noinline] def pickSum (xs : List (Nat × Nat)) : Nat :=
  match pick xs with
  | some (a, b) => a + b
  | none => 0

@[noinline] def callAll (f : List (Nat × Nat) → Option (Nat × Nat)) (xs : List (Nat × Nat)) (n : Nat) :
    Array (Option (Nat × Nat)) := Id.run do
  let mut out := Array.mkEmpty n
  for _ in [0:n] do
    out := out.push (f xs)
  return out

@[noinline] def viaFn (f : List (Nat × Nat) → Option (Nat × Nat)) (xs : List (Nat × Nat)) : Option (Nat × Nat) :=
  f xs

@[noinline] def countUp2 (s : (Nat × Nat) × Nat) (k : Nat) : (Nat × Nat) × Nat :=
  match k with
  | 0 => s
  | k + 1 => countUp2 (s.1, s.2 + 1) k

@[noinline] def storeQ (xs : Array (Nat × Nat)) (n : Nat) : Array ((Nat × Nat) × Nat) := Id.run do
  let mut out := Array.mkEmpty n
  for i in [0:n] do
    let q := xs[i % xs.size]!
    match q with
    | (a, _) =>
      let p := if a % 2 == i % 2 then (q, 1) else (q, 2)
      out := out.push p
  return out

@[noinline] def wrapQ (xs : List (Nat × Nat)) (k : Nat) : Option ((Nat × Nat) × Nat) :=
  let q := xs.headD (0, 0)
  match q with
  | (a, _) => if a < 1000000 then some (q, k) else none

@[noinline] def readQ (xs : List (Nat × Nat)) : Nat :=
  match wrapQ xs 3 with
  | some ((a, b), c) => a + b + c
  | none => 0

@[noinline] def storeW (xs : List (Nat × Nat)) (n : Nat) : Array (Option ((Nat × Nat) × Nat)) := Id.run do
  let mut out := Array.mkEmpty n
  for i in [0:n] do
    out := out.push (wrapQ xs i)
  return out

unsafe def main (args : List String) : IO Unit := do
  match args with
  | [mode, k] =>
    let n := k.toNat!
    if mode == "store" then
      let out := storeAll ⟨n, 1, 0⟩ n
      IO.println s!"{out.size} {bestScore [(1, 2), (3, 4)]} {out.foldl (fun a b => a + b.hits) 0}"
    else if mode == "find" then
      let out := findAll (n, n + 1) n
      IO.println s!"{out.size} {out.foldl (fun a b => a + b.1) 0}"
    else if mode == "inner" then
      let s0 : (Nat × Nat) × Nat := ((n, n + 1), 0)
      let mut t := 0
      for _ in [0:n] do
        t := t + (countUp2 s0 1).2
      IO.println s!"{t}"
    else if mode == "elems" then
      let out := storeQ #[(1, 2), (3, 4), (6, 5)] n
      IO.println s!"{out.size} {out.foldl (fun a p => a + p.2) 0}"
    else if mode == "opt" then
      let out := storeW [(n, 1)] n
      IO.println s!"{out.size} {readQ [(2, 3)]}"
    else
      let xs := [(n, n + 1), (2, 3)]
      let out := callAll pick xs n
      IO.println s!"{out.size} {pickSum xs} {out.foldl (fun a o => a + (o.map (·.1)).getD 0) 0}"
  | _ =>
    for n in [0, 4] do
      let s0 : Nat × Nat := (n + 5, n + 6)
      let r := find s0 n
      IO.println s!"find {r} same={ptrAddrUnsafe r == ptrAddrUnsafe s0}"
    IO.println s!"useTwice {useTwice 4}"
    let xs := [(5, 6), (2, 3)]
    let r := viaFn pick xs
    IO.println s!"viaFn {r} {pickSum xs} same={match r with | some q => ptrAddrUnsafe q == ptrAddrUnsafe xs.head! | none => false}"
    let b0 : Best := ⟨7, 1, 0⟩
    let b1 := scanBucket [] b0
    IO.println s!"scanBucket {b1.key} {bestScore [(1, 2)]} same={ptrAddrUnsafe b0 == ptrAddrUnsafe b1}"
    let s0 : (Nat × Nat) × Nat := ((7, 8), 0)
    let r := countUp2 s0 3
    IO.println s!"inner {r} sameInner={ptrAddrUnsafe r.1 == ptrAddrUnsafe s0.1}"
    let zs := #[(1, 2), (3, 4)]
    let out := storeQ zs 2
    IO.println s!"elems {out} sameInner={ptrAddrUnsafe out[0]!.1 == ptrAddrUnsafe zs[0]!}"
    let ys := [(5, 6)]
    let w := (storeW ys 1)[0]!
    IO.println s!"opt {w} {readQ ys} sameInner={match w with | some (q, _) => ptrAddrUnsafe q == ptrAddrUnsafe ys.head! | none => false}"
