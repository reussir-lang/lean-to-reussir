/-! Runtime test: allocations of the shapes optimization `flatten-structs`
splits (with `RtFlattenAlloc.alloc`, `alloc-check.sh`: lean2rr's
allocations grow no faster than native's). Each mode runs n steps:
- `loop6`: a `for` loop in `IO` with six variables (a nested `Prod` state,
  returned in `EST.Out.ok` at the end);
- `adler`: an Adler-32 fold over a `ByteArray` (`Nat × Nat` state);
- `helper`: the same fold through a step function that is not inlined
  (lean-zip's `updateByte`): the loop passes its split state to the
  helper's split parameter, and the helper returns a tuple;
- `monad`: hand-written state and exception transformers, each step a call
  returning `Except String Nat × Array Nat`;
- `interp`: an interpreter step in `ReaderT Nat (ExceptT String (StateT
  Nat IO))`, each step a call returning `EST.Out (Except String Nat × Nat)`;
- `bucket`: an inner loop over short lists (most of them empty) run once
  per element of an outer loop, its state passed on unchanged, rebuilt at
  its exit only after a step (never per run of the inner loop). -/

set_option linter.unusedVariables false

@[noinline] def loop6 (n : Nat) : IO Nat := do
  let mut a := 0
  let mut b := 0
  let mut c := 0
  let mut d := 0
  let mut e := 0
  let mut f := 0
  for i in [0:n] do
    a := a + 1
    b := b + i % 7
    if i % 3 == 0 then c := c + 1
    d := max d (i % 11)
    e := (e + i) % 1000003
    f := f ^^^ i
  return a + b + c + d + e + f

@[noinline] def adler (data : ByteArray) : Nat :=
  let (a, b) := data.data.foldl (fun (s : Nat × Nat) (x : UInt8) =>
    let a := (s.1 + x.toNat) % 65521
    (a, (s.2 + a) % 65521)) (1, 0)
  b * 65536 + a

@[noinline] def adlerByte (s : Nat × Nat) (x : UInt8) : Nat × Nat :=
  let a := (s.1 + x.toNat) % 65521
  (a, (s.2 + a) % 65521)

@[noinline] def adlerHelper (data : ByteArray) : Nat :=
  let (a, b) := data.data.foldl adlerByte (1, 0)
  b * 65536 + a

def StateT' (σ : Type) (α : Type) := σ → (α × σ)
def ExceptT' (ε : Type) (α : Type) := StateT' (Array Nat) (Except ε α)

@[noinline] def mstep (k : Nat) : ExceptT' String Nat := fun s =>
  if k % 1000 == 999 then (.error s!"step {k}", s) else (.ok (k % 13), s.set! (k % s.size) k)

@[noinline] def mloop : Nat → Nat → ExceptT' String Nat
  | 0, acc => fun s => (.ok acc, s)
  | k + 1, acc => fun s =>
    match mstep k s with
    | (.ok v, s') => mloop k (acc + v) s'
    | (.error e, s') => mloop k (acc + 1) s'

abbrev M := ReaderT Nat (ExceptT String (StateT Nat IO))

@[noinline] def istep (k : Nat) : M Nat := do
  let lim ← read
  modify (· + 1)
  if k > lim then throw s!"over {k}"
  return k % 17

@[noinline] def iloop : Nat → Nat → M Nat
  | 0, acc => pure acc
  | k + 1, acc => do
    let v ← tryCatch (istep k) fun _ => pure 0
    iloop k (acc + v)

structure Best where
  key : Nat
  score : Nat
  hits : Nat

@[noinline] def scanBucket : List (Nat × Nat) → Best → Best
  | [], b => b
  | (k, s) :: rest, b =>
    if s > b.score then scanBucket rest { key := k, score := s, hits := b.hits + 1 }
    else scanBucket rest { key := b.key, score := b.score, hits := b.hits }

@[noinline] def scanAll (buckets : Array (List (Nat × Nat))) : Best := Id.run do
  let mut best : Best := { key := 0, score := 0, hits := 0 }
  for bucket in buckets do
    best := scanBucket bucket best
  return best

def main (args : List String) : IO Unit := do
  let mode := args.head?.getD "loop6"
  let n := (args.tail.head? >>= String.toNat?).getD 1000
  match mode with
  | "loop6" => IO.println s!"loop6 {← loop6 n}"
  | "adler" =>
    let data := ByteArray.mk ((List.range n).toArray.map fun i => UInt8.ofNat (i * 7 + 3))
    IO.println s!"adler {adler data}"
  | "helper" =>
    let data := ByteArray.mk ((List.range n).toArray.map fun i => UInt8.ofNat (i * 7 + 3))
    IO.println s!"helper {adlerHelper data}"
  | "monad" =>
    let (r, s) := mloop n 0 (Array.replicate 64 0)
    IO.println s!"monad {match r with | .ok v => toString v | .error e => e} {s.foldl (· + ·) 0}"
  | "interp" =>
    let (r, s) ← (iloop n 0).run (n / 2) |>.run 0
    IO.println s!"interp {match r with | .ok v => toString v | .error e => e} {s}"
  | "bucket" =>
    let buckets := (List.range n).toArray.map fun i =>
      if i % 4 != 0 then [] else [(i, i * 37 % 101)]
    let b := scanAll buckets
    IO.println s!"bucket key={b.key} score={b.score} hits={b.hits}"
  | _ => IO.println "mode?"
