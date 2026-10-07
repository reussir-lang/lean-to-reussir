/-! Runtime test: IO results of every scalar kind passed through generic
monadic code (the result of an IO action has a type parameter, so a
`UInt64`, `Float`, `Char` or `Bool` result is stored where its type is not
known): `List.mapM`, `Array.foldlM`, `forM`, `StateT Float IO`,
`ExceptT UInt64 IO` (an error payload of 2^64 − 1), `EStateM` with a
`Float` state, `EIO UInt64 Float`, `IO.asTask` and `IO.wait` of a `Float`,
`BaseIO` actions; `initialize` values of generic types (a reference to a
`Float`, a `UInt64` above 2^63, a pair, an array of functions, an `Array Float`); and
the exit code of `main : IO UInt32`, computed through a generic monad
stack (natively 3). -/

initialize gFloat : IO.Ref Float ← IO.mkRef 2.5
initialize gBig : UInt64 ← pure 18446744073709551615
initialize gPair : Nat × Float ← pure (2 ^ 64, -0.0)
initialize gFns : Array (Nat → Nat) ← pure #[(· * 7), (· + 1)]
initialize gArr : Array Float ← pure #[1.5, Float.ofBits 1]

@[noinline] def readF (r : IO.Ref Float) : IO Float := r.get
@[noinline] def bigU : IO UInt64 := pure 18446744073709551614
@[noinline] def charIO (n : Nat) : BaseIO Char := pure (Char.ofNat (0x10FFFF - n))
@[noinline] def boolIO (n : Nat) : IO Bool := pure (n % 2 == 0)
@[noinline] def u8IO (n : Nat) : IO UInt8 := pure (n * 100).toUInt8

/-- Generic: runs the actions and collects their results. -/
@[noinline] def seqAll {m : Type → Type} [Monad m] {α : Type} (xs : List (m α)) : m (List α) := xs.mapM id

@[noinline] def sumF (xs : Array Float) : StateT Float IO Unit :=
  xs.forM fun x => modify (· + x)

@[noinline] def failing (n : Nat) : ExceptT UInt64 IO Float := do
  if n > 2 then throw 18446744073709551615
  return n.toFloat * 1.5

@[noinline] def stepE : EStateM String Float UInt64 := do
  modify (· * 2.5)
  let s ← get
  if s > 100 then throw s!"big {s}"
  return s.toUInt64 + 18446744073709551000

@[noinline] def eio (b : Bool) : EIO UInt64 Float :=
  if b then throw 9223372036854775808 else pure (-0.0)

/-- The exit code, through `ReaderT` and `StateT` over `IO`. -/
@[noinline] def exitCode : ReaderT UInt32 (StateT UInt32 IO) UInt32 := do
  let base ← read
  modify (· + base)
  let s ← get
  return s % 5

def main : IO UInt32 := do
  let fs ← seqAll [readF gFloat, pure (Float.ofBits 1), pure (-0.0)]
  IO.println s!"floats {fs.map Float.toBits}"
  let us ← seqAll [bigU, pure gBig, pure 9223372036854775808]
  IO.println s!"u64 {us}"
  let cs ← (List.range 3).mapM fun i => (charIO i : IO Char)
  IO.println s!"chars {cs.map Char.toNat}"
  let bs ← (List.range 3).mapM boolIO
  let u8s ← (List.range 4).mapM u8IO
  IO.println s!"bools {bs} u8 {u8s}"
  let total ← #[1, 2, 3].foldlM (fun (acc : UInt64) i => do return acc + (← bigU) + i) 0
  IO.println s!"foldlM {total}"
  let ((), s) ← (sumF #[0.5, 0.25, -0.0]).run 1.0
  IO.println s!"stateT {s} {s.toBits}"
  for n in [1, 3] do
    match ← (failing n).run with
    | .ok f => IO.println s!"exceptT ok {f}"
    | .error e => IO.println s!"exceptT error {e}"
  match stepE.run 4.0 with
  | .ok v st => IO.println s!"estate ok {v} {st}"
  | .error e st => IO.println s!"estate error {e} {st}"
  match stepE.run 50.0 with
  | .ok v st => IO.println s!"estate ok {v} {st}"
  | .error e st => IO.println s!"estate error {e} {st}"
  for b in [true, false] do
    match ← (eio b).toBaseIO with
    | .ok f => IO.println s!"eio ok {f.toBits}"
    | .error e => IO.println s!"eio error {e}"
  let t ← IO.asTask (pure (Float.ofBits 0x7fefffffffffffff))
  match ← IO.wait t with
  | .ok f => IO.println s!"task {f.toBits}"
  | .error e => IO.println s!"task error {e}"
  gFloat.modify (· * 4)
  IO.println s!"init {← gFloat.get} {gBig} {gPair.1} {gPair.2.toBits} {gFns.map (· 6)} {gArr.map Float.toBits}"
  let (code, st) ← (exitCode.run 3).run 5
  IO.println s!"exit {code} {st}"
  return code
