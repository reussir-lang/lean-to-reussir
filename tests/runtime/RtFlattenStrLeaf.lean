/-! Runtime test: `String` fields of two-constructor results (optimization
`flatten-structs`). The fields of the constructor a value does not have are
placeholders; a `String` field of the error constructor of `Except`,
`EST.Out` or `EStateM.Result` is passed boxed, so that its placeholder on
the success path is `box(0)` (no count), and a real message goes into the
box and comes out of it where the program reads it; the `String` fields of
other constructors stay at their type. The outputs must equal native's for:
- a recursive search returning `Except String Nat × Array Nat` (the
  shape of Unionfind's `findEntryAux`): errors at several depths, from a
  literal and from a computed string, and results passed up unchanged;
- `EStateM String Nat` with errors thrown, caught and passed on, and
  `Except (String × Nat) Nat` (a `String` in a structure of the error);
- `Option String` results, read and changed after they come back (a push
  on the unique string, a comparison, the length, stored in an array);
- an inductive of two constructors with `String` fields at their own
  layout (not boxed in its record): `ok (n : Nat) (tag : String)`,
  `bad (msg : String)`;
- `Except String (String × Nat)` (a `String` in a structure in each
  constructor) and `Except String String` (the constructors share their
  field: not boxed);
- `IO String` results with errors raised and caught;
- a loop whose state is `Option String`;
- `Except String (Except String Nat)` (an error at each level, passed up
  or changed);
- `ExceptT String (StateT Nat IO)` with `throwThe` and `tryCatchThe`;
- `EStateM` with a structure error that holds a `String` (`Err`), and with
  an error type of two constructors (`MyErr`: one with a `String`, one
  without);
- `Except Err Nat` errors changed and passed up; a loop whose state is
  `Except String Nat`;
- `Except String Nat` values stored in an `Array` and an `Option`;
- results of pure tasks (`Task.spawn`), `IO.userError`s thrown and caught
  (with `finally`), `EIO String` through `toBaseIO`, and an `IO.asTask`
  whose action throws. -/

@[noinline] def findRoot : Nat → Nat → Array Nat → Except String Nat × Array Nat
  | 0, _, s => (.error "out of fuel", s)
  | i + 1, n, s =>
    if h : n < s.size then
      let p := s[n]
      if p == n then (.ok n, s)
      else match findRoot i p s with
        | (.ok r, s) => (.ok r, s.set! n r)
        | (.error e, s) => (.error (if e.length > 30 then e else s!"{e}/{n}"), s)
    else (.error s!"invalid node {n}", s)

@[noinline] def rootsLoop (k : Nat) : Nat → Nat → Array Nat → Except String Nat × Array Nat
  | 0, acc, s => match findRoot k (k + 3) s with
    | (.ok r, s') => (.ok (acc + r), s')
    | (.error e, s') => (.error s!"{e} after {acc}", s')
  | j + 1, acc, s =>
    let i := k - (j + 1)
    match findRoot (if i == 70 then 2 else k) i s with
    | (.ok r, s') => rootsLoop k j (acc + r) s'
    | (.error e, s') => (.error s!"{e} at {i}", s')

@[noinline] def roots (k : Nat) : Except String Nat × Array Nat :=
  rootsLoop k k 0 ((Array.range k).map fun i => if i == 0 then 0 else i / 2)

@[noinline] def estep (k : Nat) : EStateM String Nat Nat := do
  modify (· + k)
  if k % 4 == 3 then throw s!"estep {k} at {← get}"
  pure (k * 2)

@[noinline] def eloop : Nat → Nat → EStateM String Nat Nat
  | 0, acc => pure acc
  | j + 1, acc => do
    let v ← tryCatch (estep j) fun e => if e.length > 14 then throw (e ++ "!") else pure 1
    eloop j (acc + v)

@[noinline] def epair (k : Nat) : Except (String × Nat) Nat :=
  if k % 5 == 4 then .error (s!"epair {k}", k) else .ok (k + 100)

@[noinline] def pick (k : Nat) : Option String :=
  if k % 3 == 0 then none else some s!"v{k}"

@[noinline] def pickLit (k : Nat) : Option String :=
  if k % 4 == 1 then some "lit" else none

inductive Res where
  | ok (n : Nat) (tag : String)
  | bad (msg : String)

@[noinline] def classify (k : Nat) : Res :=
  if k % 5 == 0 then .bad s!"five {k}" else .ok (k * 2) (if k % 2 == 0 then "even" else s!"odd{k}")

@[noinline] def pair (k : Nat) : Except String (String × Nat) :=
  if k % 6 == 5 then .error s!"pair {k}" else .ok (s!"p{k}", k + 1)

@[noinline] def same (k : Nat) : Except String String :=
  if k % 2 == 0 then .error s!"e{k}" else .ok s!"o{k}"

@[noinline] def ioStr (k : Nat) : IO String := do
  if k % 4 == 3 then throw (IO.userError s!"io {k}")
  pure s!"io-ok {k}"

@[noinline] def lastSome (n : Nat) : Option String := Id.run do
  let mut cur : Option String := none
  for k in [0:n] do
    if k == 50 then break
    match pick k with
    | some s => cur := some (s ++ "!")
    | none => pure ()
  return cur

structure Err where
  msg : String
  code : Nat

inductive MyErr where
  | bad (s : String) (n : Nat)
  | worse (n : Nat)

@[noinline] def nested (k : Nat) : Except String (Except String Nat) :=
  if k % 3 == 0 then .error s!"outer {k}"
  else if k % 3 == 1 then .ok (.error s!"inner {k}")
  else .ok (.ok (k * 7))

@[noinline] def nestedLoop : Nat → Nat → Except String (Except String Nat)
  | 0, acc => .ok (.ok acc)
  | j+1, acc => match nested (j + acc % 5) with
    | .error e => if j % 7 == 0 then .error (e ++ "!") else nestedLoop j (acc + e.length)
    | .ok (.error e) => if j % 11 == 0 then .ok (.error e) else nestedLoop j (acc + 2 * e.length)
    | .ok (.ok v) => nestedLoop j (acc + v)

abbrev M := ExceptT String (StateT Nat IO)

@[noinline] def stepM (k : Nat) : M Nat := do
  modify (· + k)
  let s ← get
  if s % 13 == 5 then throwThe String s!"stepM {k} at {s}"
  pure (s * 2)

@[noinline] def loopM : Nat → Nat → M Nat
  | 0, acc => pure acc
  | j+1, acc => do
    let v ← tryCatchThe String (stepM j) fun e => if e.length > 16 then throwThe String (e ++ "?") else pure e.length
    loopM j (acc + v)

@[noinline] def estruct (k : Nat) : EStateM Err String Nat := do
  modify (· ++ s!"{k},")
  if k % 5 == 3 then throw ({ msg := s!"estruct {k} {(← get).length}", code := k } : Err)
  pure (k + 1)

@[noinline] def eloopS : Nat → Nat → EStateM Err String Nat
  | 0, acc => pure acc
  | j+1, acc => do
    let v ← tryCatch (estruct j) fun e => if e.code > 10 then throw ({ e with msg := e.msg ++ "#" } : Err) else pure e.msg.length
    eloopS j (acc + v)

@[noinline] def emy (k : Nat) : EStateM MyErr Nat String := do
  modify (· + k)
  if k % 4 == 1 then throw (MyErr.bad s!"emy {k}" k)
  if k % 4 == 2 then throw (MyErr.worse k)
  pure s!"r{k}"

@[noinline] def emyLoop : Nat → String → EStateM MyErr Nat String
  | 0, acc => pure acc
  | j+1, acc => do
    let r ← tryCatch (emy j) fun
      | .bad s n => if n > 20 then throw (MyErr.bad (s ++ "+") n) else pure s
      | .worse n => pure s!"w{n}"
    emyLoop j (acc ++ r.take 3)

@[noinline] def eErr (k : Nat) : Except Err Nat :=
  if k % 6 == 1 then .error { msg := s!"err{k}", code := k } else .ok (k * 3)

@[noinline] def eErrLoop : Nat → Nat → Except Err Nat
  | 0, acc => .ok acc
  | j+1, acc => match eErr j with
    | .error e => if e.code > 30 then .error { e with msg := e.msg.toUpper } else eErrLoop j (acc + e.msg.length)
    | .ok v => eErrLoop j (acc + v)

@[noinline] def firstErr (n : Nat) : Except String Nat := Id.run do
  let mut st : Except String Nat := .ok 0
  for k in [0:n] do
    match st with
    | .ok v => st := if k % 9 == 8 then .error s!"at {k} {v}" else .ok (v + k)
    | .error e => if k % 10 == 0 then st := .error (e ++ ".") else pure ()
  return st

@[noinline] def collect (n : Nat) : Array (Except String Nat) × Option (Except String Nat) := Id.run do
  let mut arr := #[]
  let mut last := none
  for k in [0:n] do
    let r : Except String Nat := if k % 4 == 0 then .error s!"c{k}" else .ok k
    arr := arr.push r
    if k % 5 == 0 then last := some r
  return (arr, last)

@[noinline] def taskWork (k : Nat) : Except String Nat :=
  if k % 3 == 0 then .error s!"task {k}" else .ok (k * k)

def showE : Except String Nat → String
  | .ok v => s!"ok {v}"
  | .error e => s!"error {e} {e == "c0"} {e.length}"

@[noinline] def ioThrow (k : Nat) : IO Nat := do
  if k % 3 == 1 then throw (IO.userError s!"io {k}")
  pure k

@[noinline] def eioStr (k : Nat) : EIO String Nat := do
  if k % 3 == 2 then throw s!"eio {k}"
  pure (k + 100)

def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 200
  let (r, arr) := roots n
  IO.println s!"roots {match r with | .ok v => toString v | .error e => e} {arr.toList.take 12}"
  let (r2, _) := roots 1
  IO.println s!"roots1 {match r2 with | .ok v => toString v | .error e => e}"
  for m in [3, 12, 40] do
    match (eloop m 0).run 0 with
    | .ok v st => IO.println s!"eloop {m}: ok {v} {st}"
    | .error e st => IO.println s!"eloop {m}: error {e} {st}"
  IO.println s!"epair {(List.range 12).map fun k => match epair k with | .ok v => s!"{v}" | .error (e, n) => s!"{e}/{n}"}"
  let mut store : Array String := #[]
  let mut total := 0
  for k in [0:n] do
    match pick k with
    | some s =>
      let t := s.push '#'
      total := total + t.length
      if k % 17 == 1 then store := store.push t
    | none => total := total + 1
    match pickLit k with
    | some s => if s == "lit" then total := total + 100 else total := total + 1000
    | none => pure ()
  IO.println s!"pick {total} {store}"
  let mut c := (0, 0, "")
  for k in [0:n] do
    match classify k with
    | .ok m tag => c := (c.1 + m + tag.length, c.2.1, if k == 13 then tag else c.2.2)
    | .bad msg => c := (c.1, c.2.1 + msg.length, c.2.2)
  IO.println s!"classify {c}"
  let ps := (List.range 12).map fun k => match pair k with
    | .ok (s, m) => s!"{s}:{m}"
    | .error e => e.toUpper
  IO.println s!"pair {ps}"
  let ss := (List.range 6).map fun k => match same k with
    | .ok s => s.length
    | .error e => e.length * 10
  IO.println s!"same {ss}"
  let mut io := #[]
  for k in [0:8] do
    try io := io.push (← ioStr k)
    catch e => io := io.push s!"caught {e}"
  IO.println s!"io {io}"
  IO.println s!"lastSome {lastSome n} {lastSome 2} {lastSome 0}"
  IO.println s!"nested {(List.range 6).map fun k => match nested k with | .error e => e | .ok (.error e) => "i:" ++ e | .ok (.ok v) => toString v}"
  for m in [5, 20, n] do
    match nestedLoop m 1 with
    | .error e => IO.println s!"nestedLoop {m}: E {e}"
    | .ok (.error e) => IO.println s!"nestedLoop {m}: IE {e}"
    | .ok (.ok v) => IO.println s!"nestedLoop {m}: {v}"
  for m in [3, 10, n] do
    let (r, s) ← (loopM m 0).run.run 1
    IO.println s!"loopM {m}: {match r with | .ok v => toString v | .error e => e} {s}"
  for m in [4, 12, n] do
    match (eloopS m 0).run "" with
    | .ok v s => IO.println s!"eloopS {m}: ok {v} {s.length}"
    | .error e s => IO.println s!"eloopS {m}: error {e.msg} {e.code} {s.length}"
  for m in [3, 9, n] do
    match (emyLoop m "").run 0 with
    | .ok v s => IO.println s!"emyLoop {m}: ok {v} {s}"
    | .error (.bad e k) s => IO.println s!"emyLoop {m}: bad {e} {k} {s}"
    | .error (.worse k) s => IO.println s!"emyLoop {m}: worse {k} {s}"
  for m in [5, 40, n] do
    match eErrLoop m 0 with
    | .ok v => IO.println s!"eErrLoop {m}: ok {v}"
    | .error e => IO.println s!"eErrLoop {m}: error {e.msg} {e.code}"
  IO.println s!"firstErr {showE (firstErr 5)} {showE (firstErr n)}"
  let (arr, last) := collect n
  IO.println s!"collect {arr.size} {(arr.toList.take 6).map showE} {last.map showE}"
  let tasks := (List.range 6).map fun k => Task.spawn fun _ => taskWork (k + n)
  IO.println s!"tasks {tasks.map fun t => showE t.get}"
  let mut acc := #[]
  for k in [0:6] do
    try
      let v ← ioThrow k
      acc := acc.push s!"v{v}"
    catch e =>
      acc := acc.push s!"c:{e}"
    finally
      IO.println s!"finally {k}"
  IO.println s!"io {acc}"
  let mut acc2 := #[]
  for k in [0:6] do
    match ← (eioStr k).toBaseIO with
    | .ok v => acc2 := acc2.push s!"{v}"
    | .error e => acc2 := acc2.push e
  IO.println s!"eio {acc2}"
  let t ← IO.asTask (do let v ← ioThrow (n + 1); pure (v + 1))
  match t.get with
  | .ok v => IO.println s!"asTask ok {v}"
  | .error e => IO.println s!"asTask error {e}"
