/-! Runtime test: functions whose result is a structure (optimization
`flatten-structs`): a function that builds its structure result at every
return, and whose callers read it field by field, returns the fields as a
`[value]` tuple. The outputs must equal native's in every shape:
- hand-written state and exception transformers (`Except ε α × σ`, the
  shape of the classic Unionfind), with errors raised and caught, and an
  error arm that returns the callee's result of another type unchanged;
- a result read field by field by one caller and stored whole by another
  (the second rebuilds it);
- mutual recursion returning pairs; a non-tail recursion returning pairs;
- a nested structure result; scalar fields (`UInt64`, `Float`, `Bool`);
- a function used as a function value (through its wrapper);
- a result with a function-typed field (not split: kept whole);
- `ptrEq` of a result with an argument it may return unchanged. -/

set_option linter.unusedVariables false

def StateT' (m : Type → Type) (σ : Type) (α : Type) := σ → m (α × σ)
namespace StateT'
variable {m : Type → Type} [Monad m] {σ : Type} {α β : Type}
@[inline] protected def pure (a : α) : StateT' m σ α := fun s => pure (a, s)
@[inline] protected def bind (x : StateT' m σ α) (f : α → StateT' m σ β) : StateT' m σ β :=
  fun s => do let (a, s') ← x s; f a s'
@[inline] def read : StateT' m σ σ := fun s => pure (s, s)
@[inline] def updt (f : σ → σ) : StateT' m σ Unit := fun s => pure ((), f s)
instance : Monad (StateT' m σ) := { pure := @StateT'.pure _ _ _, bind := @StateT'.bind _ _ _ }
end StateT'

def ExceptT' (m : Type → Type) (ε : Type) (α : Type) := m (Except ε α)
namespace ExceptT'
variable {m : Type → Type} [Monad m] {ε : Type} {α β : Type}
@[inline] protected def pure (a : α) : ExceptT' m ε α := (pure (Except.ok a) : m (Except ε α))
@[inline] protected def bind (x : ExceptT' m ε α) (f : α → ExceptT' m ε β) : ExceptT' m ε β :=
  (do let v ← x; match v with
      | Except.error e => pure (Except.error e)
      | Except.ok a => f a : m (Except ε β))
@[inline] def error (e : ε) : ExceptT' m ε α := (pure (Except.error e) : m (Except ε α))
@[inline] def lift (x : m α) : ExceptT' m ε α := (do let a ← x; pure (Except.ok a) : m (Except ε α))
instance : Monad (ExceptT' m ε) := { pure := @ExceptT'.pure _ _ _, bind := @ExceptT'.bind _ _ _ }
end ExceptT'

abbrev M (α : Type) := ExceptT' (StateT' Id (Array Nat)) String α

@[inline] def read : M (Array Nat) := ExceptT'.lift StateT'.read
@[inline] def updt (f : Array Nat → Array Nat) : M Unit := ExceptT'.lift (StateT'.updt f)
@[inline] def throw' {α : Type} (e : String) : M α := ExceptT'.error e

def size' : M Nat := do let a ← read; pure a.size

def get' (i : Nat) : M Nat := do
  let a ← read
  if h : i < a.size then pure a[i] else throw' s!"index {i} out of {a.size}"

def push' (v : Nat) : M Unit := updt (·.push v)

def sumTo : Nat → Nat → M Nat
  | 0, acc => pure acc
  | k + 1, acc => do
    let v ← get' k
    sumTo k (acc + v)

def fill : Nat → M Unit
  | 0 => pure ()
  | k + 1 => do push' (k * 3 % 17); fill k

/-- Errors pass through `bind` unchanged (an error arm returns the callee's
result, of another type). -/
def program (n : Nat) (bad : Bool) : M Nat := do
  fill n
  let s ← size'
  let t ← sumTo s 0
  if bad then
    let _ ← get' (s + 5)
    pure 0
  else pure (t + s)

def runM {α : Type} (x : M α) : Except String α × Array Nat := x #[]

structure Stats where
  lo : Nat
  hi : Nat
  total : Nat
  deriving Repr

@[noinline] def stats (xs : List Nat) : Stats :=
  xs.foldl (fun s x => { lo := min s.lo x, hi := max s.hi x, total := s.total + x })
    { lo := 1000000, hi := 0, total := 0 }

@[noinline] def statsSpread (xs : List Nat) : Nat :=
  let s := stats xs
  s.hi - s.lo + s.total

mutual
  def evenOdd : Nat → Nat × Nat
    | 0 => (1, 0)
    | k + 1 => let (e, o) := oddEven k; (e + 1, o)
  def oddEven : Nat → Nat × Nat
    | 0 => (0, 1)
    | k + 1 => let (e, o) := evenOdd k; (e, o + 2)
end

@[noinline] def fibPair : Nat → Nat × Nat
  | 0 => (0, 1)
  | k + 1 => let (a, b) := fibPair k; (b, (a + b) % 1000000007)

@[noinline] def nested (k : Nat) : (Nat × Nat) × Nat :=
  if k % 2 == 0 then ((k, k + 1), k + 2) else ((k * 2, k), 7)

structure Scal where
  w : UInt64
  x : Float
  b : Bool

@[noinline] def scal (k : Nat) : Scal :=
  if k % 3 == 0 then { w := UInt64.ofNat k * 1000003, x := k.toFloat / 3.0, b := true }
  else { w := 18446744073709551000 + UInt64.ofNat k, x := 0.25, b := false }

@[noinline] def withFn (k : Nat) : (Nat → Nat) × Nat := (fun y => y + k, k * 2)

@[noinline] def keepOrBump (p : Nat × Nat) (bump : Bool) : Nat × Nat :=
  if bump then (p.1 + 1, p.2) else p

unsafe def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 2000
  match runM (program n false) with
  | (.ok v, s) => IO.println s!"ok {v} size {s.size}"
  | (.error e, s) => IO.println s!"error {e} size {s.size}"
  match runM (program n true) with
  | (.ok v, s) => IO.println s!"ok {v} size {s.size}"
  | (.error e, s) => IO.println s!"error {e} size {s.size}"
  let xs := (List.range n).map (· * 7919 % 10007)
  IO.println s!"spread {statsSpread xs}"
  let kept := [stats xs, stats (xs.take 10)]
  IO.println s!"kept {kept.map (·.total)} {repr (stats [])}"
  IO.println s!"evenOdd {evenOdd (n % 101)} oddEven {oddEven (n % 103)}"
  IO.println s!"fibPair {fibPair n}"
  let ((a, b), c) := nested n
  IO.println s!"nested {a} {b} {c} {(nested (n + 1)).1.1}"
  let sc := (List.range 5).map scal
  IO.println s!"scal {sc.map (·.w)} {sc.map (·.x)} {sc.map (·.b)}"
  let pairs := (List.range 4).map fibPair
  IO.println s!"as a function value {pairs}"
  let (f, k) := withFn n
  IO.println s!"withFn {f 1} {k}"
  let p : Nat × Nat := (n, n + 3)
  let q0 := keepOrBump p false
  let q1 := keepOrBump p true
  IO.println s!"keepOrBump {q0} {q1} same0={ptrEq p q0} same1={ptrEq p q1}"
