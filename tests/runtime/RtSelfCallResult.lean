/-! Runtime test: a result type recovered from the callers (Stage 3,
`MonoRetype.resultsFromCallers`) of a declaration that calls itself at
another type. `f {α} (n) (x : α) : α` calls itself at `T k`, a type computed
from `k` (Lean's code types its values `lcAny`). `main` calls `f` at `Big 70`,
a type too large for an instance of its own, so the call goes to the
instance at `lcAny`, whose result is `lcAny`; `main` binds it at `Big 70`.
The inner call binds its result at `lcAny`, the declaration's own result
type, but its value is a `T k` (a `Nat`, then a pair). That self call did not
count as a call site, so Stage 3 gave the instance the result type `Big 70`
and converted every value it returns to it: "INTERNAL PANIC: unreachable
code has been reached" (hunt MONO-01). A self call counts now, except a tail
call at the declaration's result type. -/

-- `T k`: a type that depends on a value.
def T : Nat → Type
  | 0 => Nat
  | n+1 => T n × T n

def mk : (n : Nat) → T n
  | 0 => (7 : Nat)
  | n+1 => (mk n, mk n)

def size : (k : Nat) → T k → Nat
  | 0, v => v
  | k+1, (a, b) => size k a + size k b

-- `Big 70`: larger than Stage 1's bound for type arguments.
def Big : Nat → Type
  | 0 => String
  | n+1 => Big n × Nat

def mkBig : (n : Nat) → Big n
  | 0 => "big"
  | n+1 => (mkBig n, n)

def first : (n : Nat) → Big n → String
  | 0, s => s
  | n+1, (b, _) => first n b

def f {α : Type} (n : Nat) (x : α) : α :=
  match n with
  | 0 => x
  | k+1 =>
    let y : T k := f k (mk k)
    dbgTrace s!"size {size k y}" fun _ => x

-- A tail self call at the result type still lets the callers decide.
def g : (n : Nat) → (m : Nat) → T m
  | 0, m => mk m
  | n+1, m => g n m

def main : IO Unit := do
  let b : Big 70 := f 2 (mkBig 70)
  IO.println (first 70 b)
  let p : Nat × Nat := g 3 1
  IO.println s!"{p.1} {p.2}"
