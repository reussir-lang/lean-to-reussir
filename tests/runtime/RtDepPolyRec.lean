/-! Runtime test: polymorphic recursion, where a function calls itself at a
larger type, so that no finite set of copies per type argument covers the
calls:
- `nest`-style recursion at `α × α`, `List α`, `Option α` and `Array α`,
  printing with dictionaries that each level builds from the one before
  (`ToString (α × α)` from `ToString α`: `instToStringProd` over an
  unknown type), and the same with `Hashable` and `Ord`;
- nested datatypes over growing types: perfect trees (`Perfect α` holds a
  `Perfect (α × α)`), lists whose element type grows (`Nested α` holds a
  `Nested (List α)`), built, summed, compared and printed;
- monad transformers at an unknown monad: a recursion that adds a
  `StateT`, a `ReaderT` or an `ExceptT` layer at each level, throwing and
  catching across levels.
Arguments: D N (default 10 6): the depth of the recursions and a size. -/

-- nest-style recursion
def nestP {α : Type} [ToString α] : Nat → α → String
  | 0, x => toString x
  | n + 1, x => nestP n (x, x)

def nestL {α : Type} [ToString α] : Nat → α → String
  | 0, x => toString x
  | n + 1, x => nestL n [x, x]

def nestO {α : Type} [ToString α] : Nat → α → String
  | 0, x => toString x
  | n + 1, x => nestO n (some x)

def nestA {α : Type} [ToString α] : Nat → α → String
  | 0, x => toString x
  | n + 1, x => nestA n #[x]

def hashNest {α : Type} [Hashable α] : Nat → α → UInt64
  | 0, x => hash x
  | n + 1, x => mixHash (hash x) (hashNest n (x, x))

def ordNest {α : Type} [Ord α] : Nat → α → α → Ordering
  | 0, x, y => compare x y
  | n + 1, x, y =>
    let _ : Ord (α × α) := lexOrd
    match ordNest n (x, y) (y, x) with
    | Ordering.eq => compare x y
    | o => o

-- nested datatypes
/-- A perfect tree: the type argument doubles at each level (an index, as
Lean requires for a nested datatype over a growing type). -/
inductive Perfect : Type → Type 1 where
  | zero {α : Type} (x : α) : Perfect α
  | succ {α : Type} (t : Perfect (α × α)) : Perfect α

def Perfect.mk {α : Type} : Nat → α → Perfect α
  | 0, x => .zero x
  | n + 1, x => .succ (Perfect.mk n (x, x))

/-- Builds with different leaves: the pair `(x, f x)` at each level. -/
def Perfect.mk2 {α : Type} (f : α → α) : Nat → α → Perfect α
  | 0, x => .zero x
  | n + 1, x => .succ (Perfect.mk2 (fun p => (f p.1, f p.2)) n (x, f x))

def Perfect.sum {α : Type} (f : α → Nat) : Perfect α → Nat
  | .zero x => f x
  | .succ t => Perfect.sum (fun p => f p.1 + f p.2) t

def Perfect.depth {α : Type} : Perfect α → Nat
  | .zero _ => 0
  | .succ t => 1 + t.depth

def Perfect.beq {α : Type} (eq : α → α → Bool) : Perfect α → Perfect α → Bool
  | .zero x, .zero y => eq x y
  | .succ s, .succ t => Perfect.beq (fun p q => eq p.1 q.1 && eq p.2 q.2) s t
  | _, _ => false

def Perfect.str {α : Type} [ToString α] : Perfect α → String
  | .zero x => toString x
  | .succ t => "S" ++ t.str

inductive Nested : Type → Type 1 where
  | nil {α : Type} : Nested α
  | cons {α : Type} (x : α) (rest : Nested (List α)) : Nested α

def Nested.mk {α : Type} : Nat → α → Nested α
  | 0, _ => .nil
  | n + 1, x => .cons x (Nested.mk n [x, x])

def Nested.len {α : Type} : Nested α → Nat
  | .nil => 0
  | .cons _ r => 1 + r.len

def Nested.sum {α : Type} (f : α → Nat) : Nested α → Nat
  | .nil => 0
  | .cons x r => f x + Nested.sum (fun l => l.foldl (fun s y => s + f y) 0) r

-- monad transformers at an unknown monad
def growS {m : Type → Type} [Monad m] [MonadStateOf Nat m] : Nat → m Nat
  | 0 => do modify (· + 1); return (← get)
  | k + 1 => do
    let r ← (growS (m := StateT String m) k).run' s!"lvl{k}"
    modify (· + r)
    return r + 1

def growR {m : Type → Type} [Monad m] [MonadReaderOf Nat m] : Nat → m Nat
  | 0 => read
  | k + 1 => do
    let base ← read
    let r ← (growR (m := ReaderT Nat m) k).run (base + k)
    return r * 2 + base

def growE {m : Type → Type} [Monad m] [MonadExceptOf String m] : Nat → m Nat
  | 0 => throw "bottom"
  | k + 1 => do
    let r ← (growE (m := ExceptT Nat m) k).run
    match r with
    | .ok v => if k % 3 == 0 then throw s!"at {k} got {v}" else return v + 1
    | .error e => return e + 100
termination_by k => k

def catchE {m : Type → Type} [Monad m] [MonadExceptOf String m] (k : Nat) : m Nat :=
  tryCatch (growE k) (fun e => return e.length)

def main (args : List String) : IO Unit := do
  let d := (args.getD 0 "10").toNat!
  let n := (args.getD 1 "6").toNat!
  IO.println (nestP (d / 3) n)
  IO.println (nestL (d / 3) "s")
  IO.println (nestO d (-(n : Int)))
  IO.println (nestA d (2.5 : Float))
  IO.println (hashNest d n)
  IO.println (hashNest d "h")
  IO.println (repr (ordNest d n (n + 1)))
  IO.println (repr (ordNest d "b" "a"))
  let p := Perfect.mk d n
  let q := Perfect.mk2 (· + 1) d n
  IO.println s!"perfect {p.depth} {p.sum id} {q.sum id} {p.beq (· == ·) p} {p.beq (· == ·) q}"
  IO.println (Perfect.mk 3 "x").str
  IO.println (Perfect.mk2 (fun (u : UInt64) => u * 3) 3 18446744073709551615).str
  let ns := Nested.mk d n
  IO.println s!"nested {ns.len} {ns.sum id}"
  IO.println s!"nested string {(Nested.mk (d / 2) "ab").sum String.length}"
  let (r, s) := (growS (m := StateM Nat) d).run n
  IO.println s!"growS {r} {s}"
  IO.println s!"growR {(growR (m := ReaderM Nat) d).run n}"
  IO.println s!"growE {repr ((catchE (m := Except String) d))}"
  match ← (catchE (m := ExceptT String IO) (d + 1)).run with
  | .ok v => IO.println s!"growE io ok {v}"
  | .error e => IO.println s!"growE io error {e}"
