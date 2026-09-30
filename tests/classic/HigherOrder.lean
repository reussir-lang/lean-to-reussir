/-
lean2rr classic corpus: `higher-order` (written for this corpus).

Hand-written and library map/filter/foldl/foldr; closures stored in lists,
arrays, structures and options; partial application of known and unknown
functions; functions that do work before returning a closure; calls through
unknown closures of different arities; over-application (applying a
function to more arguments than its definition takes, the extra ones going
to the returned closure); composition chains; Church numerals; CPS.

Size argument n (default 20000000): the number of loop iterations in the
driver; each iteration makes many indirect calls.
-/

/-! ## Hand-written list combinators -/

def myMap {α β : Type} (f : α → β) : List α → List β
  | [] => []
  | x :: xs => f x :: myMap f xs

def myFilter {α : Type} (p : α → Bool) : List α → List α
  | [] => []
  | x :: xs => if p x then x :: myFilter p xs else myFilter p xs

def myFoldl {α β : Type} (f : β → α → β) (init : β) : List α → β
  | [] => init
  | x :: xs => myFoldl f (f init x) xs

def myFoldr {α β : Type} (f : α → β → β) (init : β) : List α → β
  | [] => init
  | x :: xs => f x (myFoldr f init xs)

/-! ## Closures in data structures -/

structure Op where
  name : String
  arity : Nat
  run1 : Nat → Nat
  run2 : Nat → Nat → Nat
  run3 : Nat → Nat → Nat → Nat
deriving Inhabited

def add3 (a b c : Nat) : Nat := a + 2 * b + 3 * c

def ops (k : Nat) : Array Op := #[
  { name := "add", arity := 2, run1 := (· + k), run2 := Nat.add, run3 := add3 },
  { name := "mul", arity := 2, run1 := (· * 3), run2 := (· * ·), run3 := fun a b c => a * b + c },
  { name := "max", arity := 2, run1 := Nat.max k, run2 := Nat.max, run3 := fun a b c => Nat.max a (Nat.max b c) },
  { name := "sub", arity := 2, run1 := Nat.sub (1000 + k), run2 := Nat.sub, run3 := fun a => add3 (a + k) }
]

/-- A table of named unary functions, some of them partial applications. -/
def table (k : Nat) : List (String × (Nat → Nat)) :=
  [("succ", Nat.succ), ("dbl", fun x => 2 * x), ("addk", Nat.add k), ("mod7", (· % 7)),
   ("add3_1_2", add3 1 2), ("add3_x", fun x => add3 x x x), ("pow2", fun x => 2 ^ (x % 20))]

/-! ## Functions that do work, then return closures -/

/-- Computes the polynomial's coefficients' sum first, then returns an evaluator
  that captures both the list and the sum. -/
def mkPoly (coeffs : List Nat) : Nat → Nat :=
  let s := coeffs.foldl (· + ·) 0
  fun x => (coeffs.foldr (fun c acc => acc * x + c) 0 + s) % 1000000007

/-- Returns a closure of two arguments after a loop. -/
def mkMixer (seed : Nat) : Nat → Nat → Nat := Id.run do
  let mut h := seed
  for i in [0:10] do
    h := (h * 31 + i) % 65521
  return fun a b => (a * h + b) % 65521

/-- Returns a function that itself returns a function (curried result). -/
def mkCurried (k : Nat) : Nat → Nat → Nat → Nat :=
  let base := k * k
  fun a =>
    let t := a + base
    fun b c => t * b + c

/-- A closure capturing values of many types. -/
def mkCapture (n : Nat) (s : String) (f : Float) (u : UInt64) (i : Int) (b : Bool) : Nat → String :=
  fun x => s!"{n + x}:{s}:{f + x.toFloat}:{u + x.toUInt64}:{i - x}:{b && x % 2 == 0}"

/-! ## Arity games -/

def compose {α β γ : Type} (g : β → γ) (f : α → β) : α → γ := fun x => g (f x)

def twice {α : Type} (f : α → α) : α → α := f ∘ f

def flip' {α β γ : Type} (f : α → β → γ) : β → α → γ := fun b a => f a b

def curry' {α β γ : Type} (f : α × β → γ) : α → β → γ := fun a b => f (a, b)

def uncurry' {α β γ : Type} (f : α → β → γ) : α × β → γ := fun p => f p.1 p.2

/-- Takes two arguments and returns a unary function: `pick a b c` is an
  over-application. -/
def pick (a b : Nat) : Nat → Nat :=
  if a > b then (· + a) else (· * (b + 1))

/-- An unknown function of arity 3 applied one argument at a time and all at once. -/
def applyStaged (f : Nat → Nat → Nat → Nat) (a b c : Nat) : Nat :=
  let g := f a
  let h := g b
  h c + f a b c + (f a) b c

/-- Apply a list of unknown functions of different shapes. -/
def applyAll (fs : List (Nat → Nat)) (x : Nat) : Nat :=
  fs.foldl (fun acc f => (acc + f x) % 1000000007) 0

/-! ## Church numerals and CPS -/

def Church := (Nat → Nat) → Nat → Nat

def church : Nat → Church
  | 0 => fun _ z => z
  | n + 1 => fun s z => s (church n s z)

def churchAdd (a b : Church) : Church := fun s z => a s (b s z)
def churchMul (a b : Church) : Church := fun s => a (b s)
def unchurch (c : Church) : Nat := c (· + 1) 0

def sumCPS : List Nat → (Nat → Nat) → Nat
  | [], k => k 0
  | x :: xs, k => sumCPS xs (fun r => k (r + x))

/-! ## Driver -/

def main (args : List String) : IO UInt32 := do
  let n := (args.head?.bind String.toNat?).getD 20000000

  -- List combinators, hand-written versus library.
  let xs := List.range 2000
  let a1 := myFoldl (· + ·) 0 (myMap (· * 3) (myFilter (· % 2 == 0) xs))
  let a2 := ((xs.filter (· % 2 == 0)).map (· * 3)).foldl (· + ·) 0
  let a3 := myFoldr (fun x acc => (acc * 7 + x) % 1000003) 1 xs
  let a4 := xs.foldr (fun x acc => (acc * 7 + x) % 1000003) 1
  IO.println s!"lists: {a1} {a2} {a3} {a4} {myFoldr (fun x acc => x :: acc) [] [1, 2, 3]} {(myMap toString [1, 2]) ++ ["x"]}"

  -- Main loop: indirect calls through every kind of closure.
  let tbl := table 5
  let opsA := ops 7
  let poly := mkPoly [3, 1, 4, 1, 5, 9, 2, 6]
  let mixer := mkMixer 12345
  let cur := mkCurried 3
  let cur1 := cur 11          -- partial application of a returned closure
  let chain := (List.range 50).foldl (fun f i => compose (· + i % 3) f) id
  let fs : List (Nat → Nat) := [poly, mixer 3, cur1 2, cur 1 1, twice (· * 2), flip' Nat.sub 3,
                                 curry' (fun p => p.1 * p.2) 6, uncurry' Nat.add ∘ (fun x => (x, x)), chain]
  let mut acc : Nat := 0
  let mut acc2 : UInt64 := 0
  for i in [0:n] do
    let (_, f) := tbl[i % tbl.length]!
    let op := opsA[i % opsA.size]!
    acc := (acc + f i + op.run1 i + op.run2 i (i % 13) + op.run3 i 2 3) % 1000000007
    acc := (acc + pick (i % 17) 8 i + applyStaged op.run3 (i % 5) 1 2) % 1000000007
    if i % 64 == 0 then
      acc := (acc + applyAll fs i) % 1000000007
    acc2 := acc2 * 31 + (mixer i (i + 1)).toUInt64
  IO.println s!"loop: {acc} {acc2}"

  -- Closures stored in an array, updated functionally, then applied.
  let mut arr : Array (Nat → Nat) := #[]
  for k in [0:32] do
    arr := arr.push (if k % 2 == 0 then (· + k) else (Nat.mul k))
  arr := arr.modify 3 (fun f => f ∘ f)
  arr := arr.set! 0 (mkPoly [1, 1])
  let applied := arr.foldl (fun (s : Nat) f => s + f 10) 0
  IO.println s!"array: size={arr.size} sum={applied}"

  -- Option / Except of closures.
  let optF : Option (Nat → Nat → Nat) := if n > 0 then some (fun a b => a * 100 + b) else none
  let r1 := match optF with | some f => f 4 2 | none => 0
  let exF : Except String (Nat → Nat) := .ok (cur 1 2)
  let r2 := match exF with | .ok f => f 5 | .error _ => 0
  IO.println s!"option/except: {r1} {r2} {(optF.map (· 7)).map (· 8) |>.getD 0}"

  -- Captures, currying, Church numerals, CPS.
  let cap := mkCapture 10 "s" 1.5 (0xFFFFFFFFFFFFFFFF) (-3) true
  IO.println s!"capture: {cap 1} {cap 2}"
  let c6 := church 6
  let c7 := church 7
  IO.println s!"church: {unchurch (churchAdd c6 c7)} {unchurch (churchMul c6 c7)} {unchurch (church (n % 997))} cps: {sumCPS (List.range 1000) id} {sumCPS [1, 2, 3] (· * 10)}"
  IO.println s!"arity: {pick 9 2 5} {pick 1 2 5} {(pick 3 4) 5} {applyStaged add3 1 2 3} {(compose (· + 1) (· * 2)) 5} {mkCurried 2 1 2 3} {(mkCurried 2 1) 2 3} {mkMixer 1 2 3}"
  pure 0
