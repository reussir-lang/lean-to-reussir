/-! Runtime test: cases of the shared dependent-type corpus (programs built
by another translator's team and checked against native Lean), combined:
each case keeps its code in a namespace named after its case id, and `main`
runs each with that case's arguments in this order, printing `-- <id>`
before it (and `exit <code>` after a `main : IO UInt32`). The cases, with
what each checks:
- `A880`: Emit printed a cast before `<` unparenthesized (`a | b as u32 <
  128u32`, rustc's generic-argument parse), from String.decodeChar's guard
  and a direct UInt8 → UInt32 comparison.
- `A881`: N14's manual_range_contains outside C9's collapse.
- `A883`: Comparisons of a fixed-width variable with its type's 0 or MAX (`x
  < 0u8`, `255u8 < x`, `x <= 0u8`) and redundant, impossible or tautological
  pairs of literal comparisons on one variable (`x >= 10 && x > 20`, ...
- `A885`: A structure whose slot parameter a field holds under a pointer-
  carrying container (`items : List α`), built at `Nat` and `String` in one
  array (tracked: refused as nested-coercion naming ...
- `A886`: (e), Lem-T15-dyn: a dynamic read tests the type the value was
  injected at, the variant read in the declaration's own type parameters
  (`take::<Option<A>>`), then makes it the use's type
- `A887`: A slot parameter's field under a by- value constructor around an
  arrow (`shw : Option (α → String)`) takes its own coercions in the rebuild
  (`DepCo.wrapField`), and the rewrite's own ...
- `A888`: An extreme comparison whose operand is a call
  (`array::get_bang(..) < 0u8`, `get_v(..) <= 255u8`) was not folded, and a
  fold left identical literal arms under an effectful condition (`if
  boom(..) { true } else ...
- `A890`: Types.md Rule 6.3a under D67 (e): a lifted lambda, partial
  application or nested lambda that passes its dependent parameter's `Dyn`
  on to `lenP` keeps the generic and prints `len_p::<A>`
- `A892`: A structure's slot parameter under an arrow inside `Except`,
  `Sum`, a product and `Except` of a pair of arrows: the field is rebuilt
  with its own wrappers, and an alternative that changes ...
- `A893`: Types.md Rule 6.3a: the instance keys KS and KL relate into K's
  most general key, and a T15 wrapper reads `_dep.gen.<declaration>` as its
  own type parameters.
- `A894`: Outside a cast node a read at a type no variant has is never
  reached (Lem-T15-dyn (b)): `P2`'s `shw` at `String` with `gen := none` is
  wrapped as `unreachable!`, and Lean's `[3, nogen]` prints. -/

namespace A880
def lowBits (a b : UInt8) : Bool :=
  ((a.toUInt32 <<< 8) ||| (b &&& 63).toUInt32) < 128

def outside (n : Nat) (x : UInt32) : Bool :=
  if x < 10 then n + 1 < 3 else if x > 20 then n + 1 < 3 else n == 7

@[noinline] def chain3 (y : Bool) (x : UInt8) (n : Nat) : IO Nat := do
  if y then IO.print "T" else if x < 10 then IO.print "T" else if x > 20 then IO.print "T" else IO.print "F"
  return n

@[noinline] def chain4 (x z : UInt8) (n : Nat) : IO Nat := do
  if x < 10 then IO.print "T" else if x > 20 then IO.print "T" else if z < 3 then IO.print "T"
  else if z > 9 then IO.print "T" else IO.print "F"
  return n

@[inline] def k (x : UInt8) : Option UInt8 :=
  if x < 10 then none else if x > 20 then none else some x

@[noinline] def useK (n : Nat) (x : UInt8) : Nat :=
  match k x with
  | none => n + 7
  | some v => n + v.toNat

@[noinline] def degen (x : UInt8) (w : UInt16) : List Bool :=
  [x < 0, 255 < x, x ≤ 0, x ≥ 255, w < 0, w ≤ 65535, 65535 ≤ w, x ≥ 10 && x > 20, x ≥ 0 && 0 == x,
   x < 10 && x > 20, x < 10 || x ≥ 5, x ≥ 0, x == 3 || x ≤ 7, x > 20 || x ≥ 10]

@[noinline] def pairs (x : UInt8) (n : Nat) : IO Nat := do
  if x > 20 then IO.print "T" else if x ≥ 10 then IO.print "T" else IO.print "F"
  if x < 10 then IO.print "T" else if x ≥ 5 then IO.print "T" else IO.print "F"
  if x ≥ 10 then (if x > 20 then IO.print "T" else pure ()) else pure ()
  if x < 10 then (if x > 20 then IO.print "T" else pure ()) else pure ()
  if x ≥ 0 then (if 0 == x then IO.print "Z" else pure ()) else pure ()
  return n

@[noinline] def getV (a : Array UInt8) (i : Nat) : UInt8 := a[i]!
@[noinline] def boom (a : Array UInt8) (x : UInt8) : Bool := a[x.toNat]! == 7

@[noinline] def effs (a : Array UInt8) (i j : Nat) (x : UInt8) : List String :=
  [if a[i]! < 0 then "neg" else "nonneg", if a[i]! ≤ 255 then "le" else "gt",
   if a[i]! > 2 || a[j]! ≤ 255 then "or" else "nor", if a[i]! > 2 && a[j]! > 255 then "and" else "nand",
   if getV a j < 0 then "n" else "p", if 255 < getV a i then "big" else "small",
   if a[i]! > 0 && x < 0 then "y" else "z", if boom a x || x ≥ 0 then "t" else "f"]

@[noinline] def p5 (arr : Array UInt8) (i : Nat) (x : UInt8) : Bool := arr[i]! > 0 && x < 0
@[noinline] def p6 (arr : Array UInt8) (x : UInt8) : Bool := boom arr x || x ≥ 0

def caseMain (args : List String) : IO UInt32 := do
  let s := args.getD 0 ""
  let n := (args.getD 1 "0").toNat!
  let a := (args.getD 2 "0").toNat!.toUInt8
  let b := (args.getD 3 "0").toNat!.toUInt8
  if h : (s.toByteArray.utf8DecodeChar? n).isSome = true then
    IO.println s!"char={(String.decodeChar s n h).toNat}"
  else
    IO.println "char=none"
  IO.println s!"lt={decide (a.toUInt32 < b.toUInt32)} low={lowBits a b} out={outside n a.toUInt32} out2={outside 7 b.toUInt32}"
  let c3 ← chain3 (n == 2) a n
  let c4 ← chain4 a b n
  IO.println s!" c={c3 + c4} k={useK n a} k2={useK n b}"
  IO.println s!"d={degen a (b.toUInt16 * 257)} d2={degen b 0}"
  let p ← pairs a n
  let q ← pairs b n
  IO.println s!" p={p + q}"
  let arr : Array UInt8 := #[1, 200, 3]
  IO.println s!"e={effs arr (n % 3) ((n + 1) % 3) a}"
  IO.println s!"e2={effs arr (n + 5) 0 b}"
  IO.println s!"r2={p5 arr (n % 3) a} {p6 arr (b % 3)} {p5 arr (n + 4) a} {p6 arr b}"
  return 0
end A880

namespace A881
@[noinline] def out1 (x : UInt8) (n : Nat) : IO Nat := do
  if x < 10 then IO.print "T" else if x > 20 then IO.print "T" else IO.print "F"
  return n

@[noinline] def chain3 (y : Bool) (x : UInt8) (n : Nat) : IO Nat := do
  if y then IO.print "T" else if x < 10 then IO.print "T" else if x > 20 then IO.print "T" else IO.print "F"
  return n

@[noinline] def chain4 (x z : UInt8) (n : Nat) : IO Nat := do
  if x < 10 then IO.print "T" else if x > 20 then IO.print "T" else if z < 3 then IO.print "T"
  else if z > 9 then IO.print "T" else IO.print "F"
  return n

@[inline] def k (x : UInt8) : Option UInt8 :=
  if x < 10 then none else if x > 20 then none else some x

@[noinline] def useK (n : Nat) (x : UInt8) : Nat :=
  match k x with
  | none => n + 7
  | some v => n + v.toNat

def caseMain (args : List String) : IO UInt32 := do
  let n := (args.getD 0 "0").toNat!
  let a := (args.getD 1 "0").toNat!.toUInt8
  let b := (args.getD 2 "0").toNat!.toUInt8
  let r1 ← out1 a n
  let r3 ← chain3 (n == 2) a n
  let r4 ← chain4 a b n
  IO.println s!" r={r1 + r3 + r4} k={useK n a} k2={useK n b}"
  return 0
end A881

namespace A883
@[noinline] def degen (x : UInt8) (w : UInt16) : List Bool :=
  [x < 0, 255 < x, x ≤ 0, x ≥ 255, w < 0, w ≤ 65535, 65535 ≤ w, x ≥ 10 && x > 20, x ≥ 0 && 0 == x,
   x < 10 && x > 20, x < 10 || x ≥ 5, x ≥ 0, x == 3 || x ≤ 7, x > 20 || x ≥ 10]

@[noinline] def pairs (x : UInt8) (n : Nat) : IO Nat := do
  if x > 20 then IO.print "T" else if x ≥ 10 then IO.print "T" else IO.print "F"
  if x < 10 then IO.print "T" else if x ≥ 5 then IO.print "T" else IO.print "F"
  if x ≥ 10 then (if x > 20 then IO.print "T" else pure ()) else pure ()
  if x < 10 then (if x > 20 then IO.print "T" else pure ()) else pure ()
  if x ≥ 0 then (if 0 == x then IO.print "Z" else pure ()) else pure ()
  return n

def caseMain (args : List String) : IO UInt32 := do
  let n := (args.getD 0 "0").toNat!
  let a := (args.getD 1 "0").toNat!.toUInt8
  let b := (args.getD 2 "0").toNat!.toUInt8
  IO.println s!"d={degen a (b.toUInt16 * 257)} d2={degen b 0}"
  let p ← pairs a n
  let q ← pairs b n
  IO.println s!" p={p + q}"
  return 0
end A883

namespace A885

structure Pkg where
  α : Type
  val : α
  items : List α
@[noinline] def pkgN (n : Nat) : Pkg := ⟨Nat, n, [n, n + 1]⟩
@[noinline] def pkgS (s : String) : Pkg := ⟨String, s, [s, "x", "y"]⟩
def caseMain (args : List String) : IO Unit := do
  let n := args.length
  let ps : Array Pkg := #[pkgN n, pkgS "s"]
  IO.println s!"{ps.foldl (fun a p => a + p.items.length) 0}"
end A885

namespace A886

def T1 (α : Type) : Bool → Type
  | true => α
  | false => Option α
def mk1 {α : Type} (b : Bool) (x : α) : T1 α b := match b with
  | true => x
  | false => some x
def get1 {α : Type} (b : Bool) (v : T1 α b) (d : α) : α := match b, v with
  | true, a => a
  | false, o => (show Option α from o).getD d
def caseMain (args : List String) : IO UInt32 := do
  let b := args.length % 2 == 0
  IO.println s!"{get1 b (mk1 b "z") "d"}"
  return 0
end A886

namespace A887

structure POpt where
  α : Type
  val : α
  shw : Option (α → String)
def rO (p : POpt) : String := match p.shw with | some f => f p.val | none => "none"
def caseMain (args : List String) : IO UInt32 := do
  let k := args.length
  let os : List POpt := [⟨Nat, k, some toString⟩, ⟨String, "q", none⟩]
  IO.println s!"{os.map rO}"
  return 0
end A887

namespace A888
@[noinline] def getV (a : Array UInt8) (i : Nat) : UInt8 := a[i]!
@[noinline] def boom (a : Array UInt8) (x : UInt8) : Bool := a[x.toNat]! == 7

@[noinline] def effs (a : Array UInt8) (i j : Nat) (x : UInt8) : List String :=
  [if a[i]! < 0 then "neg" else "nonneg", if a[i]! ≤ 255 then "le" else "gt",
   if a[i]! > 2 || a[j]! ≤ 255 then "or" else "nor", if a[i]! > 2 && a[j]! > 255 then "and" else "nand",
   if getV a j < 0 then "n" else "p", if 255 < getV a i then "big" else "small",
   if a[i]! > 0 && x < 0 then "y" else "z", if boom a x || x ≥ 0 then "t" else "f"]

@[noinline] def p5 (arr : Array UInt8) (i : Nat) (x : UInt8) : Bool := arr[i]! > 0 && x < 0
@[noinline] def p6 (arr : Array UInt8) (x : UInt8) : Bool := boom arr x || x ≥ 0

def caseMain (args : List String) : IO UInt32 := do
  let n := (args.getD 0 "0").toNat!
  let a := (args.getD 1 "0").toNat!.toUInt8
  let b := (args.getD 2 "0").toNat!.toUInt8
  let arr : Array UInt8 := #[1, 200, 3]
  IO.println s!"e={effs arr (n % 3) ((n + 1) % 3) a}"
  IO.println s!"e2={effs arr (n + 5) 0 b}"
  IO.println s!"r2={p5 arr (n % 3) a} {p6 arr (b % 3)} {p5 arr (n + 4) a} {p6 arr b}"
  return 0
end A888

namespace A890

@[noinline] def pickL {α : Type} (b : Bool) (x : α) : if b then List α else List (List α) :=
  match b with | true => [x, x, x] | false => [[x], [x]]
@[noinline] def lenP {α : Type} (b : Bool) (v : if b then List α else List (List α)) : Nat :=
  match b, v with
  | true, xs => xs.length
  | false, xss => xss.length + 10
@[noinline] def lenK {α : Type} (k : Nat) (b : Bool) (v : if b then List α else List (List α)) : Nat :=
  match b, v with
  | true, xs => xs.length + k
  | false, xss => xss.length + 10 * k
@[noinline] def useFn (f : (b : Bool) → (if b then List Nat else List (List Nat)) → Nat) (b : Bool) (n : Nat) : Nat :=
  f b (pickL b n)
@[noinline] def useG {γ : Type} (f : (b : Bool) → (if b then List γ else List (List γ)) → Nat) (b : Bool) (x : γ) : Nat :=
  f b (pickL b x)
-- a lambda passing its dependent parameter on to lenP (reviewer 1's R1)
@[noinline] def lenLam (b : Bool) (n : Nat) : Nat := useFn (fun c v => lenP c v + 1) b n
-- a partial application and nested lambdas
@[noinline] def viaPartial (b : Bool) (n : Nat) : Nat := useFn (lenK (n + 1)) b n
@[noinline] def viaNested (b : Bool) (n : Nat) : Nat := useFn (fun c => fun v => (fun w => lenK 2 c w * 2) v) b n
-- a lambda capturing a dependent value
@[noinline] def capt (b0 : Bool) (n : Nat) : Nat :=
  let held := pickL b0 (n + 7)
  useFn (fun c v => lenP c v + lenP b0 held * 100) (!b0) n
-- a lambda in generic code
@[noinline] def viaG {δ : Type} (b : Bool) (x : δ) : Nat := useG (fun c v => lenP c v + 1) b x
def caseMain (args : List String) : IO Unit := do
  let n := args.length
  IO.println s!"{[lenLam true n, lenLam false n]} {[viaPartial true n, viaPartial false n, viaNested true n, viaNested false n]}"
  IO.println s!"{[capt true n, capt false n]} {[viaG true n, viaG false "s", viaG false n, viaG true "t"]}"
end A890

namespace A892

structure P4 where
  α : Type
  val : α
  ex : Except String (α → α)
  shw : α → String
def r4 (p : P4) : String := match p.ex with | .ok f => p.shw (f p.val) | .error e => e
structure P5 where
  α : Type
  val : α
  ex : Sum (α → α) Nat
  shw : α → String
def r5 (p : P5) : String := match p.ex with | .inl f => p.shw (f p.val) | .inr n => toString n
structure P6 where
  α : Type
  val : α
  ex : (α → α) × Nat
  shw : α → String
def r6 (p : P6) : String := p.shw (p.ex.1 p.val) ++ toString p.ex.2
structure P8 where
  α : Type
  val : α
  ex : Except String ((α → α) × (α → String))
def r8 (p : P8) : String := match p.ex with | .ok (f, g) => g (f p.val) | .error e => e
def caseMain (args : List String) : IO UInt32 := do
  let k := args.length
  let l4 : List P4 := [⟨Nat, k, .ok (· + 1), toString⟩, ⟨String, "s", .error "err", id⟩]
  let l5 : List P5 := [⟨Nat, k, .inl (· + 1), toString⟩, ⟨String, "s", .inr 9, id⟩, ⟨String, "t", .inl (· ++ "!"), id⟩]
  let l6 : List P6 := [⟨Nat, k, ((· + 1), 3), toString⟩, ⟨String, "s", ((· ++ "?"), 4), id⟩]
  let l8 : List P8 := [⟨Nat, k, .ok ((· * 2), toString)⟩, ⟨String, "s", .error "e"⟩, ⟨String, "u", .ok ((· ++ "+"), id)⟩]
  IO.println s!"{l4.map r4} {l5.map r5} {l6.map r6} {l8.map r8}"
  return 0
end A892

namespace A893

def K (α β : Type) : Bool → Type
  | true => α
  | false => β
def KS (γ : Type) (b : Bool) : Type := K γ γ b
def KL (γ : Type) (b : Bool) : Type := K γ (List γ) b
def mkS {γ : Type} (b : Bool) (x : γ) : KS γ b := match b with
  | true => x
  | false => x
def mkL {γ : Type} (b : Bool) (x : γ) : KL γ b := match b with
  | true => x
  | false => [x, x, x]
def readK {α β : Type} (b : Bool) (v : K α β b) (f : α → Nat) (g : β → Nat) : Nat := match b, v with
  | true, a => f (show α from a)
  | false, c => g (show β from c)
def caseMain (args : List String) : IO UInt32 := do
  let k := args.length
  let b := k % 2 == 0
  IO.println s!"{readK (α := Nat) (β := Nat) b (mkS b k) id (· + 100)} {readK (α := String) (β := List String) b (mkL b "x") String.length List.length}"
  IO.println s!"{readK (α := Nat) (β := List Nat) (!b) (mkL (!b) k) id (fun l => l.length * 2)}"
  return 0
end A893

namespace A894

structure P2 where
  α : Type
  gen : Option (Nat → α)
  shw : α → String
def r2 (p : P2) (n : Nat) : String := match p.gen with | some g => p.shw (g n) | none => "nogen"
def caseMain (args : List String) : IO UInt32 := do
  let k := args.length
  let l2 : List P2 := [⟨Nat, some (· * 3), toString⟩, ⟨String, none, id⟩]
  IO.println s!"{l2.map (r2 · k)}"
  return 0
end A894

def main : IO Unit := do
  IO.println "-- A880"
  let c ← A880.caseMain ["ab", "5", "20", "9"]
  IO.println s!"exit {c}"
  IO.println "-- A881"
  let c ← A881.caseMain ["3", "9", "21"]
  IO.println s!"exit {c}"
  IO.println "-- A883"
  let c ← A883.caseMain ["3", "7", "0"]
  IO.println s!"exit {c}"
  IO.println "-- A885"
  A885.caseMain ["a", "b", "c"]
  IO.println "-- A886"
  let c ← A886.caseMain ["a"]
  IO.println s!"exit {c}"
  IO.println "-- A887"
  let c ← A887.caseMain ["a"]
  IO.println s!"exit {c}"
  IO.println "-- A888"
  let c ← A888.caseMain ["4", "1", "9"]
  IO.println s!"exit {c}"
  IO.println "-- A890"
  A890.caseMain ["a"]
  IO.println "-- A892"
  let c ← A892.caseMain ["a"]
  IO.println s!"exit {c}"
  IO.println "-- A893"
  let c ← A893.caseMain ["a"]
  IO.println s!"exit {c}"
  IO.println "-- A894"
  let c ← A894.caseMain ["a"]
  IO.println s!"exit {c}"
