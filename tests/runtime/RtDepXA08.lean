/-! Runtime test: cases of the shared dependent-type corpus (programs built
by another translator's team and checked against native Lean), combined:
each case keeps its code in a namespace named after its case id, and `main`
runs each with that case's arguments in this order, printing `-- <id>`
before it (and `exit <code>` after a `main : IO UInt32`). The cases, with
what each checks:
- `A808`: T15 step 2 (b): a class whose reduced types differ only at a child
  keeps its head, the child site-keyed (`Pkg<U>`, by value): the injection
  is at the slot, inside a rebuild of the structure.
- `A817`: A Ref read re-nested into a statement that borrows the same cell.
- `A831`: T15 step 2 (b) and 2a: `Pkg2<U1, U2>`, one site key per differing
  child
- `A834`: A position's type is its site root's type read down its path, so
  the `List.nil` tail of `[pickL false n, pickL false (n + 1)].map (lenP
  false)`, whose list Lean types `List (List (List Nat))`, ...
- `A867`: Polymorphic recursion across a mutual block (`mA n x := mB n [x]`,
  `mB n x := mA n x`, and a block declared the other way round, `nB n x :=
  nA n (x, x)`) is found on the component's ...
- `A869`: (e), two family keys a move relates: the two related keys through
  mutual polymorphic recursion (`evenL n x := oddL n (x, x)`, `oddL n x :=
  evenL n [x]`), each arm calling lenP on pickL.
- `A871`: (b)'s split limit, the boundary below it: one call of a function
  generic in eight keyed lists splits into 256 alternatives, which translate
  within A4's budget.
- `A872`: (b)'s split limit, the boundary above it: nine keyed lists to one
  generic call would split into 512 alternatives, refused as `split-limit`
  (support- status NS17).
- `A874`: A coercion at a by-value structure's slot parameter that a field
  holds under an arrow (`shw : α → String`) wraps that field in the rebuild
  (`DepCo.wrapField`), in an Array of `Pkg<U>` and ...
- `A876`: `List.filter (·.1)` over a list of dependent pairs `(b : Bool) ×
  Nat` printed a move out of the list's `Link` cell -/

namespace A808

structure Pkg where
  α : Type
  val : α
  tag : Nat
def pkgN (n : Nat) : Pkg := ⟨Nat, n, 1⟩
def pkgS (s : String) : Pkg := ⟨String, s, 2⟩
def caseMain (args : List String) : IO UInt32 := do
  let n := args.length
  let ps := [pkgN n, pkgS "hi", pkgN (n * 7)]
  IO.println s!"{(ps.map (·.tag)).foldl (· + ·) 0} {ps.length}"
  return 0
end A808

namespace A817

structure PkgA where
  α : Type
  r : IO.Ref (Nat → α)

@[noinline] def touchA (p : PkgA) : IO Unit := do p.r.set (← p.r.get)
@[noinline] def touchN (r : IO.Ref Nat) : IO Unit := do r.set (← r.get)
@[noinline] def touchS (r : IO.Ref String) : IO Unit := do r.set ((← r.get) ++ "!")
@[noinline] def touchF (r : IO.Ref (Nat → Nat)) : IO Unit := do r.set (← r.get)
@[noinline] def swapN (r : IO.Ref Nat) : IO Nat := do r.swap ((← r.get) + 1)
@[noinline] def swapL (r : IO.Ref (List Nat)) : IO (List Nat) := do
  let old ← r.swap (← r.get)
  return old ++ old
@[noinline] def setTo (r : IO.Ref Nat) (v : Nat) : IO Unit := r.set (v + 1)
@[noinline] def passGet (r : IO.Ref Nat) : IO Nat := do
  setTo r (← r.get)
  setTo r ((← r.get) * 2)
  r.get
@[noinline] def bumpU (r : IO.Ref UInt64) (v : UInt64) : IO Unit := r.set (v + 3)
@[noinline] def passGetU (r : IO.Ref UInt64) : IO UInt64 := do
  bumpU r (← r.get)
  r.modify (· * 2)
  r.get
@[noinline] def two (r1 r2 : IO.Ref (Array Nat)) : IO Unit := do r2.set ((← r1.get).push 1)
@[noinline] def modTwo (r s : IO.Ref Nat) : IO Unit := do r.modify (· + (← s.get))
@[noinline] def loopRef (r : IO.Ref Nat) (n : Nat) : IO Unit := do
  for i in [0:n] do
    r.set ((← r.get) + i)

def caseMain (args : List String) : IO Unit := do
  let k := args.length
  let rf ← IO.mkRef (fun (x : Nat) => x + 1 + k)
  touchA ⟨Nat, rf⟩
  touchF rf
  let rn ← IO.mkRef k
  touchN rn
  let rs ← IO.mkRef s!"s{k}"
  touchS rs
  touchS rs
  let a ← swapN rn
  let rl ← IO.mkRef [k, k + 1]
  let l ← swapL rl
  let p ← passGet rn
  let ru ← IO.mkRef k.toUInt64
  let u ← passGetU ru
  let ra ← IO.mkRef #[k]
  two ra ra
  modTwo rn rn
  loopRef rn (k + 2)
  IO.println s!"{(← rf.get) 41} {← rn.get} {← rs.get} {a} {l} {← rl.get} {p} {u} {← ra.get}"
end A817

namespace A831

structure Pkg where
  α : Type
  val : α
  tag : Nat
@[noinline] def pkgN (n : Nat) : Pkg := ⟨Nat, n, 1⟩
@[noinline] def pkgS (s : String) : Pkg := ⟨String, s, 2⟩
@[noinline] def tags (ps : List Pkg) : Nat := ps.foldl (fun a p => a + p.tag) 0
structure Pkg2 where
  α : Type
  β : Type
  a : α
  b : β
  tag : Nat
@[noinline] def p2a (n : Nat) : Pkg2 := ⟨Nat, String, n, "x", 3⟩
@[noinline] def p2b (s : String) : Pkg2 := ⟨String, Nat, s, 7, 4⟩
@[noinline] def tags2 (ps : Array Pkg2) : Nat := ps.foldl (fun a p => a + p.tag) 0
def caseMain (args : List String) : IO Unit := do
  let z := args.length
  IO.println s!"{tags [pkgN (5 + z), pkgS "hi", pkgN 1]} {tags2 #[p2a z, p2b "q", p2a 2]}"
end A831


namespace A834

namespace LPh
@[noinline] def pickL {α : Type} (b : Bool) (x : α) : if b then List α else List (List α) :=
  match b with | true => [x, x, x] | false => [[x], [x]]
@[noinline] def lenP {α : Type} (b : Bool) (v : if b then List α else List (List α)) : Nat :=
  match b, v with
  | true, xs => xs.length
  | false, xss => xss.length + 10
@[noinline] def viaCaller (b : Bool) (n : Nat) : Nat := lenP b (pickL b n)
@[noinline] def viaCallerS (b : Bool) (s : String) : Nat := lenP b (pickL b s)
@[noinline] def viaGen {β : Type} (b : Bool) (x : β) : Nat := lenP b (pickL b x)
@[noinline] def viaGen2 {β : Type} (b : Bool) (x : β) : Nat := viaGen b [x] + viaGen (!b) x
@[noinline] def asValue (n : Nat) : List Nat :=
  let g : (b : Bool) → (if b then List Nat else List (List Nat)) → Nat := lenP
  [g true (pickL true n), g false (pickL false n)]
@[noinline] def hof (n : Nat) : List Nat := [pickL false n, pickL false (n + 1)].map (lenP false)
@[noinline] def hofPart (n : Nat) : List Nat := [true, false].map fun b => lenP b (pickL b n)
end LPh
def caseMain (args : List String) : IO Unit := do
  let n := args.length
  IO.println s!"{[LPh.viaCaller true n, LPh.viaCaller false n, LPh.viaCallerS true "s", LPh.viaCallerS false "s", LPh.viaGen true (n, n), LPh.viaGen false (n, n)]} {LPh.viaGen2 true n} {LPh.asValue n} {LPh.hof n} {LPh.hofPart n}"
end A834

namespace A867

def pickL (b : Bool) (x : α) : if b then α else List α := match b with | true => x | false => [x, x]
@[noinline] def lenL (b : Bool) (x : α) : Nat := match b with
  | true => 1
  | false => let l : List α := pickL false x; l.length
mutual
@[noinline] def mA (n : Nat) (x : α) : Nat := match n with | 0 => lenL false x | n+1 => mB n [x]
@[noinline] def mB (n : Nat) (x : α) : Nat := match n with | 0 => lenL true x | n+1 => mA n x
end
mutual
@[noinline] def nB (n : Nat) (x : α) : Nat := match n with | 0 => lenL true x | n+1 => nA n (x, x)
@[noinline] def nA (n : Nat) (x : α) : Nat := match n with | 0 => lenL false x | n+1 => nB n x
end
def caseMain (args : List String) : IO Unit := do
  let z := args.length
  IO.println s!"{mA 3 (5 + z : Nat)} {mB 2 "x"} {mA 2 "y"} {mB (3 + z) (7 : Nat)}"
  IO.println s!"{nB 3 (5 + z : Nat)} {nA 2 "x"} {nB 2 "y"} {nA (4 + z) [z]}"
end A867

namespace A869

def Ty : Bool → Type | true => Nat | false => String
def pick : (b : Bool) → Nat → Ty b | true, n => n * 2 | false, n => toString n
def pickL (b : Bool) (x : α) : if b then α else List α := match b with | true => x | false => [x, x]
@[noinline] def lenP {α : Type} (b : Bool) (v : if b then List α else List (List α)) : Nat := match b with
  | true => let l : List α := v; l.length
  | false => let l : List (List α) := v; (l.map List.length).foldl (· + ·) 0
@[noinline] def lenL (b : Bool) (x : α) : Nat := match b with
  | true => 1
  | false => let l : List α := pickL false x; l.length
mutual
@[noinline] def evenL (n : Nat) (x : α) : Nat := match n with | 0 => lenP false (pickL false [x]) | n+1 => oddL n (x, x)
@[noinline] def oddL (n : Nat) (x : α) : Nat := match n with | 0 => lenP true (pickL true [x, x]) | n+1 => evenL n [x]
end
def caseMain (args : List String) : IO Unit := IO.println s!"{evenL 2 (3 + args.length)} {oddL 3 "x"}"
end A869

namespace A871

@[noinline] def foo {a1 a2 a3 a4 a5 a6 a7 a8 : Type} (l1 : List a1) (l2 : List a2) (l3 : List a3) (l4 : List a4) (l5 : List a5) (l6 : List a6) (l7 : List a7) (l8 : List a8) : Nat := l1.length + l2.length + l3.length + l4.length + l5.length + l6.length + l7.length + l8.length
abbrev TL (b : Bool) : Type := if b then List Nat else List (List Nat)
@[noinline] def pickL (b : Bool) (n : Nat) : TL b :=
  match b with | true => [n, n, n] | false => [[n], [n]]
@[noinline] def bar (b : Bool) (x1 x2 x3 x4 x5 x6 x7 x8 : TL b) : Nat :=
  match b with
  | true => foo x1 x2 x3 x4 x5 x6 x7 x8
  | false => foo x1 x2 x3 x4 x5 x6 x7 x8
def caseMain (args : List String) : IO Unit := do
  let b := args.length == 0
  let p := pickL b args.length
  IO.println s!"{bar b p p p p p p p p}"
end A871

namespace A872

@[noinline] def foo {a1 a2 a3 a4 a5 a6 a7 a8 a9 : Type} (l1 : List a1) (l2 : List a2) (l3 : List a3) (l4 : List a4) (l5 : List a5) (l6 : List a6) (l7 : List a7) (l8 : List a8) (l9 : List a9) : Nat := l1.length + l2.length + l3.length + l4.length + l5.length + l6.length + l7.length + l8.length + l9.length
abbrev TL (b : Bool) : Type := if b then List Nat else List (List Nat)
@[noinline] def pickL (b : Bool) (n : Nat) : TL b :=
  match b with | true => [n, n, n] | false => [[n], [n]]
@[noinline] def bar (b : Bool) (x1 x2 x3 x4 x5 x6 x7 x8 x9 : TL b) : Nat :=
  match b with
  | true => foo x1 x2 x3 x4 x5 x6 x7 x8 x9
  | false => foo x1 x2 x3 x4 x5 x6 x7 x8 x9
def caseMain (args : List String) : IO Unit := do
  let b := args.length == 0
  let p := pickL b args.length
  IO.println s!"{bar b p p p p p p p p p}"
end A872

namespace A874

structure Pkg where
  α : Type
  val : α
  shw : α → String
def pkgN (n : Nat) : Pkg := ⟨Nat, n, fun x => s!"nat {x}"⟩
def pkgS (s : String) : Pkg := ⟨String, s, fun x => s!"str {x}"⟩
def render (p : Pkg) : String := p.shw p.val
def caseMain (args : List String) : IO UInt32 := do
  let arr : Array Pkg := #[pkgN args.length] |>.push (pkgS "s")
  let lst : List Pkg := [pkgN (args.length + 1), pkgS "t", pkgN 7]
  IO.println (String.intercalate "," (arr.toList.map render))
  IO.println (String.intercalate "," (lst.map render))
  return 0
end A874

namespace A876

def mkP (i : Nat) : (b : Bool) × Nat := if i % 3 == 0 then ⟨false, i⟩ else ⟨true, i * 10⟩
structure P (α β : Type) where
  a : α
  b : β
def dbl (x : Nat) : Nat := x * 2
def inc (x : Nat) : Nat := x + 1
/-- a `fn`-pointer component is `Copy`, so the pair is read in place -/
def mkF (i : Nat) : (b : Bool) × (Nat → Nat) := if i % 3 == 0 then ⟨false, dbl⟩ else ⟨true, inc⟩
def mkQ (i : Nat) : P Bool Nat := if i % 3 == 0 then ⟨false, i⟩ else ⟨true, i * 10⟩
def caseMain (args : List String) : IO UInt32 := do
  let comp := (List.range (args.length + 5)).map mkP
  let rev := comp.filter (fun p => p.1)
  IO.println s!"{rev.foldl (fun a p => a + p.2) 0}"
  let fs := ((List.range (args.length + 5)).map mkF).filter (fun p => p.1)
  IO.println s!"{fs.foldl (fun a p => a + p.2 3) 0}"
  let qs := ((List.range (args.length + 5)).map mkQ).filter (fun p => p.a)
  IO.println s!"{qs.foldl (fun a p => a + p.b) 0}"
  return 0
end A876

def main : IO Unit := do
  IO.println "-- A808"
  let c ← A808.caseMain ["a", "b", "c"]
  IO.println s!"exit {c}"
  IO.println "-- A817"
  A817.caseMain ["a", "b", "c"]
  IO.println "-- A831"
  A831.caseMain ["a", "b", "c"]
  IO.println "-- A834"
  A834.caseMain ["a", "b", "c"]
  IO.println "-- A867"
  A867.caseMain ["a", "b", "c"]
  IO.println "-- A869"
  A869.caseMain ["a", "b", "c"]
  IO.println "-- A871"
  A871.caseMain ["a", "b", "c"]
  IO.println "-- A872"
  A872.caseMain ["a", "b", "c"]
  IO.println "-- A874"
  let c ← A874.caseMain ["a", "b", "c"]
  IO.println s!"exit {c}"
  IO.println "-- A876"
  let c ← A876.caseMain ["a", "b", "c", "d"]
  IO.println s!"exit {c}"
