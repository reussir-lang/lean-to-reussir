/-! Runtime test: two casts through a `Box` to `F2` (plan §5.1, §10 "Casts
that natively read an address"), whose conversions both need `T1`→`T2` (a
tree: two recursive fields, so `convMachine`, which also adds two enum
types) and `Q1`→`Q2` (inside an array field, `vecConv`), generated inside
`boxCastConv`'s probes. `F1`'s conversion also needs a function value at
another representation (its field `f`). Its probe used to be undone, which
cut the functions and types it had generated (eight and two) back off the
emitted items and their names out of the function index, and `H1`'s, kept,
generated them anew; a rollback that left a name in the index, or a type or
function behind, failed the build (review R9S2R-04, program R9Probe9).
Since review CLR-01 a cast that needs a wrapper converts too: both are kept
and both run here. A probe is now undone only for a cast that has no
conversion after it registered function-value helpers. `conv-count-check.sh`
also builds this program with the conversion counter. -/
structure Pkg where
  α : Type
  v : α

inductive T1 | leaf | node (l : T1) (x : Nat) (r : T1)
inductive T2 | leaf | node (l : T2) (y : Int) (r : T2)
inductive Q1 | a | b (x : Nat) (r : Q1)
inductive Q2 | a | b (y : Int) (r : Q2)

structure F1 where
  t : T1
  a : Array Q1
  f : Nat → T1
structure H1 where
  t : T1
  a : Array Q1
  f : Nat → T2
structure F2 where
  t : T2
  a : Array Q2
  f : Nat → T2

def T2.sum : T2 → Nat
  | .leaf => 0
  | .node l y r => l.sum + y.toNat + r.sum
def Q2.sum : Q2 → Nat
  | .a => 0
  | .b y r => y.toNat + r.sum

@[noinline] unsafe def asF2 (p : Pkg) : Nat := match (unsafeCast p.v : F2) with
  | ⟨t, a, f⟩ => t.sum + a.foldl (fun n q => n + q.sum) 0 + (f 3).sum

@[noinline] def pkgF (t : T1) (a : Array Q1) : Pkg := ⟨F1, ⟨t, a, fun n => .node .leaf n .leaf⟩⟩
@[noinline] def pkgH (t : T1) (a : Array Q1) : Pkg := ⟨H1, ⟨t, a, fun n => .node .leaf (Int.ofNat n) .leaf⟩⟩

unsafe def main (args : List String) : IO Unit := do
  let k := args.length
  let t : T1 := .node (.node .leaf 1 .leaf) (40 + k) (.node .leaf 2 .leaf)
  let a : Array Q1 := #[.b 5 .a, .b (6 + k) (.b 7 .a)]
  IO.println s!"F {asF2 (pkgF t a)}"
  IO.println s!"H {asF2 (pkgH t a)}"
