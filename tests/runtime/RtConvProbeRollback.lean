/-! Runtime test: two casts through a `Box` to `F2` (plan §5.1, §10 "Casts
that natively read an address"), of an `F1` and of an `H1`. Both
conversions are generated inside the unboxing function to `F2`
(`genUnbox`) and need the same helpers: `T1`→`T2` (a tree: two recursive
fields, a `structConv` that calls itself) and, for each element of the
array field (an array of boxes, one `Array` type), `Q1`→`Q2` in the
unboxing function to `Q2`; `F1`'s also needs a function value at another
representation (its field `f`: a wrapper and its conversion). The test
used to guard the rollback of a cast's probe (`boxCastConv`: a rollback
that left a name in the function index, or a type or function behind,
failed the build; review R9S2R-04, program R9Probe9). The rollback is gone,
since no cast that `boxCastable` accepts registers a helper and then fails
(review of rule 1, simplicity finding 1): the test now checks that both
conversions run, with helpers that the first one generates and the second
one reuses. `conv-count-check.sh` also builds this program with the
conversion counter. -/
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
