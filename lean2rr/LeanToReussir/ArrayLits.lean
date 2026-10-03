import Std.Data.HashMap
import LeanToReussir.RR

/-!
# `Array Nat` literals as tables

A literal `#[e₁, …, eₙ]` of type `Array Nat` reaches the generated code
(once its chain of closed terms is spliced, `Emit/Program`'s
`spliceChainConsts`) as `n` pairs

```
let x : Nat = l2r_nat_small(k);
let r : LNatArr = lean_natarr_push(a, x);
```

rrc costs time and memory for each of them (about 0.3 MB per `Nat`
operation, docs/reussir-bugs.md bug 17), so a run of such pairs, each `x`
and each intermediate `r` used only there, becomes one call
`l2r_natarr_lits(a, id)` that pushes the words of table `id` (generated with
the program: `natLitTable`), the same elements in the same order. The
runtime stores a small `Nat` as the word `2k + 1`. Runs shorter than
`minRun` stay as they are.
-/

namespace LeanToReussir.ArrayLits
open RR

/-- The shortest run made a table. -/
def minRun : Nat := 32

/-- Identifier tokens of an atom's text (`x == k`). -/
def atomIdents (t : String) : Array String := Id.run do
  let mut out := #[]
  let mut cur := ""
  for c in t.toList do
    if c.isAlphanum || c == '_' then cur := cur.push c
    else
      if !cur.isEmpty then out := out.push cur
      cur := ""
  if !cur.isEmpty then out := out.push cur
  return out

mutual
  /-- Count the uses of every variable of `e`. -/
  partial def exprUses (e : Expr) (acc : Std.HashMap String Nat) : Std.HashMap String Nat :=
    let bump (acc : Std.HashMap String Nat) (n : String) := acc.insert n (acc.getD n 0 + 1)
    match e with
    | .var n => if n.all (fun c => c.isAlphanum || c == '_') then bump acc n else (atomIdents n).foldl bump acc
    | .atom t => (atomIdents t).foldl bump acc
    | .call _ _ args | .ctor _ _ args => args.foldl (fun a x => exprUses x a) acc
    | .apply f x => exprUses x (exprUses f acc)
    | .field x _ | .cast x _ => exprUses x acc
    | .lam _ _ b | .block b => blockUses b acc
    | .ite c t f => blockUses f (blockUses t (exprUses c acc))
    | .mtch s arms => arms.foldl (fun a arm => blockUses arm.body a) (exprUses s acc)
  partial def blockUses (b : Block) (acc : Std.HashMap String Nat) : Std.HashMap String Nat :=
    exprUses b.result (b.lets.foldl (fun a (_, _, e) => exprUses e a) acc)
end

/-- The word of a small `Nat` literal `let x : Nat = l2r_nat_small(k)`. -/
def smallLit? : Option Ty × Expr → Option UInt64
  | (some (.named "Nat"), .call "l2r_nat_small" #[] #[.atom k]) =>
    match k.toNat? with
    | some v => if v < 2 ^ 63 then some (UInt64.ofNat (2 * v + 1)) else none
    | none => none
  | _ => none

/-- The runs of `lets` made tables (see the module comment), with the
tables appended to `tables`. -/
def tableLets (uses : Std.HashMap String Nat) (lets : Array (String × Option Ty × Expr))
    (tables : Array (Array UInt64)) : Array (String × Option Ty × Expr) × Array (Array UInt64) := Id.run do
  let n := lets.size
  let mut out := #[]
  let mut tables := tables
  let mut i := 0
  while i < n do
    let mut j := i
    let mut words : Array UInt64 := #[]
    let mut input := ""
    let mut prev := ""
    while j + 1 < n do
      let (x, tx, ex) := lets[j]!
      let (r, tr, er) := lets[j + 1]!
      let some w := smallLit? (tx, ex) | break
      unless tr == some (.named "LNatArr") && uses.getD x 0 == 1 do break
      let .call "lean_natarr_push" #[] #[.var a, .var x'] := er | break
      unless x' == x do break
      if words.isEmpty then input := a
      else unless a == prev && uses.getD prev 0 == 1 do break
      words := words.push w
      prev := r
      j := j + 2
    if words.size ≥ minRun then
      out := out.push (prev, some (.named "LNatArr"),
        .call "l2r_natarr_lits" #[] #[.var input, .atom (toString tables.size)])
      tables := tables.push words
      i := j
    else
      out := out.push lets[i]!
      i := i + 1
  return (out, tables)

/-- Make the runs of pushed small `Nat` literals in the top-level `let`s of
every function of `fns` tables. Returns the functions and the tables. -/
def natArrLits (fns : Array Item) : Array Item × Array (Array UInt64) := Id.run do
  let mut tables := #[]
  let mut out := #[]
  for it in fns do
    match it with
    | .fn name ps ret body =>
      -- Only a function with such a run is looked at closely.
      let candidate := body.lets.size ≥ 2 * minRun && body.lets.any fun (_, _, e) =>
        e matches .call "lean_natarr_push" #[] _
      if !candidate then
        out := out.push it
        continue
      let (lets, ts) := tableLets (blockUses body {}) body.lets tables
      tables := ts
      out := out.push (.fn name ps ret ⟨lets, body.result⟩)
    | _ => out := out.push it
  return (out, tables)

/-- The runtime function behind `natArrLits`: the tables as Rust arrays of
words, pushed onto the given array. -/
def natLitTable (tables : Array (Array UInt64)) : String :=
  let rows := tables.toList.map fun t => "&[" ++ ", ".intercalate (t.toList.map toString) ++ "]"
  "#[ffi(import)]\nfn l2r_natarr_lits(a : LNatArr, id : u64) -> LNatArr [{ {\n" ++
  s!"    const LITS: &[&[u64]] = &[{", ".intercalate rows}];\n" ++
  "    let mut a = a;\n" ++
  "    for &w in LITS[id as usize] { a = leanrt::tagvec::push_word(a, w); }\n" ++
  "    a\n} }];\n"

end LeanToReussir.ArrayLits
