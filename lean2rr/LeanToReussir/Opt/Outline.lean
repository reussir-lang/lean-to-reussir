import Std.Data.HashMap
import Std.Data.HashSet
import Lean.Util.SCC
import LeanToReussir.RR
import LeanToReussir.PassConfig

/-!
# Outlining deep and long function bodies (workaround `outline`)

rrc's per-function analyses grow faster than linearly in two shapes of
code that Lean programs produce routinely (docs/reussir-bugs.md, bugs 16
and 17):
- nesting: every IO bind is a `match` on the action's result whose `ok` arm
  holds the rest of the function, so a `main` of N statements nests N
  matches deep (a 3000-arm literal match nests 3000 `if`s), and reuse across
  calls costs about depth^2.6;
- length: a straight-line body of N `let`s on `Nat` costs memory in N^2.

Reussir has no early return that would let the error checks be flat, so
lean2rr bounds both on its side, after lowering. A tail path of a function
goes through the arms of a `match` or the branches of an `if` that is the
function's result, recursively, and through the rest of a block after a
`let`. A function with a tail path `triggerDepth` levels deep or
`triggerLets` `let`s long is cut: once a path is `maxDepth` levels deep or
`maxLets` `let`s long, the rest of the path becomes a new function of the
variables it uses, called in tail position (its result is the function's
result). Ordinary code is below the triggers and comes out unchanged.
Recursive functions are not cut (see `outlineFns`).

A block is outlined only if every variable it uses has a known type: the
parameters, typed `let`s and the fields of matched variants (from the type
declarations). Otherwise it stays where it is.

This works around rrc's limits; it does not make the program faster.
Without it the output is the same program, but rrc's build time and memory
grow superlinearly on long `main`s and big literal matches.
-/

namespace LeanToReussir.Outline
open RR

/-- Bounds on a tail path (see the module comment). -/
structure Limits where
  /-- A function is cut only if a tail path is this deep… -/
  triggerDepth : Nat := 32
  /-- …or has this many `let`s. -/
  triggerLets : Nat := 256
  /-- Then it is cut into parts of at most this depth… -/
  maxDepth : Nat := 8
  /-- …and this many `let`s on a path. -/
  maxLets : Nat := 64
  /-- A rest of a block shorter than this, with no nested `match`/`if`, is
  left in place. -/
  minRest : Nat := 16

/-- Identifier tokens of an atom's text (`x == k`, `i + one`): atoms can
mention variables. -/
def atomIdents (t : String) : Array String := Id.run do
  let mut out := #[]
  let mut cur := ""
  for c in t.toList do
    if c.isAlphanum || c == '_' then cur := cur.push c
    else
      if !cur.isEmpty then out := out.push cur
      cur := ""
  if !cur.isEmpty then out := out.push cur
  return out.filter fun s => !(s.front.isDigit)

/-- Free variables, in order of first use. -/
structure Fvs where
  order : Array String := #[]
  seen : Std.HashSet String := {}
  /-- Names used as variables (`.var`), as opposed to atom tokens. -/
  vars : Std.HashSet String := {}

def Fvs.add (f : Fvs) (n : String) (isVar : Bool) : Fvs :=
  let f := if isVar then { f with vars := f.vars.insert n } else f
  if f.seen.contains n then f else { f with order := f.order.push n, seen := f.seen.insert n }

mutual
  partial def exprFvs (bound : Std.HashSet String) (e : Expr) (acc : Fvs) : Fvs :=
    match e with
    | .var n =>
      -- `.var` also carries other verbatim operands (`L2RUnit::u{}`).
      if !n.all (fun c => c.isAlphanum || c == '_') then
        (atomIdents n).foldl (fun a n => if bound.contains n then a else a.add n false) acc
      else if bound.contains n then acc else acc.add n true
    | .atom t => (atomIdents t).foldl (fun a n => if bound.contains n then a else a.add n false) acc
    | .call _ _ args => args.foldl (fun a x => exprFvs bound x a) acc
    | .apply f x => exprFvs bound x (exprFvs bound f acc)
    | .ctor _ _ args => args.foldl (fun a x => exprFvs bound x a) acc
    | .field x _ => exprFvs bound x acc
    | .cast x _ => exprFvs bound x acc
    | .lam p _ b => blockFvs (bound.insert p) b acc
    | .ite c t f => blockFvs bound f (blockFvs bound t (exprFvs bound c acc))
    | .mtch s arms => arms.foldl (init := exprFvs bound s acc) fun a arm =>
        blockFvs (arm.binders.foldl (fun bs b => match b with | some n => bs.insert n | none => bs) bound) arm.body a
    | .block b => blockFvs bound b acc
  partial def blockFvs (bound : Std.HashSet String) (b : Block) (acc : Fvs) : Fvs := Id.run do
    let mut bound := bound
    let mut acc := acc
    for (x, _, e) in b.lets do
      acc := exprFvs bound e acc
      bound := bound.insert x
    return exprFvs bound b.result acc
end

/-- The variables in scope at a point of a function: name ↦ (type if
known, binding index). -/
abbrev Env := Std.HashMap String (Option Ty × Nat)

def Env.bind (env : Env) (x : String) (t : Option Ty) : Env := env.insert x (t, env.size)

structure Ctx where
  limits : Limits
  /-- Field types of each variant: (type name, variant) ↦ fields. -/
  variants : Std.HashMap (String × String) (Array Ty)

structure St where
  /-- Function names in use. -/
  taken : Std.HashSet String
  /-- The outlined functions. -/
  out : Array Item := #[]

abbrev M := ReaderT Ctx (StateM St)

/-- Whether a tail block goes on: it nests a `match`/`if`, or has at least
`minRest` `let`s. -/
partial def heavy (minRest : Nat) (b : Block) : Bool :=
  b.lets.size ≥ minRest || match b.result with
    | .mtch .. | .ite .. => true
    | .block b' => heavy (minRest - b.lets.size) b'
    | _ => false

/-- A new function name: the original function's, with a part number. -/
def freshName (base : String) : M String := do
  let base := ((base.splitOn "_l2rpart").head!)
  let mut k := 0
  repeat
    let n := s!"{base}_l2rpart{k}"
    unless (← get).taken.contains n do
      modify fun s => { s with taken := s.taken.insert n }
      return n
    k := k + 1
  return base

mutual
  /-- Process a tail block of the function `fname` (result type `ret`) at
  `depth` levels and `lets` lets from the function's start. -/
  partial def walkBlock (fname : String) (ret : Ty) (env : Env) (depth lets : Nat) (b : Block) : M Block := do
    let lim := (← read).limits
    let mut env := env
    for h : i in [:b.lets.size] do
      if lets + i ≥ lim.maxLets && i > 0 then
        let rest : Block := ⟨b.lets.extract i b.lets.size, b.result⟩
        if heavy lim.minRest rest then
          if let some call ← outline fname ret env rest then
            return ⟨b.lets.extract 0 i, call⟩
      let (x, t, _) := b.lets[i]
      env := env.bind x t
    let lets := lets + b.lets.size
    let result ← match b.result with
      | .mtch s arms =>
        let vs := (← read).variants
        let arms ← arms.mapM fun arm => do
          let fields := match arm.ctor with
            | some c => vs.getD (arm.ty, c) #[]
            | none => #[]
          let env' := arm.binders.zipIdx.foldl (init := env) fun e (bnd, j) => match bnd with
            | some n => e.bind n fields[j]?
            | none => e
          return { arm with body := ← walkTail fname ret env' (depth + 1) lets arm.body }
        pure (Expr.mtch s arms)
      | .ite c t f => pure (.ite c (← walkTail fname ret env (depth + 1) lets t) (← walkTail fname ret env (depth + 1) lets f))
      | .block b' => pure (.block (← walkBlock fname ret env depth lets b'))
      | e => pure e
    return ⟨b.lets, result⟩

  /-- A tail block one level deeper: outlined once the path is too deep. -/
  partial def walkTail (fname : String) (ret : Ty) (env : Env) (depth lets : Nat) (b : Block) : M Block := do
    let lim := (← read).limits
    if depth ≥ lim.maxDepth && heavy lim.minRest b then
      if let some call ← outline fname ret env b then
        return .ofExpr call
    walkBlock fname ret env depth lets b

  /-- Make `b` a new function of the variables it uses and return the call,
  or `none` if one of them has no known type. -/
  partial def outline (fname : String) (ret : Ty) (env : Env) (b : Block) : M (Option Expr) := do
    let fv := blockFvs {} b {}
    let mut params : Array (String × Ty × Nat) := #[]
    for n in fv.order do
      match env[n]? with
      | some (some t, k) => params := params.push (n, t, k)
      | some (none, _) => return none
      | none => if fv.vars.contains n then return none
    let ps := params.qsort fun a b => a.2.2 < b.2.2
    let name ← freshName fname
    let env' : Env := ps.foldl (fun e (n, t, _) => e.bind n (some t)) {}
    let body ← walkBlock name ret env' 0 0 b
    modify fun s => { s with out := s.out.push (.fn name (ps.map fun (n, t, _) => (n, t)) ret body) }
    return some (.call name #[] (ps.map fun (n, _, _) => .var n))
end

/-- Field types of the variants of the enums declared by `items` and by the
prelude's source (`enum [value] Nat { Small(u64), Big(LBig) }`). -/
def variantTable (items : Array Item) (prelude : String) : Std.HashMap (String × String) (Array Ty) := Id.run do
  let mut out : Std.HashMap (String × String) (Array Ty) := {}
  for it in items do
    if let .enum n _ vs := it then
      for (v, fs) in vs do out := out.insert (n, v) fs
  let mut cur : Option String := none
  for line in prelude.splitOn "\n" do
    let l := line.trimAscii.toString
    let l := if l.startsWith "pub " then (l.drop 4).toString else l
    if l.startsWith "enum " then
      let rest := (l.drop 5).toString
      let rest := if rest.startsWith "[value] " then (rest.drop 8).toString else rest
      let name := (rest.takeWhile fun c => c.isAlphanum || c == '_').toString
      -- Generic enums (`enum Foo<T>`) are skipped: their field types depend
      -- on the instance.
      cur := if (rest.drop name.length).toString.trimAscii.startsWith "{" then some name else none
    else if l.startsWith "}" then cur := none
    else if let some n := cur then
      let l := if l.endsWith "," then (l.dropEnd 1).toString else l
      let v := (l.takeWhile fun c => c.isAlphanum || c == '_').toString
      if v.isEmpty then continue
      let inner := (l.drop v.length).toString.trimAscii.toString
      if inner.isEmpty then out := out.insert (n, v) #[]
      else if inner.startsWith "(" && inner.endsWith ")" then
        let args := ((inner.drop 1).dropEnd 1).toString
        -- Top-level commas only.
        let (parts, last, _) := args.foldl (init := (#[], "", 0)) fun (ps, c, d) ch =>
          if ch == ',' && d == 0 then (ps.push c, "", d)
          else (ps, c.push ch, if ch == '<' || ch == '(' then d + 1 else if ch == '>' || ch == ')' then d - 1 else d)
        match (parts.push last).toList.mapM parseTy with
        | some tys => out := out.insert (n, v) tys.toArray
        | none => pure ()
  return out

mutual
  /-- The functions an expression calls. -/
  partial def exprCalls (e : Expr) (acc : Array String) : Array String :=
    match e with
    | .var _ | .atom _ => acc
    | .call f _ args => args.foldl (fun a x => exprCalls x a) (acc.push f)
    | .apply f x => exprCalls x (exprCalls f acc)
    | .ctor _ _ args => args.foldl (fun a x => exprCalls x a) acc
    | .field x _ | .cast x _ => exprCalls x acc
    | .lam _ _ b | .block b => blockCalls b acc
    | .ite c t f => blockCalls f (blockCalls t (exprCalls c acc))
    | .mtch s arms => arms.foldl (fun a arm => blockCalls arm.body a) (exprCalls s acc)
  partial def blockCalls (b : Block) (acc : Array String) : Array String :=
    exprCalls b.result (b.lets.foldl (fun a (_, _, e) => exprCalls e a) acc)
end

/-- The functions of the call graph `callees` that can reach themselves. -/
def recursiveFns (callees : Std.HashMap String (Array String)) : Std.HashSet String := Id.run do
  let comps := Lean.SCC.scc (callees.toList.map (·.1)) fun f => ((callees.getD f #[]).filter callees.contains).toList
  let mut out : Std.HashSet String := {}
  for c in comps do
    match c with
    | [f] => if (callees.getD f #[]).contains f then out := out.insert f
    | _ => for f in c do out := out.insert f
  return out

/-- The depth and the number of `let`s of a block's deepest and longest
tail paths. -/
partial def extent (b : Block) : Nat × Nat :=
  let (d, l) := match b.result with
    | .mtch _ arms => arms.foldl (init := (0, 0)) fun (d, l) arm =>
        let (d', l') := extent arm.body
        (max d (d' + 1), max l l')
    | .ite _ t f =>
        let (d1, l1) := extent t
        let (d2, l2) := extent f
        (max d1 d2 + 1, max l1 l2)
    | .block b' => extent b'
    | _ => (0, 0)
  (d, l + b.lets.size)

/-- Outline the deep and long tail paths of every function of `fns`
(`taken`: every function name of the program). Returns the functions, each
followed by the functions outlined from it. -/
def outlineFns (limits : Limits) (variants : Std.HashMap (String × String) (Array Ty))
    (taken : Std.HashSet String) (fns : Array Item) : Array Item := Id.run do
  -- Recursive functions are left alone: LLVM turns a self tail call into a
  -- loop, but not a cycle of tail calls through the parts (they are not
  -- always sibling calls), so a loop would use stack per iteration.
  let mut callees : Std.HashMap String (Array String) := {}
  for it in fns do
    if let .fn name _ _ body := it then callees := callees.insert name (blockCalls body #[])
  let recursive := recursiveFns callees
  let mut st : St := { taken }
  let mut out := #[]
  for it in fns do
    match it with
    | .fn name ps ret body =>
      let (d, l) := extent body
      if (d < limits.triggerDepth && l < limits.triggerLets) || recursive.contains name then
        out := out.push it
        continue
      let env : Env := ps.foldl (fun e (n, t) => e.bind n (some t)) {}
      let (body, st') := ((walkBlock name ret env 0 0 body).run { limits, variants }).run { st with out := #[] }
      out := out.push (.fn name ps ret body) ++ st'.out
      st := st'
    | _ => out := out.push it
  return out

/-- Every function name of the program: the prelude's (`preludeFns`) and
those of `fns` (including the functions of raw items). -/
def takenNames (preludeFns : Std.HashSet String) (fns : Array Item) : Std.HashSet String :=
  fns.foldl (init := preludeFns) fun acc it => match it with
    | .fn n .. => acc.insert n
    | .raw t => (t.splitOn "fn ").foldl (init := acc) fun acc chunk =>
      let name := chunk.takeWhile fun c => c.isAlphanum || c == '_'
      if name.isEmpty then acc else acc.insert name.toString
    | _ => acc

/-- Registry entry point: runs on the generated functions, after the
passes registered before it. -/
def install (c : PassConfig) : PassConfig :=
  { c with rrPasses := c.rrPasses.push fun p fns =>
      outlineFns {} (variantTable p.types p.prelude) (takenNames p.preludeFns fns) fns }

end LeanToReussir.Outline
