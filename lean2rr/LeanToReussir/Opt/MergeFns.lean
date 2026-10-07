import Std.Data.HashMap
import Std.Data.HashSet
import LeanToReussir.RR
import LeanToReussir.PassConfig

/-!
# Generated functions identical up to names, merged (optimization `merge-fns`)

Instances of one Lean definition at different type arguments often lower
to the same Reussir function: with one layout per inductive, `List.reverseAux`
at `String`, at `Nat` and at a structure all pass the head's box on
(Lower's `boxedOnlyVars`), and only their names and their local names
differ. This pass finds the generated functions that are equal once their
own name and their local names (parameters, `let`s, match binders, lambda
parameters, and those names inside atoms) are renamed in order of binding.
In each group the first function stays; each other one keeps its name and
signature and calls the first (`fn f(a, b) -> T { g(a, b) }`, which LLVM
inlines), and every call of it in a function body calls the first one
instead. Callers that become equal through that are merged in the next
round (`List.reverse` once `List.reverseAux` is). A function is never
removed: names in raw items (trampolines) and atoms keep working. A
function called from one place only takes no part (LLVM inlines it into
that place, which it would not do for the merged function several places
call), except code that runs once at startup.
-/

namespace LeanToReussir.Opt.MergeFns
open LeanToReussir.RR

/-- An identifier character (names of variables in atoms). -/
private def idChar (c : Char) : Bool := c.isAlphanum || c == '_'

/-- `t` with each identifier that `m` maps replaced. -/
private def renameAtom (m : Std.HashMap String String) (t : String) : String := Id.run do
  let mut out := ""
  let mut cur := ""
  for c in t.toList do
    if idChar c then cur := cur.push c
    else
      out := out ++ (m.getD cur cur)
      cur := ""
      out := out.push c
  return out ++ (m.getD cur cur)

/-- The renaming state: local names to canonical ones, in binding order. -/
abbrev CanonM := StateM (Std.HashMap String String × Nat)

private def bind (x : String) : CanonM String := do
  let (m, n) ← get
  if let some y := m[x]? then return y
  let y := s!"v{n}"
  set (m.insert x y, n + 1)
  return y

private def look (x : String) : CanonM String := do
  return (← get).1.getD x x

mutual
  /-- `e` with local names canonical and calls of `self` named `SELF`. -/
  partial def canonExpr (self : String) (e : Expr) : CanonM Expr := do
    match e with
    | .var n => return .var (← look n)
    | .atom t => return .atom (renameAtom (← get).1 t)
    | .call f ts args =>
      return .call (if f == self then "SELF" else f) ts (← args.mapM (canonExpr self))
    | .apply f a => return .apply (← canonExpr self f) (← canonExpr self a)
    | .ctor t v args => return .ctor t v (← args.mapM (canonExpr self))
    | .field e i => return .field (← canonExpr self e) i
    | .cast e t => return .cast (← canonExpr self e) t
    | .lam x t b =>
      let x' ← bind x
      return .lam x' t (← canonBlock self b)
    | .ite c t f => return .ite (← canonExpr self c) (← canonBlock self t) (← canonBlock self f)
    | .mtch s arms =>
      let s' ← canonExpr self s
      let arms' ← arms.mapM fun a => do
        let bs ← a.binders.mapM fun b => match b with
          | some x => some <$> bind x
          | none => pure none
        return { a with binders := bs, body := ← canonBlock self a.body }
      return .mtch s' arms'
    | .block b => return .block (← canonBlock self b)

  partial def canonBlock (self : String) (b : Block) : CanonM Block := do
    let mut lets := #[]
    for (x, t, e) in b.lets do
      -- The value first: it cannot see its own name.
      let e' ← canonExpr self e
      lets := lets.push (← bind x, t, e')
    return ⟨lets, ← canonExpr self b.result⟩
end

/-- The canonical text of function `name(ps) -> ret { body }`: equal for
two functions exactly when they are equal up to their own and their local
names. -/
def canonText (name : String) (ps : Array (String × Ty)) (ret : Ty) (body : Block) : String :=
  let act : CanonM Item := do
    let ps' ← ps.mapM fun (x, t) => do return (← bind x, t)
    return .fn "SELF" ps' ret (← canonBlock name body)
  (act.run' ({}, 0)).render

/-- The hashing state: local names to their binding numbers, the next
number, and the hash so far. -/
abbrev HashM := StateM (Std.HashMap String UInt64 × UInt64 × UInt64)

@[inline] private def mix (x : UInt64) : HashM Unit :=
  modify fun (m, n, h) => (m, n, mixHash h x)

@[inline] private def mixStr (t : String) : HashM Unit := mix (hash t)

private def hbind (x : String) : HashM Unit := do
  let (m, n, h) ← get
  match m[x]? with
  | some k => set (m, n, mixHash h k)
  | none => set (m.insert x n, n + 1, mixHash h n)

/-- A name: its binding number if local, else the name itself. -/
private def hname (x : String) : HashM Unit := do
  match (← get).1[x]? with
  | some k => mix (mixHash 7 k)
  | none => mixStr x

/-- A type as Reussir sees it (as it is rendered: function types equal
without their phantom domains, `Ty.rt`, are one type). -/
private def hty (t : Ty) : HashM Unit := mix (hash t.rt)

mutual
  /-- `canonText`'s hash, without building the text: equal canonical texts
  give equal hashes (a group is then checked with `canonText`). -/
  partial def hashExpr (self : String) (e : Expr) : HashM Unit := do
    match e with
    | .var n => mix 1; hname n
    | .atom t =>
      mix 2
      -- Identifiers in the text: locals by number.
      let mut cur := ""
      for c in t.toList do
        if c.isAlphanum || c == '_' then cur := cur.push c
        else
          if !cur.isEmpty then hname cur
          cur := ""
          mix c.toNat.toUInt64
      if !cur.isEmpty then hname cur
    | .call f ts args =>
      mix 3; mixStr (if f == self then "SELF" else f); ts.forM hty; mix args.size.toUInt64
      args.forM (hashExpr self)
    | .apply f a => mix 4; hashExpr self f; hashExpr self a
    | .ctor t v args =>
      mix 5; mixStr t; mixStr (v.getD ""); mix args.size.toUInt64; args.forM (hashExpr self)
    | .field e i => mix 6; mix i.toUInt64; hashExpr self e
    | .cast e t => mix 7; hty t; hashExpr self e
    | .lam x t b => mix 8; hbind x; hty t; hashBlock self b
    | .ite c t f => mix 9; hashExpr self c; hashBlock self t; hashBlock self f
    | .mtch s arms =>
      mix 10; hashExpr self s; mix arms.size.toUInt64
      for a in arms do
        mixStr a.ty; mixStr (a.ctor.getD "_")
        for b in a.binders do
          match b with
          | some x => hbind x
          | none => mix 11
        hashBlock self a.body
    | .block b => mix 12; hashBlock self b

  partial def hashBlock (self : String) (b : Block) : HashM Unit := do
    mix 13; mix b.lets.size.toUInt64
    for (x, t, e) in b.lets do
      hashExpr self e
      hbind x
      match t with
      | some t => hty t
      | none => mix 14
    hashExpr self b.result
end

/-- The hash of function `name(ps) -> ret { body }` (`hashExpr`). -/
def canonHash (name : String) (ps : Array (String × Ty)) (ret : Ty) (body : Block) : UInt64 :=
  let act : HashM Unit := do
    mix ps.size.toUInt64
    for (x, t) in ps do hbind x; hty t
    hty ret
    hashBlock name body
  (act.run ({}, 0, 17)).2.2.2

mutual
  /-- `e` with the calls of the functions `to` maps renamed. -/
  partial def renameCalls (to : Std.HashMap String String) (e : Expr) : Expr :=
    match e with
    | .call f ts args => .call (to.getD f f) ts (args.map (renameCalls to))
    | .apply f a => .apply (renameCalls to f) (renameCalls to a)
    | .ctor t v args => .ctor t v (args.map (renameCalls to))
    | .field e i => .field (renameCalls to e) i
    | .cast e t => .cast (renameCalls to e) t
    | .lam x t b => .lam x t (renameCallsBlock to b)
    | .ite c t f => .ite (renameCalls to c) (renameCallsBlock to t) (renameCallsBlock to f)
    | .mtch s arms => .mtch (renameCalls to s) (arms.map fun a => { a with body := renameCallsBlock to a.body })
    | .block b => .block (renameCallsBlock to b)
    | e => e

  partial def renameCallsBlock (to : Std.HashMap String String) (b : Block) : Block :=
    ⟨b.lets.map fun (x, t, e) => (x, t, renameCalls to e), renameCalls to b.result⟩
end

mutual
  /-- `counts` plus the calls in `e` of functions other than `self`. -/
  partial def countCalls (self : String) (e : Expr) (counts : Std.HashMap String Nat) :
      Std.HashMap String Nat :=
    match e with
    | .call f _ args =>
      let counts := if f == self then counts else counts.insert f (counts.getD f 0 + 1)
      args.foldl (fun c a => countCalls self a c) counts
    | .apply f a => countCalls self a (countCalls self f counts)
    | .ctor _ _ args => args.foldl (fun c a => countCalls self a c) counts
    | .field e _ | .cast e _ => countCalls self e counts
    | .lam _ _ b | .block b => countCallsBlock self b counts
    | .ite c t f => countCallsBlock self f (countCallsBlock self t (countCalls self c counts))
    | .mtch s arms => arms.foldl (fun c a => countCallsBlock self a.body c) (countCalls self s counts)
    | _ => counts

  partial def countCallsBlock (self : String) (b : Block) (counts : Std.HashMap String Nat) :
      Std.HashMap String Nat :=
    countCalls self b.result (b.lets.foldl (fun c (_, _, e) => countCalls self e c) counts)
end

mutual
  /-- Whether `e` calls a function of `fs`. -/
  partial def callsAny (fs : Std.HashMap String String) (e : Expr) : Bool :=
    match e with
    | .call f _ args => fs.contains f || args.any (callsAny fs)
    | .apply f a => callsAny fs f || callsAny fs a
    | .ctor _ _ args => args.any (callsAny fs)
    | .field e _ | .cast e _ => callsAny fs e
    | .lam _ _ b | .block b => callsAnyBlock fs b
    | .ite c t f => callsAny fs c || callsAnyBlock fs t || callsAnyBlock fs f
    | .mtch s arms => callsAny fs s || arms.any (callsAnyBlock fs ·.body)
    | _ => false

  partial def callsAnyBlock (fs : Std.HashMap String String) (b : Block) : Bool :=
    b.lets.any (callsAny fs ·.2.2) || callsAny fs b.result
end

/-- A function recorded as the first of its hash: its name, its item when
recorded (a later renaming of its calls does not change what it computes)
and its canonical text, once a second function with its hash needed it. -/
structure First where
  name : String
  item : Item
  text : Option String := none

/-- The canonical text of a recorded item. -/
def itemText : Item → String
  | .fn n ps r body => canonText n ps r body
  | _ => ""

/-- The pass: rounds of merging until no group is left. Each round looks at
the functions that changed in the previous one (all, the first time).
Functions are bucketed by `canonHash`; texts are compared only within a
bucket. -/
def mergeFns (fns : Array Item) : Array Item := Id.run do
  let mut fns := fns
  -- A function called from one place only (besides its own recursive
  -- calls) stays as it is: LLVM inlines such a function into its caller,
  -- so a merged copy would be one function called from several places,
  -- which it no longer inlines (mergesort's six `splitHalf.go` instances,
  -- each inlined into its `mergeSort`: +2.3 % instructions merged). Code
  -- that runs once at startup merges anyway: a constant's computation
  -- (`_init`) and the persist walks (`l2r_persist_`).
  let calls := fns.foldl (init := ({} : Std.HashMap String Nat)) fun c it => match it with
    | .fn n _ _ body => countCallsBlock n body c
    | _ => c
  let keep (n : String) : Bool :=
    calls.getD n 0 ≤ 1 && !(n.endsWith "_init" || n.startsWith "l2r_persist_")
  -- `rep`: the firsts by hash; `wrapOf`: a merged function (now a
  -- wrapper) to the function it calls.
  let mut rep : Std.HashMap UInt64 (Array First) := {}
  let mut wrapOf : Std.HashMap String String := {}
  let mut todo : Array Nat := (List.range fns.size).toArray
  let mut rounds := 0
  while !todo.isEmpty && rounds < 8 do
    rounds := rounds + 1
    let mut to : Std.HashMap String String := {}
    for i in todo do
      let some it@(.fn n ps r body) := fns[i]? | continue
      if wrapOf.contains n || keep n then continue
      let hk := canonHash n ps r body
      let mut found : Option String := none
      match rep[hk]? with
      | none => rep := rep.insert hk #[{ name := n, item := it }]
      | some bucket =>
        let key := canonText n ps r body
        let mut bucket := bucket
        for j in [:bucket.size] do
          let some f := bucket[j]? | continue
          let t := f.text.getD (itemText f.item)
          bucket := bucket.set! j { f with text := some t }
          if t == key && f.name != n then
            found := some f.name
            break
        if found.isNone then bucket := bucket.push { name := n, item := it, text := some key }
        rep := rep.insert hk bucket
      if let some g := found then
        -- The function that `g` ends at (a first that became a wrapper in a
        -- later round calls another); never `n` itself, which would make
        -- the two call each other.
        let mut t := g
        let mut steps := 0
        while steps < 64 do
          match wrapOf[t]? with
          | some u => t := u; steps := steps + 1
          | none => break
        if t != n && !wrapOf.contains t then
          to := to.insert n t
          wrapOf := wrapOf.insert n t
          fns := fns.set! i (.fn n ps r ⟨#[], .call t #[] (ps.map (Expr.var ·.1))⟩)
    if to.isEmpty then break
    -- Calls of merged functions call their first instead; the callers that
    -- changed are looked at again (their texts change).
    let mut next := #[]
    for i in [:fns.size] do
      match fns[i]? with
      | some (.fn n ps r body) =>
        if wrapOf.contains n then continue
        if callsAnyBlock to body then
          fns := fns.set! i (.fn n ps r (renameCallsBlock to body))
          next := next.push i
      | _ => pure ()
    -- A changed caller may be some group's first: its group keeps it (it
    -- computes what its recorded item did, the renamed calls computing
    -- what the old ones did).
    todo := next
  return fns

end LeanToReussir.Opt.MergeFns

/-- Registry entry point: runs on the generated functions, last. -/
def LeanToReussir.Opt.MergeFns.install (c : LeanToReussir.PassConfig) : LeanToReussir.PassConfig :=
  { c with rrPasses := c.rrPasses.push fun _ fns => LeanToReussir.Opt.MergeFns.mergeFns fns }
