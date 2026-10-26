import LeanToReussir.Lower.Hooks

/-! # Code -/

namespace LeanToReussir
open Lean Compiler LCNF

/-- `f` folded over the free occurrences of variable names in an RR
expression/block, in the order in which they occur in its text. -/
partial def rrFoldFree {α : Type} (f : α → String → α) (e : RR.Expr) (bound : Std.HashSet String) (acc : α) : α :=
  match e with
  | .var n => if bound.contains n || n.startsWith "L2RUnit" then acc else f acc n
  | .atom _ => acc
  | .call _ _ args => args.foldl (fun acc a => rrFoldFree f a bound acc) acc
  | .apply fn a => rrFoldFree f a bound (rrFoldFree f fn bound acc)
  | .ctor _ _ args => args.foldl (fun acc a => rrFoldFree f a bound acc) acc
  | .field e _ => rrFoldFree f e bound acc
  | .cast e _ => rrFoldFree f e bound acc
  | .lam x _ b => block f b (bound.insert x) acc
  | .ite c t e => block f e bound (block f t bound (rrFoldFree f c bound acc))
  | .mtch s arms => arms.foldl (fun acc arm =>
      let bound := arm.binders.foldl (fun b x => match x with | some x => b.insert x | none => b) bound
      block f arm.body bound acc) (rrFoldFree f s bound acc)
  | .block b => block f b bound acc
where
  block (f : α → String → α) (b : RR.Block) (bound : Std.HashSet String) (acc : α) : α :=
    let (bound, acc) := b.lets.foldl (fun (bound, acc) (x, _, e) => (bound.insert x, rrFoldFree f e bound acc)) (bound, acc)
    rrFoldFree f b.result bound acc

/-- Free variable names of an RR expression/block (for outlined join points). -/
def rrFreeVars (e : RR.Expr) (bound : Std.HashSet String) (acc : Std.HashSet String) : Std.HashSet String :=
  rrFoldFree (·.insert ·) e bound acc

def rrFreeVars.blockFreeVars (b : RR.Block) (bound : Std.HashSet String) (acc : Std.HashSet String) :
    Std.HashSet String :=
  rrFoldFree.block (·.insert ·) b bound acc

/-- The free variable names of the blocks `bs` (`rrFreeVars`; block `i`
with the names `bound[i]` bound), each once, in the order of their first
occurrence: the first block's text first. An order that depends only on
the code, not on the names: lean2rr numbers its names with one counter for
the whole program, so an order by name changes when an unrelated
definition is added (determinism-check). -/
def rrFreeVarsInOrder (bs : Array (RR.Block × Std.HashSet String)) : Array String :=
  let add (acc : Array String × Std.HashSet String) (n : String) :=
    if acc.2.contains n then acc else (acc.1.push n, acc.2.insert n)
  (bs.foldl (fun acc (b, bound) => rrFoldFree.block add b bound acc) (#[], {})).1

/-- The names of the conversions `bindField` made for field parameters
`ps` (`CodeCtx.fieldConv`), in context `ctx` right after the binding. -/
def fieldConvNames (ctx : CodeCtx) (ps : Array FVarId) : Std.HashSet String :=
  ps.foldl (fun acc p => match ctx.fieldConv[p]? with
    | some y => acc.insert y
    | none => acc) {}

/-- The `lets` that bind an alternative's fields (projections, and the
conversions `bindField` made: the names `convs`), without the conversions
that the alternative's code `body` does not use. Every site that binds
fields filters them so: enum and structure alternatives (`lowerCases`) and
Opt/LazyFields' later bindings. -/
def dropUnusedConvs (lets : ArmLets) (convs : Std.HashSet String) (body : RR.Block) : ArmLets :=
  if !lets.any (convs.contains ·.1) then lets else
  let free := rrFreeVars.blockFreeVars body {} {}
  lets.filter fun (y, _, _) => !convs.contains y || free.contains y

/-- The value of the `Nat` or `Int` constant `f` (a declaration without
parameters), if its code computes it from literals: a `Nat` literal (Lean
folds `Nat` arithmetic on literals), `Int.ofNat` or `Int.negSucc` of one,
`Int.neg`, `Int.add`, `Int.sub`, `Int.mul` and `Int.pow` (an exponent of at
most 64, a base below 2^64 in magnitude) of such values, and reads of other
such constants (up to `fuel` deep). Lean does not fold `Int` arithmetic:
`-7 : Int` is `Int.neg` of the closed term `Int.ofNat 7`, and `2 ^ 40 :
Int` is `Int.pow`. -/
partial def constNumValue? (f : Name) (fuel : Nat := 8) : LowerM (Option Int) := do
  let some { params := #[], value := .code body, .. } := (← read).decls.find? f | return none
  let keys := (← read).keys
  let declOf (g : Name) : Name := ((keys.find? g).map (·.decl)).getD g
  let rec go (c : Code .pure) (vals : Std.HashMap FVarId Int) : LowerM (Option Int) := do
    match c with
    | .let d k =>
      let arg (a : Arg .pure) : Option Int := match a with
        | .fvar x => vals[x]?
        | _ => none
      let v? ← match d.value with
        | .lit (.nat n) => pure (some (n : Int))
        | .const g _ #[] _ => if fuel > 0 then constNumValue? g (fuel - 1) else pure none
        | .const g _ #[a] _ => pure <| do
          let x ← arg a
          match declOf g with
          | ``Int.ofNat => some x
          | ``Int.negSucc => some (-x - 1)
          | ``Int.neg => some (-x)
          | _ => none
        | .const g _ #[a, b] _ => pure <| do
          let x ← arg a
          let y ← arg b
          match declOf g with
          | ``Int.add => some (x + y)
          | ``Int.sub => some (x - y)
          | ``Int.mul => some (x * y)
          | ``Int.pow => if 0 ≤ y && y ≤ 64 && x.natAbs < 2 ^ 64 then some (x ^ y.toNat) else none
          | _ => none
        | _ => pure none
      go k (match v? with | some v => vals.insert d.fvarId v | none => vals)
    | .return x => return vals[x]?
    | _ => return none
  go body {}

/-- Whether constant `f`'s value is a literal that a box holds as an
immediate: its code returns a `UInt8`/`UInt16`/`UInt32` literal or a
`UInt64`/`USize` literal below 2^63, possibly through other such constants
(up to `fuel` deep); or it is a `Nat` or `Int` constant whose value
(`constNumValue?`) the box holds as an immediate (`natBoxIsImmediate`,
`intBoxIsImmediate`: the box of any other value is a new cell,
`boxAllocates`, so `boxed-consts` boxes such a constant once). -/
partial def constIsImmediate (f : Name) (fuel : Nat := 8) : LowerM Bool := do
  let some { params := #[], value := .code body, type, .. } := (← read).decls.find? f | return false
  if type.isConstOf ``Nat || type.isConstOf ``Int then
    let some v ← constNumValue? f fuel | return false
    if type.isConstOf ``Nat then return v ≥ 0 && natBoxIsImmediate v.toNat
    return intBoxIsImmediate v
  let rec go (c : Code .pure) (vals : Std.HashMap FVarId (LetValue .pure)) : LowerM Bool := do
    match c with
    | .let d k => go k (vals.insert d.fvarId d.value)
    | .return x =>
      match vals[x]? with
      | some (.lit (.uint64 n)) | some (.lit (.usize n)) => return n.toNat < 2 ^ 63
      | some (.lit (.uint8 _)) | some (.lit (.uint16 _)) | some (.lit (.uint32 _)) => return true
      | some (.const g _ #[] _) => return fuel > 0 && (← constIsImmediate g (fuel - 1))
      | _ => return false
    | _ => return false
  go body {}

/-- The value `e` of a `let` with Lean value `v`, if boxing treats it as
native Lean does (`boxOf`, `LowerState.closedLets`): a placeholder (`◾`,
`zeroValue`), a call of a declaration of the program without parameters
(a constant or closed term, cached in a once-cell or recomputed by
`cheap-consts`, which cannot trace or panic), or a `UInt64`/`USize`
literal from 2^63 (smaller ones are immediates). Not a closed term
evaluated where it is used (`uncachedConsts`): calling it again for its
box would run it twice (a trace, a panic). -/
def closedLetValue (v : LetValue .pure) (e : RR.Expr) : LowerM (Option RR.Expr) := do
  match v, e with
  | .erased, .call _ #[] #[] => return some e
  | .const f _ #[] _, .call _ #[] #[] =>
    if (← read).uncachedConsts.contains f then return none
    match (← read).decls.find? f with
    | some { params := #[], value := .code _, .. } =>
      -- A constant whose value is a literal that boxes as an immediate
      -- (`def k : UInt64 := 77`, `def k : Nat := 5`): boxed
      -- in line, which LLVM folds, not read from a once-cell.
      if ← constIsImmediate f then return none
      return some e
    | _ => return none
  | .lit (.uint64 n), .atom _ | .lit (.usize n), .atom _ =>
    return if n.toNat ≥ 2 ^ 63 then some e else none
  | _, _ => return none

section
variable (H : LowerHooks)

/-- The call that tail call `let x := f args; return x` (at the result type
of the code) becomes in context `ctx`, if it enters a state machine (J4,
translation plan §5.6):
- in a state machine, a tail call of its declaration re-enters it at the
  entry, and one of another declaration of its cycle of tail calls at that
  declaration's variant (`StateMachine.members`): a self tail call of the
  dispatching function, which LLVM turns into a loop;
- in a declaration's own function, or in its arm of the cycle's light
  state machine, a tail call of another declaration of its cycle calls that
  declaration's entry function (`StateMachine.entryFn`, `SmMember.entryFn`)
  of the first state machine of `CodeCtx.cycles` that has it, where the
  cycle then runs.
A tail call of another declaration than the one whose code it is
(`CodeCtx.decl`) stays a call when the caller keeps an argument until it
returns (`borrowKeeps`, Lower/Borrow): natively no tail call either (Lean's
borrow inference keeps tail calls only for calls of the declaration itself,
`InferBorrow.preserveTailCall`). -/
def tailCallEntry (ctx : CodeCtx) (f : Name) (args : Array (Arg .pure)) : LowerM (Option RR.Expr) := do
  let inMachine : Option (Nat × (Array RR.Expr → LowerM RR.Expr)) := ctx.sm.bind fun sm =>
    if f == sm.self then some (sm.arity, H.stateMachine.selfCall sm)
    else (sm.members.find? (·.name == f)).map fun mb => (mb.arity, H.stateMachine.jumpCall sm mb.variant)
  let intoCycle : Option (Nat × (Array RR.Expr → LowerM RR.Expr)) :=
    if f == ctx.decl then none else ctx.cycles.findSome? fun cy =>
      let call (fn : String) (vals : Array RR.Expr) : LowerM RR.Expr := pure (.call fn #[] vals)
      if f == cy.self then some (cy.arity, call cy.entryFn)
      else (cy.members.find? (·.name == f)).map fun mb => (mb.arity, call mb.entryFn)
  let some (arity, enter) := inMachine <|> intoCycle | return none
  if args.size != arity then return none
  if f != ctx.decl then
    unless (← borrowKeeps ctx f args args.size).isEmpty do return none
  let some fd := (← read).decls.find? f | throwError "lean2rr: no declaration {f}"
  let (ps, _) := splitFnType fd.type args.size
  -- Rule 4a: the arguments of the parameters it takes.
  let keep := keepMask (fd.params.map (·.type))
  let mut vals := #[]
  for h : i in [:min args.size ps.size] do
    if keep[i]?.getD true then vals := vals.push (← lowerArg ctx args[i]! (← lowerType ps[i]!))
  return some (← enter vals)

/-! ## Indices after a proved access (`rebindIndex`)

An access at a `Nat` index that a proof keeps below the size
(`boundedIndexSyms`: `a[i]'h`, `ByteArray.get`, `a.set i x h`,
`ByteArray.set`, `a.swap i j`) returns only when the index is below the
size: its prelude twin at the index word ends the program otherwise. So
after the `let` of the access, the index is the word, far below 2^60, the
mask's bound (sizes are bounded by the address space).
When the index is a variable used again later, the let-run binds its word
before the `let` (`bindReadIndex` gives it, `LowerState.indexWords`) and,
after it, `l2r_nat_of_index(k)` (the word masked to 60 bits, as a `Nat`)
in place of the variable for the rest of the code:

```
let ix749 : u64 = l2r_nat_index(a747);
let x750 : u32 = lean_array_fget_w<u32>(a745, ix749);
let ib751 : Nat = l2r_nat_of_index(ix749);
```

LLVM then knows that the index is an rcgmp immediate and that adding a
small constant to it gives one: `i + 1` has no tag test and no overflow
path, a later access at it no tag test, and a copy of it no count. The
`Nat` itself would keep the access's big path, which rejoins after the
access (a `Nat` in [2^61, 2^63) is a heap value whose word is valid), so
every later use tested its tag again.

One exception (`loopCarriedAdds`, `CodeCtx.loopAdds`): a loop-carried
increment, `let z := Nat.add y l` with `l` a literal, `y` the
declaration's parameter at position `k` and `z` the argument at position
`k` of a self tail call, reads `y` itself (the name it had before the
rebinding, `CodeCtx.indexOrig`):

```
let x765 : Nat = lean_nat_add(a747, x764);
let x766 : Tuple742 = qpartition_loop(a743, a744, a745, a746, x765);
```

The next iteration's index then depends on this one's through one add
on the tagged value (`adds x, x, #4` and the overflow branch), where the
rebinding made it four instructions longer (`asr`, `lsl`, `and`, `add`):
X07's partition loop, whose step is that chain, ran 10% longer. Every
other use keeps the rebinding; an increment used elsewhere too still
reads `y`. Applied to every increment of a rebound index, Z01c ran 4%
longer. A self tail call that re-enters a state machine counts; the body
of an outlined join point or of a local function reads no name from
before a rebinding (`indexOrig` is empty there: the name may not be
captured). (A join point's parameter is never loop-carried in LCNF: a
jump to a join point occurs only in its continuation, not in its body.) -/

/-- The loop-carried increments of declaration `self` (parameters
`params`, code `body`): each `let z := Nat.add y l` or `Nat.add l y`, `l`
bound to a `Nat` literal, `y` the parameter at a position `k` where a self
tail call (`let r := self args; return r`) passes `z`, mapped to `y`
(`CodeCtx.loopAdds`). Binders are unique, so one pass over the code
collects them. -/
partial def loopCarriedAdds (keys : NameMap InstKey) (self : Name) (params : Array (Param .pure))
    (body : Code .pure) : Std.HashMap FVarId FVarId := Id.run do
  let pos : Std.HashMap FVarId Nat := params.zipIdx.foldl (fun m (p, i) => m.insert p.fvarId i) {}
  let declOf (f : Name) : Name := ((keys.find? f).map (·.decl)).getD f
  -- The literals, the increments of a parameter (`z`, `y`, `l`) and the
  -- arguments of the self tail calls (position, variable).
  let rec go (c : Code .pure) (acc : FVarIdSet × Array (FVarId × FVarId × FVarId) × Std.HashSet (Nat × FVarId)) :
      FVarIdSet × Array (FVarId × FVarId × FVarId) × Std.HashSet (Nat × FVarId) :=
    match c with
    | .let d k =>
      let (lits, adds, tails) := acc
      let lits := match d.value with
        | .lit (.nat _) => lits.insert d.fvarId
        | _ => lits
      let adds := match d.value with
        | .const f _ #[.fvar a, .fvar b] _ =>
          if declOf f != ``Nat.add then adds
          else if pos.contains a then adds.push (d.fvarId, a, b)
          else if pos.contains b then adds.push (d.fvarId, b, a)
          else adds
        | _ => adds
      let tails := match d.value, k with
        | .const g _ args _, .return r =>
          if g == self && r == d.fvarId then
            args.zipIdx.foldl (fun t (a, i) => match a with
              | .fvar x => t.insert (i, x)
              | _ => t) tails
          else tails
        | _, _ => tails
      go k (lits, adds, tails)
    -- A join point's `return` returns from the declaration; a local
    -- function's code is not the declaration's (a call there is no tail
    -- call of it), and it reads no name from before a rebinding.
    | .jp d k => go k (go d.value acc)
    | .fun _ k => go k acc
    | .cases cs => cs.alts.foldl (fun acc alt => go alt.getCode acc) acc
    | _ => acc
  let (lits, adds, tails) := go body ({}, #[], {})
  let mut out : Std.HashMap FVarId FVarId := {}
  for (z, y, l) in adds do
    if lits.contains l && tails.contains (pos.getD y 0, z) then out := out.insert z y
  return out

/-- Whether `e` evaluates, whenever it completes, a call of a
`boundedWordAccesses` access with the word `k` among its arguments: the
call itself, or one inside the arguments of a call or constructor, a field,
a cast, an application, the scrutinee of a `match` or the condition of an
`if`, or a block's `let`s and result (all evaluated before any branch). -/
partial def evalsBoundedAccess (k : String) : RR.Expr → Bool
  | .call g _ args =>
    (boundedWordAccesses.contains g && args.any (fun (a : RR.Expr) => match a with
      | .var n => n == k
      | _ => false)) || args.any (evalsBoundedAccess k)
  | .ctor _ _ args => args.any (evalsBoundedAccess k)
  | .field e _ | .cast e _ => evalsBoundedAccess k e
  | .apply f a => evalsBoundedAccess k f || evalsBoundedAccess k a
  | .mtch s _ => evalsBoundedAccess k s
  | .ite c _ _ => evalsBoundedAccess k c
  | .block b => b.lets.any (fun (_, _, v) => evalsBoundedAccess k v) || evalsBoundedAccess k b.result
  | _ => false

/-- The variables (Reussir names, `vars`) whose index words the let-run
wants from `bindReadIndex` for `let d` followed by `k`: for a call of a
`boundedIndexSyms` extern, its `Nat` arguments that `k` uses. -/
def indexWordsWanted (d : LetDecl .pure) (k : Code .pure) (vars : Std.HashMap FVarId (String × RR.Ty)) :
    LowerM (Std.HashSet String) := do
  let .const f _ args _ := d.value | return {}
  -- An instance of a polymorphic extern is named by its key (`calleeOf`).
  let orig := ((← read).keys.find? f).map (·.decl) |>.getD f
  let some sym := getExternNameFor (← getEnv) `c orig | return {}
  unless boundedIndexSyms.contains sym do return {}
  let mut out : Std.HashSet String := {}
  for a in args do
    if let .fvar y := a then
      if let some (n, t) := vars[y]? then
        if t == .named "Nat" && hasFVar y k then out := out.insert n
  return out

mutual
  /-- Lower a code block whose value has Reussir type `retTy`. -/
  partial def lowerCode (ctx : CodeCtx) (outlined : FVarIdSet) (retTy : RR.Ty) (c : Code .pure) :
      LowerM RR.Block := do
    match c with
    | .let .. =>
      -- A run of `let`s is lowered in a loop and prepended once, and each
      -- value is lowered with a map of just the variables it reads (all
      -- that `lowerLetValue` looks up), while the run's own variables
      -- collect in a map of their own, merged once at the end: so a long
      -- straight-line body (a spliced literal) costs linear time, where
      -- growing the context's map would copy it at every `let`.
      let base := { ctx with vars := {} }
      let outer := ctx.vars
      let mut runVars : Std.HashMap FVarId (String × RR.Ty) := {}
      let mut runCalls := ctx.letCalls
      -- The run's rebound indices (`rebindIndex`), with the name each had
      -- before its first rebinding (`CodeCtx.indexOrig`).
      let mut runOrig : Std.HashMap FVarId String := {}
      let mut c := c
      let mut lets : Array (String × Option RR.Ty × RR.Expr) := #[]
      -- `int-match`: a chain of tests of a `Nat` against literals, one
      -- `match` (Lower/IntMatch), its scrutinee and arms.
      let mut chain : Option (String × RR.Ty × IntArms) := none
      let mut litNames : Std.HashSet String := {}
      repeat
        let .let d k := c | break
        if (← read).intMatch then
          if let some (n, _, isInt, _) := litTest? ctx.intInfo none c then
            let nv := match runVars[n]?, outer[n]? with
              | some v, _ | none, some v => some v
              | none, none => none
            if let some (x, nt) := nv then
              if nt == .named (if isInt then "Int" else "Nat") then
                chain := some (x, nt, chainArms ctx.intInfo n isInt c)
                break
        let t ← lowerType d.type
        let used := valueUses d.value {}
        let small := used.fold (init := ({} : Std.HashMap FVarId (String × RR.Ty))) fun m x =>
          match runVars[x]?, outer[x]? with
          | some v, _ | none, some v => m.insert x v
          | none, none => m
        -- `rebindIndex`'s exception: a loop-carried increment of a rebound
        -- parameter reads the parameter itself (`loopCarriedAdds`).
        let small := match base.loopAdds[d.fvarId]? with
          | some y => match runOrig[y]? <|> base.indexOrig[y]? with
            | some o => small.insert y (o, RR.Ty.named "Nat")
            | none => small
          | none => small
        let ctx := { base with vars := small }
        -- J4: a tail call that enters a state machine (`tailCallEntry`).
        if let .const f _ args _ := d.value then
          if let .return x := k then
            if x == d.fvarId && t == retTy then
              if let some e ← tailCallEntry H ctx f args then return ⟨lets, e⟩
        -- A box that only goes into boxes is bound as a `Box`
        -- (`CodeCtx.boxedOnly`, `letValueBoxed`): a box field or a callee's
        -- `Box` result is not unboxed only to be boxed again.
        let t ← if t != RR.Ty.box && t != .unit && ctx.boxedOnly.contains d.fvarId &&
            (← letValueBoxed ctx d.value) then pure RR.Ty.box else pure t
        -- `rebindIndex`: the index words of a proved access, bound before
        -- its `let` (`indexWordsWanted`, `bindReadIndex`).
        let want ← indexWordsWanted d k small
        let saved := (← get).indexWords
        unless want.isEmpty do modify fun s => { s with indexWords := #[] }
        let e ← try withReader (fun r => { r with hoistIndexWords := want }) (lowerLetValue ctx d.value d.type t)
          catch ex => throwError "{ex.toMessageData}\n  in let {d.binderName} : {d.type}"
        let words ← if want.isEmpty then pure #[] else pure (← get).indexWords
        unless want.isEmpty do modify fun s => { s with indexWords := saved }
        for (w, n) in words do
          lets := lets.push (w, some (RR.Ty.named "u64"), .call "l2r_nat_index" #[] #[.var n])
        let x ← fresh "x"
        lets := lets.push (x, some t, e)
        -- After the access, the index is its word's `Nat`: one per word,
        -- for every argument of that name (`small` holds this `let`'s).
        let mut rebound : Std.HashSet String := {}
        for (w, n) in words do
          if rebound.contains n || !evalsBoundedAccess w e then continue
          rebound := rebound.insert n
          let ys := small.fold (init := #[]) fun acc y (yn, yt) =>
            if yn == n && yt == RR.Ty.named "Nat" && !ctx.rebuild.contains y then acc.push y else acc
          if ys.isEmpty then continue
          let b ← fresh "ib"
          lets := lets.push (b, some (RR.Ty.named "Nat"), .call "l2r_nat_of_index" #[] #[.var w])
          for y in ys do
            runVars := runVars.insert y (b, RR.Ty.named "Nat")
            runOrig := runOrig.insert y ((runOrig[y]? <|> base.indexOrig[y]?).getD n)
        if ctx.intInfo.litLet d then litNames := litNames.insert x
        runVars := runVars.insert d.fvarId (x, t)
        if let some v ← closedLetValue d.value e then
          modify fun s => { s with closedLets := s.closedLets.insert x (v, t) }
        if let .const f _ args _ := d.value then
          if !args.isEmpty then runCalls := runCalls.insert d.fvarId (f, args.size)
        c := k
      let vars := runVars.fold (init := outer) fun m k v => m.insert k v
      let indexOrig := runOrig.fold (init := base.indexOrig) fun m k v => m.insert k v
      let ctx' := { base with vars, letCalls := runCalls, indexOrig }
      match chain with
      | some (x, nt, arms) =>
        let m ← lowerIntMatch ctx' outlined retTy x nt arms
        -- The literals only the fused tests read are left out.
        let mut used := rrFreeVars m {} {}
        let mut kept := #[]
        for (y, t, e) in lets.reverse do
          if litNames.contains y && !used.contains y then continue
          used := rrFreeVars e {} used
          kept := kept.push (y, t, e)
        return ⟨kept.reverse, m⟩
      | none =>
        let b ← lowerCode ctx' outlined retTy c
        return { b with lets := lets ++ b.lets }
    | .return x =>
      if let some (e, t) := ctx.rebuild[x]? then return .ofExpr (← coerce e t retTy)
      match ctx.vars[x]? with
      | some (n, t) => return .ofExpr (← coerce (.var n) t retTy)
      | none => throwError "lean2rr: return of unbound variable (internal error)"
    | .unreach _ => return .ofExpr (.call "l2r_unreachable" #[retTy] #[])
    | .cases cs => return .ofExpr (← lowerCases ctx outlined retTy cs)
    | .jmp j args =>
      -- The arguments of the parameters the join point takes (rule 4:
      -- not the erased ones), for the jumps that pass arguments.
      let taken : Array (Arg .pure) := match ctx.jpKeep[j]? with
        | some keep => (args.zipIdx.filter fun (_, i) => keep[i]?.getD true).map (·.1)
        | none => args
      match ctx.jumps[j]? with
      | some (.inline params body) =>
        -- J1: bind the parameters to the arguments, then the body.
        let mut ctx' := ctx
        let mut lets := #[]
        for (p, a) in params.zip args do
          let t ← lowerType p.type
          let x ← fresh "j"
          lets := lets.push (x, some t, ← lowerArg ctx a t)
          ctx' := { ctx' with vars := ctx'.vars.insert p.fvarId (x, t) }
        let b ← lowerCode ctx' outlined retTy body
        return { b with lets := lets ++ b.lets }
      | some (.yield tys) =>
        let vals ← (taken.zip tys).mapM fun (a, t) => lowerArg ctx a t
        match vals.size with
        | 0 => return .ofExpr .unitVal
        | 1 => return .ofExpr vals[0]!
        | _ =>
          let (tn, order) ← tupleType tys
          return .ofExpr (.ctor tn none (order.map (vals[·]!)))
      | some (.call fn captured) =>
        let tys := ctx.jpParams.getD j #[]
        let vals ← (taken.zip tys).mapM fun (a, t) => lowerArg ctx a t
        return .ofExpr (.call fn #[] (captured.map .var ++ vals))
      | some (.enter variant captured) =>
        let some sm := ctx.sm | throwError "lean2rr: state-machine jump outside a state machine"
        let tys := ctx.jpParams.getD j #[]
        let vals ← (taken.zip tys).mapM fun (a, t) => lowerArg ctx a t
        return .ofExpr (← H.stateMachine.jumpCall sm variant (captured.map .var ++ vals))
      | none => throwError "lean2rr: jump to unknown join point (internal error)"
    | .jp d k =>
      -- Rule 4: a join point takes no erased parameter (bound to the unit
      -- value in its body).
      let keepJ := d.params.map fun p => !erasedDom p.type
      let params := (d.params.zip keepJ).filterMap fun (p, b) => if b then some p else none
      let unitVars (m : Std.HashMap FVarId (String × RR.Ty)) : Std.HashMap FVarId (String × RR.Ty) :=
        (d.params.zip keepJ).foldl (init := m) fun m (p, b) => if b then m else m.insert p.fvarId ("L2RUnit::u{}", .unit)
      let ptys ← params.mapM (lowerType ·.type)
      let ctx := { ctx with jpParams := ctx.jpParams.insert d.fvarId ptys,
                            jpKeep := ctx.jpKeep.insert d.fvarId keepJ,
                            jpBodies := ctx.jpBodies.insert d.fvarId d.value }
      if outlined.contains d.fvarId then
        -- J3: outline the body into a function over its free variables.
        let pnames ← params.mapM fun _ => fresh "p"
        let vars := (params.zip (pnames.zip ptys)).foldl (fun m (p, nt) => m.insert p.fvarId nt) (unitVars ctx.vars)
        -- A function of its own: the names before a rebinding
        -- (`indexOrig`) are not captured.
        let bodyCtx := { ctx with vars, indexOrig := {} }
        let body ← lowerCode bodyCtx outlined retTy d.value
        let bound := pnames.foldl (·.insert ·) ({} : Std.HashSet String)
        -- Captured in the order of their first use in the body, not by
        -- name (`rrFreeVarsInOrder`): the order of the outlined function's
        -- parameters, and of a state machine's slots.
        let free := rrFreeVarsInOrder #[(body, bound)]
        -- The variables in scope: those `vars` names, and those captured
        -- by the outlined join points in scope, which the body's jumps to
        -- them pass by name even where `vars` names them differently.
        let varTys : Std.HashMap String RR.Ty := ctx.vars.fold (fun m _ (n, t) => m.insert n t) ctx.captured
        let captured := free.filter varTys.contains
        let capturedTys := captured.map fun n => (n, varTys.getD n .unit)
        let fparams := capturedTys ++ pnames.zip ptys
        let ctx := { ctx with captured := capturedTys.foldl (fun m (n, t) => m.insert n t) ctx.captured }
        if let some sm := ctx.sm then
          -- J4: a variant of the state machine.
          let variant ← fresh "j"
          modify fun s => { s with smArms := s.smArms.push (variant, fparams, body) }
          return ← lowerCode { ctx with jumps := ctx.jumps.insert d.fvarId (.enter variant captured) } outlined retTy k
        let fn ← fresh "jp_"
        modify fun s => { s with fns := s.fns.push (.fn fn fparams retTy body) }
        lowerCode { ctx with jumps := ctx.jumps.insert d.fvarId (.call fn captured) } outlined retTy k
      else
        let jumps := (countJumps k {}).getD d.fvarId 0
        if jumps ≤ 1 || (H.duplicateJp { bodies := ctx.jpBodies, single := ctx.jpSingle, loop := ctx.loop } d jumps &&
            !endsInJumps k (({} : FVarIdSet).insert d.fvarId) outlined) then
          -- J1, or a small join point that is not J2: its body at each jump.
          let jpSingle := if jumps ≤ 1 then ctx.jpSingle.insert d.fvarId else ctx.jpSingle
          lowerCode { ctx with jumps := ctx.jumps.insert d.fvarId (.inline d.params d.value), jpSingle }
            outlined retTy k
        else
          -- J2: the scope computes the join point's arguments, two or more
          -- as a tuple (`tupleType`, its members in `memberOrder`).
          let (resTy, posOf) ← match ptys.size with
            | 0 => pure (RR.Ty.unit, #[])
            | 1 => pure (ptys[0]!, #[0])
            | _ => do
              let (tn, order) ← tupleType ptys
              pure (RR.Ty.named tn, positionsOf order)
          let scope ← lowerCode { ctx with jumps := ctx.jumps.insert d.fvarId (.yield ptys) } outlined resTy k
          let r ← fresh "jv"
          let mut lets : Array (String × Option RR.Ty × RR.Expr) := #[(r, some resTy, .block scope)]
          let mut ctx' := { ctx with vars := unitVars ctx.vars }
          for h : i in [:params.size] do
            let p := params[i]
            let x ← fresh "y"
            let e := if ptys.size == 1 then RR.Expr.var r else .field (.var r) posOf[i]!
            lets := lets.push (x, some ptys[i]!, e)
            ctx' := { ctx' with vars := ctx'.vars.insert p.fvarId (x, ptys[i]!) }
          let b ← lowerCode ctx' outlined retTy d.value
          return { b with lets := lets ++ b.lets }
    | .fun d k _ =>
      -- Lambda lifting normally removes local functions; lower defensively:
      -- nested Reussir closures, one per domain of the function's type at
      -- run time (rule 4: a phantom domain has none; a unit domain at a
      -- parameter the function does not take, `keepMask`, is ignored).
      let fty ← lowerType d.type
      let keep := keepMask (d.params.map (·.type))
      let mut vars := ctx.vars
      let mut layers : Array (String × RR.Ty) := #[]
      let mut pre : Array (String × Option RR.Ty × RR.Expr) := #[]
      let mut t := fty
      for h : i in [:d.params.size] do
        let p := d.params[i]
        -- `lowerType` gives a domain (unit, phantom or data) for every
        -- domain of the Lean type, and a local function's type has one per
        -- parameter (Lean's invariant), so this holds.
        let .fn dom c := t | throwError "lean2rr: local function {d.binderName}: its type {d.type} has fewer domains than its {d.params.size} parameters (internal error)"
        if dom == RR.Ty.phantom then
          -- No argument at run time: a placeholder for a parameter it takes.
          if keep[i]! && !erasedDom p.type then
            let x ← fresh "lp"
            let pt ← lowerType p.type
            pre := pre.push (x, some pt, ← zeroValue pt)
            vars := vars.insert p.fvarId (x, pt)
          else vars := vars.insert p.fvarId ("L2RUnit::u{}", .unit)
        else
          let x ← fresh "lp"
          layers := layers.push (x, t)
          vars := vars.insert p.fvarId (if keep[i]! then (x, dom) else ("L2RUnit::u{}", .unit))
        t := c
      if layers.isEmpty then
        throwError "lean2rr: local function {d.binderName}: every domain of its type {d.type} is phantom (internal error: its last domain stays, `keptErasedHead`)"
      let bodyCtx := { ctx with vars, indexOrig := {} }
      let body ← lowerCode bodyCtx outlined t d.value
      let mut lam := RR.Expr.block { body with lets := pre ++ body.lets }
      for (n, lt) in layers.reverse do
        lam := rawFnValue lt n (.ofExpr lam)
      let x ← fresh "f"
      let b ← lowerCode { ctx with vars := ctx.vars.insert d.fvarId (x, fty) } outlined retTy k
      return { b with lets := #[(x, some fty, lam)] ++ b.lets }
    | _ => throwError "lean2rr: impure code (internal error)"

  partial def lowerCases (ctx : CodeCtx) (outlined : FVarIdSet) (retTy : RR.Ty) (cs : Cases .pure) :
      LowerM RR.Expr := do
    let some (scrut0, sty0) := ctx.vars[cs.discr]? | throwError "lean2rr: cases on unbound variable"
    -- A `cases` on a value of statically unknown type: unbox it to the
    -- inductive's one type first (`uniformType`).
    if sty0 == RR.Ty.box then
      let uty ← uniformType cs.typeName
      let u ← fresh "uv"
      let conv ← coerce (.var scrut0) RR.Ty.box uty
      let ctx' := { ctx with vars := ctx.vars.insert cs.discr (u, uty) }
      return .block ⟨#[(u, some uty, conv)], ← lowerCases ctx' outlined retTy cs⟩
    -- A cast value (see `castCases`): converted first, or matched through
    -- the corresponding constructors of its own type.
    let mut view : Option String := none
    match ← castCases sty0 cs.typeName with
    | .same => pure ()
    | .view _ dn => view := some dn
    | .convert dty =>
      let u ← fresh "cv"
      let conv ← coerce (.var scrut0) sty0 dty
      let ctx' := { ctx with vars := ctx.vars.insert cs.discr (u, dty) }
      return .block ⟨#[(u, some dty, conv)], ← lowerCases ctx' outlined retTy cs⟩
    | .unit =>
      -- No data: the only alternative, its fields carry nothing.
      let some alt := cs.alts[0]? | return .call "l2r_unreachable" #[retTy] #[]
      let ctx' := alt.getParams.foldl (fun c p => { c with vars := c.vars.insert p.fvarId ("L2RUnit::u{}", .unit) }) ctx
      return .block (← lowerCode ctx' outlined retTy alt.getCode)
    let (scrut, sty) := (scrut0, sty0)
    -- A `cases` on Reussir's built-in `Nat` or `Int` (Stage 2 keeps it
    -- under `int-match`): a `match` on the integer (Lower/IntMatch).
    if (cs.typeName == ``Nat && sty == .named "Nat") || (cs.typeName == ``Int && sty == .named "Int") then
      let arms := if cs.typeName == ``Nat then natArms ctx.intInfo {} cs #[] {} else intArms ctx.intInfo cs
      return ← lowerIntMatch ctx outlined retTy scrut sty arms
    let altFor (ctor : Name) : Option (Alt .pure) := cs.alts.find? fun
      | .alt c _ _ _ => c == ctor
      | _ => false
    let dflt : Option (Code .pure) := cs.alts.findSome? fun
      | .default k => some k
      | _ => none
    match sty with
    | .named "bool" =>
      let branch (ctor : Name) : LowerM RR.Block := do
        match altFor ctor with
        | some alt => lowerAlt ctx outlined retTy alt.getCode
        | none =>
          match dflt with
          | some k => lowerAlt ctx outlined retTy k
          | none => return .ofExpr (.call "l2r_unreachable" #[retTy] #[])
      return .ite (.var scrut) (← branch ``Bool.true) (← branch ``Bool.false)
    | .named tn =>
      let some info := (← get).typeInfos[tn]?
        | throwError "lean2rr: cases on non-nominal type {tn} ({cs.typeName})"
      -- The alternatives' constructors, at each constructor position of
      -- the matched type, and their layouts over its records.
      let (actors, layoutOf) ← match view with
        | none => pure (info.ctorOrder, fun c => info.ctors.find? c)
        | some dn =>
          let some di := (← get).typeInfos[dn]? | throwError "lean2rr: no type {dn}"
          let mut m : NameMap CtorLayout := {}
          for (sc, dc) in info.ctorOrder.zip di.ctorOrder do
            if let (some sl, some dl) := (info.ctors.find? sc, di.ctors.find? dc) then
              m := m.insert dc (← viewLayout sc dc sl dl)
          pure (di.ctorOrder, fun c => m.find? c)
      match info.shape with
      | .struct =>
        let some alt := cs.alts[0]? | throwError "lean2rr: empty cases"
        match alt with
        | .alt ctor ps k _ =>
          let some layout := layoutOf ctor | throwError "lean2rr: bad constructor"
          -- The fields, projected (a hook may bind some later: Opt/LazyFields).
          let arm : CasesArm := { discr := cs.discr, scrut, ty := tn, layout, params := ps, code := k,
                                  shared := !info.value && view.isNone }
          let (lets, ctx') ← H.structFields ctx arm
          let convs := fieldConvNames ctx' (ps.map (·.fvarId))
          let b ← lowerCode ctx' outlined retTy k
          return .block { b with lets := dropUnusedConvs lets convs b ++ b.lets }
        | .default k => return .block (← lowerCode ctx outlined retTy k)
        | _ => throwError "lean2rr: impure alternative"
      | _ =>
        let mut arms := #[]
        for ctor in actors do
          let some layout := layoutOf ctor | continue
          match altFor ctor with
          | some (.alt _ ps k _) =>
            let mut ctx' := ctx
            let mut binders := Array.replicate (layout.fields.filter (·.isSome)).size (none : Option String)
            for h : i in [:ps.size] do
              let p := ps[i]
              match layout.fields[i]? with
              | some (some (j, ft)) =>
                let x ← fresh "f"
                binders := binders.set! j (some x)
                ctx' := { ctx' with vars := ctx'.vars.insert p.fvarId (x, ft) }
              | _ => ctx' := { ctx' with vars := ctx'.vars.insert p.fvarId ("L2RUnit::u{}", .unit) }
            -- Hooks: fields bound later instead (Opt/LazyFields), bindings
            -- before the arm's code (Opt/NullaryScrutinee).
            let arm : CasesArm := { discr := cs.discr, scrut, ty := tn, layout, params := ps, code := k,
                                    shared := info.shape == .enum, view := view.isSome }
            let (armBinders, armCtx) ← H.enumFields ctx' arm binders
            let (pre, armCtx) ← H.armPrelude armCtx arm armBinders
            -- The fields bound by the match, at their parameters' own types
            -- (`bindField`); a hook may have left some to be bound later
            -- (Opt/LazyFields), and the binders keep the fields' values as
            -- the record holds them (Opt/FreshRebuild rebuilds from them).
            let mut conv := #[]
            let mut armCtx := armCtx
            for h : i in [:ps.size] do
              let p := ps[i]
              let some (some (j, ft)) := layout.fields[i]? | continue
              let some (some x) := armBinders[j]? | continue
              unless armCtx.vars[p.fvarId]? == some (x, ft) do continue
              let (c, ctx2) ← bindField armCtx p.fvarId (← lowerType p.type) x ft
              conv := conv ++ c
              armCtx := ctx2
            let body ← lowerAlt armCtx outlined retTy k
            conv := dropUnusedConvs conv (conv.foldl (fun s (y, _, _) => s.insert y) {}) body
            arms := arms.push { ty := tn, ctor := some layout.variant, binders := armBinders,
                                body := { body with lets := pre ++ conv ++ body.lets } }
          | _ => pure ()
        if arms.size < info.ctorOrder.size then
          let body ← match dflt with
            | some k => lowerAlt ctx outlined retTy k
            | none => pure (.ofExpr (.call "l2r_unreachable" #[retTy] #[]))
          arms := arms.push { ty := tn, ctor := none, binders := #[], body }
        return .mtch (.var scrut) arms
    | t => throwError "lean2rr: cases on value of type {t.render} ({cs.typeName})"

  /-- The `match` on `Nat` or `Int` variable `scrut` (of type `sty`) with
  arms `arms` (Lower/IntMatch). An arm's binder is a `Nat` (converted to
  its parameter's type, `bindField`), `_` where the code does not use it.
  An arm that names the scrutinee reads it through a binding Reussir makes
  of the whole scrutinee (#803): in a literal arm the constant, in `_`,
  `Int::OfNat(m)`, `Int::OfNat(_)` and a last arm without a binder (which
  Reussir makes the `default`) the value itself, but in an arm that
  selects the scrutinee minus a bound (`Nat::Succ(p)`, `Int::NegSucc(m)`,
  `Nat::Succ(_)` before other arms, …) a value rebuilt from that
  difference (`p + 1`: an allocation for a heap value). So where such an
  arm names the scrutinee,
  the `match` is on a copy (`let s = n; match s { … }`): the arm reads `n`
  itself, which Reussir retains for it (a test of the tag for an
  immediate). Arms not covering every value get `_ => l2r_unreachable`. -/
  partial def lowerIntMatch (ctx : CodeCtx) (outlined : FVarIdSet) (retTy : RR.Ty) (scrut : String)
      (sty : RR.Ty) (arms : IntArms) : LowerM RR.Expr := do
    let mut out : Array RR.Arm := #[]
    let mut copy := false
    for h : i in [:arms.arms.size] do
      let a := arms.arms[i]
      let code := a.fullCode
      let (arm, offset) ← match a.pat with
        | .lit v => pure (({ ty := "", ctor := some (toString v), binders := #[], body := ← lowerAlt ctx outlined retTy code } : RR.Arm), false)
        | .wild ws =>
          pure ({ ty := "", ctor := none, binders := #[], body := ← lowerAlt ctx outlined retTy code, wrap := ws },
            ws.any (· != ("Int", "OfNat")))
        | .bind ws ty c p =>
          let offset := !(ws.isEmpty && c == "OfNat")
          if ctx.used.contains p.fvarId then
            let x ← fresh "f"
            let (conv, ctx') ← bindField ctx p.fvarId (← lowerType p.type) x (.named "Nat")
            let body ← lowerAlt ctx' outlined retTy code
            let conv := dropUnusedConvs conv (conv.foldl (fun s (y, _, _) => s.insert y) {}) body
            pure ({ ty, ctor := some c, binders := #[some x], body := { body with lets := conv ++ body.lets }, wrap := ws }, offset)
          else
            pure ({ ty, ctor := some c, binders := #[none], body := ← lowerAlt ctx outlined retTy code, wrap := ws }, offset)
      -- The last arm, without a binder, takes what is left: Reussir makes it
      -- the `default`, which receives the scrutinee itself.
      let last := i + 1 == arms.arms.size && arms.exhaustive && arm.binders.all (·.isNone)
      if offset && !last && !copy && (rrFreeVars.blockFreeVars arm.body {} {}).contains scrut then copy := true
      out := out.push arm
    unless arms.exhaustive do
      out := out.push { ty := "", ctor := none, binders := #[], body := .ofExpr (.call "l2r_unreachable" #[retTy] #[]) }
    if copy then
      let s ← fresh "ns"
      return .block ⟨#[(s, some sty, .var scrut)], .mtch (.var s) out⟩
    return .mtch (.var scrut) out

  /-- Lower the code of an alternative, after its fields are bound (a hook
  may bind more first: Opt/LazyFields). -/
  partial def lowerAlt (ctx : CodeCtx) (outlined : FVarIdSet) (retTy : RR.Ty) (k : Code .pure) :
      LowerM RR.Block :=
    H.lowerAlt (lowerAlt · outlined retTy) (lowerCode · outlined retTy) ctx retTy k
end

/-- What lowering a declaration's code needs, set up from the declaration:
its body (after `LowerHooks.prepareBody`), Reussir parameters and their
variables, result type, call cycle and outlined join points. -/
structure DeclSetup where
  body : Code .pure
  /-- The result's LCNF type and Reussir type. -/
  resTy : Expr
  ret : RR.Ty
  params : Array (String × RR.Ty)
  vars : Std.HashMap FVarId (String × RR.Ty)
  loop : NameSet
  outlined : FVarIdSet
  deriving Inhabited

/-- Set up declaration `d` (with code `body`) for lowering. -/
def setupDecl (d : Decl .pure) (body : Code .pure) : LowerM DeclSetup := do
  let body := H.prepareBody body
  let (_, r) := splitFnType d.type d.params.size
  let ret ← lowerType r
  -- Rule 4a: the Reussir function takes an erased parameter only when it
  -- is the last one (one unit for the trailing erased ones); the others
  -- are bound to the unit value.
  let keep := keepMask (d.params.map (·.type))
  let mut params : Array (String × RR.Ty) := #[]
  let mut vars : Std.HashMap FVarId (String × RR.Ty) := {}
  for h : i in [:d.params.size] do
    let p := d.params[i]
    if keep[i]! then
      let x ← fresh "a"
      let t ← lowerType p.type
      params := params.push (x, t)
      vars := vars.insert p.fvarId (x, t)
    else vars := vars.insert p.fvarId ("L2RUnit::u{}", .unit)
  let loop := ((← read).callCycles.find? d.name).getD {}
  let outlined := chooseOutlined H.duplicateJp loop body
  return { body, resTy := r, ret, params, vars, loop, outlined }

/-- Lower the code of declaration `d` (set up as `su`) in state machine
`sm?`, if any; `cycles`: the state machines of its cycle of tail calls that
its tail calls enter (`CodeCtx.cycles`). -/
def lowerDeclCode (d : Decl .pure) (su : DeclSetup) (sm? : Option StateMachine)
    (cycles : Array StateMachine := #[]) : LowerM RR.Block := do
  let lc ← read
  let ctx : CodeCtx := { vars := su.vars, sm := sm?, loop := su.loop, used := codeUses su.body {},
                         boxedOnly := ← boxedOnlyVars su.body su.ret, decl := d.name, cycles,
                         intInfo := if lc.intMatch then intMatchInfo lc.decls su.body else {},
                         loopAdds := loopCarriedAdds lc.keys d.name d.params su.body }
  -- The body of a declaration without parameters runs once: a constant
  -- boxed there is boxed in line (`boxOf`), not given a once-cell.
  modify fun s => { s with inConstBody := d.params.isEmpty }
  let block ← try lowerCode H ctx su.outlined su.ret su.body
    catch e => throwError "{e.toMessageData}\n  while lowering {d.name}"
  modify fun s => { s with inConstBody := false }
  return block

/-- Whether declaration `d` gets lowered code of its own (not the glue of
`IO.Process.output`, `processOutputBody`). -/
def ownLowering (d : Decl .pure) : LowerM Bool := do
  let orig := ((← read).keys.find? d.name).map (·.decl) |>.getD d.name
  return !(orig == ``IO.Process.output && d.params.size == 3)

/-- Lower a declaration with code to a Reussir function; `cycles`: the
state machines of its cycle of tail calls (`lowerGroup`), which its tail
calls of the cycle's other declarations enter (`CodeCtx.cycles`). -/
def lowerDecl (d : Decl .pure) (cycles : Array StateMachine := #[]) : LowerM Unit := do
  let .code body := d.value | return
  -- A constant whose code is one string literal (or one read of such a
  -- constant) has no function: its reads call the literal cache
  -- (`strLitCached`).
  if (← read).litConsts.contains d.name then return
  let su ← setupDecl H d body
  let params := su.params
  let ret := su.ret
  -- `IO.Process.output`: generated glue instead of Lean's body (see
  -- `processOutputBody`).
  unless ← ownLowering d do
    let block ← processOutputBody params ret su.resTy
    modify fun s => { s with fns := s.fns.push (.fn (fnName d.name) params ret block) }
    return
  -- J4: the declaration as one state machine when an outlined join point
  -- calls it back in tail position (`LowerHooks.stateMachine`).
  let sm? := H.stateMachine.plan d su.body su.outlined (params.map (·.1)) none
  modify fun s => { s with smArms := #[] }
  let block ← lowerDeclCode H d su sm? cycles
  if let some sm := sm? then
    H.stateMachine.emit d sm params ret block
    return
  -- A constant is cached in a once-cell, unless a hook has it recomputed
  -- at each use (Opt/CheapConsts) or it is a closed term evaluated where
  -- it is used (`uncachedConsts`, `chainConsts`). (One whose code is one
  -- string literal has no function at all: `litConsts`, above.)
  if d.params.isEmpty && !(← H.recomputeConst su.body) && !(← read).uncachedConsts.contains d.name then
    let items ← cafAccessor (fnName d.name) ret block
    modify fun s => { s with fns := s.fns ++ items }
  else
    modify fun s => { s with fns := s.fns.push (.fn (fnName d.name) params ret block) }

/-- The Lean declaration that mono declaration `n` comes from (an instance
`f._l2r.k`, or a declaration a pass made from one, `f._l2r.k._l2r_flat`):
`f`; `n` when there is none. -/
def sourceDeclName (keys : NameMap InstKey) (n : Name) : Name :=
  match keys.find? n with
  | some k => k.decl
  | none => match n with
    | .str p _ | .num p _ => if p.isAnonymous then n else sourceDeclName keys p
    | .anonymous => n

/-- A state machine of a cycle of tail calls (`lowerGroup`) over its
declarations `ds` (set up as `sus`, in program order), entered by functions
named with `suffix`: planned for the first declaration whatever its join
points, with an entry variant per declaration (the first one's is the
entry), whose fields are its parameters and whose arm is its lowered code,
and an entry function per declaration (`fnName d ++ suffix`,
`StateMachine.entryFn`, `SmMember.entryFn`). In it, a tail call of one of
`ds` re-enters it at that declaration's variant (`tailCallEntry`), and one
of another declaration of the cycle enters the first state machine of
`cycles` that has it. Emitted here. -/
def cycleMachine (ds : Array (Decl .pure)) (sus : Array DeclSetup) (suffix : String)
    (cycles : Array StateMachine) : LowerM (Option StateMachine) := do
  let d0 := ds[0]!
  let su0 := sus[0]!
  let some sm0 := H.stateMachine.plan d0 su0.body su0.outlined (su0.params.map (·.1)) (some (fnName d0.name ++ suffix))
    | return none
  let mut members : Array SmMember := #[]
  for i in [1:ds.size] do
    members := members.push { name := ds[i]!.name, variant := ← fresh "e", arity := ds[i]!.params.size,
                              params := sus[i]!.params, entryFn := fnName ds[i]!.name ++ suffix }
  let sm : StateMachine := { sm0 with members }
  modify fun s => { s with smArms := #[] }
  let block ← lowerDeclCode H d0 su0 (some sm) cycles
  for i in [1:ds.size] do
    let b ← lowerDeclCode H ds[i]! sus[i]! (some sm) cycles
    modify fun s => { s with smArms := s.smArms.push (members[i - 1]!.variant, sus[i]!.params, b) }
  H.stateMachine.emit d0 sm su0.params su0.ret block
  return some sm

/-- Lower the declarations `ds` of a cycle of tail calls (`tailCallGroups`,
in program order): each as its own function (`lowerDecl`), as if alone,
and the cycle as one more state machine (J4, translation plan §5.6,
`cycleMachine`), named after the first declaration (`_cyc`). In a
declaration's own function, a tail call of another declaration of the
cycle calls that declaration's entry function (`CodeCtx.cycles`); in the
state machine, a tail call of a declaration of the cycle re-enters it at
that declaration's variant, a self tail call of the function, which LLVM
turns into a loop (`tailCallEntry`). So the cycle runs in one frame, where
separate functions call each other, a sibling call only where LLVM can
make one (not with a multi-word result whose returns LLVM merged, nor with
more stack arguments than the caller's), and use stack per call. A call
that is not a tail call calls the declaration's own function, also from
the state machine: a deep recursion of a declaration uses its own frame per
level, not the state machine's, which LLVM sizes for every arm.

A cycle whose declarations' frames differ much (`cycleWeight`,
`lightMembers`), with two or more light declarations that tail-call each
other and one or more heavy ones, also gets a light state machine of its
light declarations (`_lit`): their own functions' tail calls of each other
enter it instead, and in it, a tail call of a heavy declaration enters the
cycle's state machine (one more frame per entry, and the cycle then runs
there). So a deep recursion that passes a tail call between two light
declarations at every level enters the light state machine at every level,
whose frame is small, not the cycle's state machine, whose frame is sized
for the heavy declarations' arms. When the results have different Reussir
types, or one of them has no code of its own (`ownLowering`), the cycle
has no state machine. -/
def lowerGroup (ds : Array (Decl .pure)) : LowerM Unit := do
  let mut sus : Array DeclSetup := #[]
  for d in ds do
    match d.value with
    | .code body =>
      if (← ownLowering d) && !(← read).litConsts.contains d.name then
        sus := sus.push (← setupDecl H d body)
    | .extern _ => pure ()
  let mut cycles : Array StateMachine := #[]
  if sus.size == ds.size && ds.size ≥ 2 && sus.all (·.ret == sus[0]!.ret) then
    let debug := (← IO.getEnv "L2R_DEBUG").isSome
    let keys := (← read).keys
    let names (xs : Array (Decl .pure)) := (xs.map (sourceDeclName keys ·.name |>.toString)).qsort (· < ·)
    if let some sm := ← cycleMachine H ds sus "_cyc" #[] then
      if debug then IO.eprintln s!"lean2rr: one state machine for a cycle of tail calls: {names ds}"
      cycles := #[sm]
      -- The light state machine, of the light declarations, when two of
      -- them tail-call each other and the cycle has a heavy one.
      let light := lightMembers ((ds.zip sus).map fun ((d, su) : Decl .pure × DeclSetup) => cycleWeight d su.body)
      let lds := (ds.zip light).filterMap fun ((d, l) : Decl .pure × Bool) => if l then some d else none
      let lsus := (sus.zip light).filterMap fun ((su, l) : DeclSetup × Bool) => if l then some su else none
      let lightNames : NameSet := lds.foldl (fun m (d : Decl .pure) => m.insert d.name) {}
      let linked := (lsus.zip lds).any fun ((su, d) : DeclSetup × Decl .pure) =>
        (tailCallees su.body).any fun (g, _) => g != d.name && lightNames.contains g
      if lds.size ≥ 2 && lds.size < ds.size && linked then
        if let some lsm := ← cycleMachine H lds lsus "_lit" #[sm] then
          if debug then
            IO.eprintln s!"lean2rr: a light state machine for the cycle of tail calls {names ds}: {names lds}"
          cycles := #[lsm, sm]
  for d in ds do lowerDecl H d cycles

end

end LeanToReussir
