import Lean
import LeanToReussir.PassConfig

/-!
# Map loops split by element representation (optimization `split-map-loops`)

Stage 3 (translation plan §4, §2.7): an `Array.map` loop whose element
representation changes runs, without this pass, on an array of `Box`es,
converted from the input on entry and to the result on exit. This pass
gives such a loop a split instance over the source and the result array.
-/

namespace LeanToReussir
open Lean Compiler LCNF

/-! ## Map loops that change the element representation

A `map` loop of `Array.mapMUnsafe`/`mapFinIdxMUnsafe` (§2.7) replaces the
elements of its array one by one, so the array holds `α` values at the
indices not visited yet and `β` values at the others. When `α` and `β` have
the same representation, the loop runs on the precise array
(`paramsFromCallers`). When they differ, the array parameter stays
`Array lcAny`, and the loop would run on an array of `Box`es, converted from
the input on entry and to the result on exit. Instead, such a loop gets a
*split* instance over two arrays: the source `src : Array α`, read at `α`'s
own representation (each slot still replaced by the placeholder after it is
read, as Lean does, so that the element stays unshared), and the result
`dst : Array β`, which the caller creates empty with the source's size as
capacity, and to which each mapped value is pushed.

The loop must have the shape Lean gives it: the arrays derived from the
parameter (by `uset`, and through join points) are only read with `uget` at
the loop index (before any value is written), written with `uset` at the
loop index (the placeholder, then the mapped value, once), measured
(`usize`, `size`), passed to the loop again with the index plus one after
the value was written, or with the index to the loop a `_redArg` wrapper
calls, returned, put in a constructor or passed to a join point; and the
entry call passes the index `0`. Then `dst` holds exactly the values mapped
so far whenever the loop runs at index `i` (it has `i` elements), so the
value written at index `i` is the next one pushed. Any other shape keeps the
uniform loop. -/

/-- The shape of a `map` loop: its array parameter (the only one of type
`Array lcAny`), its index parameter, and the type of the values it stores. -/
structure LoopShape where
  arrPos : Nat
  idxPos : Nat
  elem : Expr

/-- The extern instance of `Array` operation `op` at element type `t`. -/
def arrayExternAt (op : Name) (t : Expr) : MRetypeM Name := do
  let some base ← getBaseDecl? op | throwError "lean2rr: no base declaration of {op}"
  externInstance op base #[eraseLevels t]

def isPlaceholderArg (erased : FVarIdSet) : Arg .pure → Bool
  | .fvar x => erased.contains x
  | _ => true

/-- The shape of map loop `d` (see `LoopShape`), given the shapes of the
other map loops. -/
def loopShape? (d : Decl .pure) (types : Types) (shapes : NameMap LoopShape) : MRetypeM (Option LoopShape) := do
  let .code c := d.value | return none
  let keys := (← get).keys
  let arrs := d.params.zipIdx.filter fun (p, _) => isArrayAny p.type.consumeMData
  let #[(arr, arrPos)] := arrs | return none
  let erased := erasedVars c {}
  let paramIdx (a : Arg .pure) : Option Nat := match a with
    | .fvar x => d.params.findIdx? (·.fvarId == x)
    | _ => none
  let apps := constApps c #[]
  let mut idx : Option Nat := none
  let mut elems : Array Expr := #[]
  for (f, args, _) in apps do
    match (keys.find? f).map (·.decl) with
    | some ``Array.uget | some ``Array.uset =>
      if args[1]? == some (.fvar arr.fvarId) && idx.isNone then idx := args[2]? >>= paramIdx
      if (keys.find? f).map (·.decl) == some ``Array.uset && args.size == 5 then
        if !isPlaceholderArg erased args[3]! then
          match args[3]! with
          | .fvar x => elems := elems.push (types.getD x anyExpr)
          | _ => pure ()
    | _ =>
      -- A wrapper (`_redArg`): the loop it passes the array to.
      if let some s := shapes.find? f then
        if args[s.arrPos]? == some (.fvar arr.fvarId) then
          if idx.isNone then idx := args[s.idxPos]? >>= paramIdx
          elems := elems.push s.elem
  let some idxPos := idx | return none
  unless d.params[idxPos]!.type.consumeMData.isConstOf ``USize do return none
  let some β := elems[0]? | return none
  if ← unknown β then return none
  for t in elems do
    if (← norm t) != (← norm β) then return none
  return some { arrPos, idxPos, elem := β }

/-- `c` without the placeholders (`let x := ◾`) it does not use (the
split loop's source gets a placeholder of its own type). -/
partial def dropDeadPlaceholders (c : Code .pure) : Code .pure :=
  match c with
  | .let d k =>
    let k := dropDeadPlaceholders k
    if d.value matches .erased && !usesFVar d.fvarId k then k else .let d k
  | .jp d k => .jp (FunDecl.mk d.fvarId d.binderName d.params d.type (dropDeadPlaceholders d.value)) (dropDeadPlaceholders k)
  | .fun d k _ => .fun (FunDecl.mk d.fvarId d.binderName d.params d.type (dropDeadPlaceholders d.value)) (dropDeadPlaceholders k)
  | .cases cs => .cases ⟨cs.typeName, cs.resultType, cs.discr, cs.alts.map fun
      | .alt ctor ps code _ => .alt ctor ps (dropDeadPlaceholders code)
      | .default code => .default (dropDeadPlaceholders code)
      | a => a⟩
  | c => c
where
  argUses (x : FVarId) (args : Array (Arg .pure)) : Bool := args.any fun a => match a with | .fvar y => y == x | _ => false
  usesFVar (x : FVarId) (c : Code .pure) : Bool :=
    match c with
    | .let d k =>
      (match d.value with
        | .const _ _ args _ => argUses x args
        | .fvar g args => g == x || argUses x args
        | .proj _ _ y => y == x
        | _ => false) || usesFVar x k
    | .jp d k | .fun d k _ => usesFVar x d.value || usesFVar x k
    | .cases cs => cs.discr == x || cs.alts.any fun alt => usesFVar x alt.getCode
    | .jmp j args => j == x || argUses x args
    | .return y => y == x
    | _ => false

structure SplitCtx where
  self : Name
  selfNew : Name
  shape : LoopShape
  α : Expr
  β : Expr
  types : Types
  shapes : NameMap LoopShape

/-- What the rewrite of a loop body knows: each derived array's source and
result arrays and how many values were written into it since the loop was
entered (0 or 1); the `USize` variables that are the loop index plus a
constant; the `USize` literals 1; the placeholders; the derived arrays
passed to each join point parameter (their write counts; `none` for
another argument). -/
structure SplitSt where
  pairs : Std.HashMap FVarId (FVarId × FVarId) := {}
  count : Std.HashMap FVarId Nat := {}
  off : Std.HashMap FVarId Nat := {}
  one : FVarIdSet := {}
  erased : FVarIdSet := {}
  seen : Std.HashMap (FVarId × Nat) (Array (Option Nat)) := {}

abbrev SplitM := StateT SplitSt MRetypeM

def splitFail {α : Type} : SplitM α := throwError "lean2rr: map loop not split"

def replaceArrayAny (t β : Expr) : SplitM Expr := do
  match countArrayAny t with
  | 0 => return t
  | 1 => return t.replace fun e => if isArrayAny e then some (mkApp (mkConst ``Array) β) else none
  | _ => splitFail

mutual
  /-- Ensure the split instance of map loop `f` (whose shape is in `shapes`)
  from `α` to `β`: its name, or `none` if the loop cannot be split. -/
  partial def ensureSplit (f : Name) (α β : Expr) (shapes : NameMap LoopShape)
      (src : NameMap (Decl .pure × Types)) : MRetypeM (Option Name) := do
    let key := (f, ← norm α, ← norm β)
    if let some r := (← get).splits[key]? then
      -- An instance being built is only referenced by itself.
      if let some n := r then
        if (← get).splitBusy.contains n then return none
      return r
    let some (d, types) := src.find? f | return none
    let some shape := shapes.find? f | return none
    let name := Name.num (f ++ `_l2r_split) (← get).splits.size
    modify fun s => { s with splits := s.splits.insert key (some name), splitBusy := s.splitBusy.insert name }
    let r ← try some <$> buildSplit d shape types name α β shapes src catch _ => pure none
    modify fun s => { s with splitBusy := s.splitBusy.erase name }
    match r with
    | some d' =>
      modify fun s => { s with sigs := s.sigs.insert name (declSig d') }
      let (d', _, _) ← localRetype d'
      modify fun s => { s with splitDecls := s.splitDecls.push d', sigs := s.sigs.insert name (declSig d') }
      return some name
    | none =>
      modify fun s => { s with splits := s.splits.insert key none }
      return none

  /-- The split instance `name` of map loop `d`. -/
  partial def buildSplit (d : Decl .pure) (shape : LoopShape) (types : Types) (name : Name) (α β : Expr)
      (shapes : NameMap LoopShape) (src : NameMap (Decl .pure × Types)) : MRetypeM (Decl .pure) := do
    let .code c := d.value | throwError "lean2rr: no code"
    let ret := (splitArrows d.type d.params.size).2
    if ← unknown ret then throwError "lean2rr: map loop result unknown"
    let p := d.params[shape.arrPos]!
    let s ← mkFreshFVarId
    let t ← mkFreshFVarId
    let params := d.params[:shape.arrPos].toArray ++
      #[{ p with fvarId := s, binderName := `src, type := mkApp (mkConst ``Array) α },
        { p with fvarId := t, binderName := `dst, type := mkApp (mkConst ``Array) β }] ++
      d.params[shape.arrPos + 1:].toArray
    let st : SplitSt := {
      pairs := ({} : Std.HashMap _ _).insert p.fvarId (s, t)
      count := ({} : Std.HashMap _ _).insert p.fvarId 0
      off := ({} : Std.HashMap _ _).insert d.params[shape.idxPos]!.fvarId 0
      erased := erasedVars c {} }
    let cx : SplitCtx := { self := d.name, selfNew := name, shape, α, β, types, shapes }
    let (c', _) ← (splitCode cx src c).run st
    return { withSig d params ret with name, value := .code (dropDeadPlaceholders c') }

  /-- Rewrite a loop body for its split instance (see `SplitSt`); fails on
  any other use of a derived array. -/
  partial def splitCode (cx : SplitCtx) (src : NameMap (Decl .pure × Types)) (c : Code .pure) :
      SplitM (Code .pure) := do
    let chain? (a : Arg .pure) : SplitM (Option FVarId) := do
      match a with
      | .fvar x => return if (← getThe SplitSt).pairs.contains x then some x else none
      | _ => return none
    let noChain (args : Array (Arg .pure)) : SplitM Unit := do
      for a in args do
        if (← chain? a).isSome then splitFail
    let offOf (a : Arg .pure) : SplitM (Option Nat) := do
      match a with
      | .fvar x => return (← getThe SplitSt).off[x]?
      | _ => return none
    match c with
    | .let d k =>
      match d.value with
      | .lit (.usize 1) =>
        modifyThe SplitSt fun st => { st with one := st.one.insert d.fvarId }
        return .let d (← splitCode cx src k)
      | .const f us args _ =>
        let keys := (← getThe MRetypeState).keys
        let op := (keys.find? f).map (·.decl)
        let arrArg ← match args[1]? with
          | some a => chain? a
          | none => pure none
        if let some x := arrArg then
          let some (xs, xd) := (← getThe SplitSt).pairs[x]? | splitFail
          let cnt := ((← getThe SplitSt).count[x]?).getD 0
          match op with
          | some ``Array.uget =>
            -- Possibly over-applied: the element of an array of functions
            -- applied to the function's arguments.
            unless args.size ≥ 4 && cnt == 0 && (← offOf args[2]!) == some 0 do splitFail
            noChain (args.eraseIdx! 1)
            let inst ← arrayExternAt ``Array.uget cx.α
            let d' := { d with type := if args.size == 4 then cx.α else d.type,
                               value := .const inst [] (#[.erased, .fvar xs, args[2]!, .erased] ++ args[4:].toArray) }
            return .let d' (← splitCode cx src k)
          | some ``Array.uset =>
            unless args.size == 5 && cnt == 0 && (← offOf args[2]!) == some 0 do splitFail
            noChain (args.eraseIdx! 1)
            if isPlaceholderArg (← getThe SplitSt).erased args[3]! then
              -- The placeholder, at `α`, into the source.
              let z ← mkFreshFVarId
              let zd : LetDecl .pure := { fvarId := z, binderName := `_x, type := cx.α, value := .erased }
              let inst ← arrayExternAt ``Array.uset cx.α
              let d' := { d with type := mkApp (mkConst ``Array) cx.α,
                                 value := .const inst [] #[.erased, .fvar xs, args[2]!, .fvar z, .erased] }
              modifyThe SplitSt fun st => { st with pairs := st.pairs.insert d.fvarId (d.fvarId, xd), count := st.count.insert d.fvarId 0, erased := st.erased.insert z }
              return .let zd (.let d' (← splitCode cx src k))
            -- The mapped value, pushed onto the result.
            let .fvar v := args[3]! | splitFail
            if (← norm (cx.types.getD v anyExpr)) != (← norm cx.β) then splitFail
            let inst ← arrayExternAt ``Array.push cx.β
            let d' := { d with type := mkApp (mkConst ``Array) cx.β, value := .const inst [] #[.erased, .fvar xd, .fvar v] }
            modifyThe SplitSt fun st => { st with pairs := st.pairs.insert d.fvarId (xs, d.fvarId), count := st.count.insert d.fvarId 1 }
            return .let d' (← splitCode cx src k)
          | some ``Array.usize | some ``Array.size =>
            unless args.size == 2 do splitFail
            let inst ← arrayExternAt op.get! cx.α
            return .let { d with value := .const inst [] #[.erased, .fvar xs] } (← splitCode cx src k)
          | _ => pure ()
        -- A call of this loop, or of the loop a wrapper calls.
        let callee? : Option (Option LoopShape) :=
          if f == cx.self then some (some cx.shape) else (cx.shapes.find? f).map some
        if let some (some sh) := callee? then
          if args.size == ((← getThe MRetypeState).sigs[f]?.map (·.params.size)).getD 0 then
            if let some y ← chain? args[sh.arrPos]! then
              let some (ys, yd) := (← getThe SplitSt).pairs[y]? | splitFail
              let cnt := ((← getThe SplitSt).count[y]?).getD 0
              unless (← offOf args[sh.idxPos]!) == some cnt do splitFail
              noChain (args.eraseIdx! sh.arrPos)
              let target ← if f == cx.self then pure cx.selfNew else do
                match ← ensureSplit f cx.α cx.β cx.shapes src with
                | some n => pure n
                | none => splitFail
              let args' := args[:sh.arrPos].toArray ++ #[.fvar ys, .fvar yd] ++ args[sh.arrPos + 1:].toArray
              return .let { d with value := .const target us args' } (← splitCode cx src k)
        if (← getEnv).isConstructor f then
          -- A result (`some bs`, `EST.Out.ok bs w`): the result array.
          let mut args' := #[]
          let mut any := false
          for a in args do
            match ← chain? a with
            | some y =>
              let some (_, yd) := (← getThe SplitSt).pairs[y]? | splitFail
              args' := args'.push (.fvar yd)
              any := true
            | none => args' := args'.push a
          if any then
            let ty ← replaceArrayAny d.type cx.β
            return .let { d with type := ty, value := .const f us args' } (← splitCode cx src k)
          return .let d (← splitCode cx src k)
        noChain args
        -- The loop index plus one.
        if f == ``USize.add && args.size == 2 then
          match args[0]!, args[1]! with
          | .fvar a, .fvar b =>
            if let some o := (← getThe SplitSt).off[a]? then
              if (← getThe SplitSt).one.contains b then modifyThe SplitSt fun st => { st with off := st.off.insert d.fvarId (o + 1) }
          | _, _ => pure ()
        return .let d (← splitCode cx src k)
      | .fvar _ args =>
        noChain args
        return .let d (← splitCode cx src k)
      | .proj _ _ x =>
        if (← getThe SplitSt).pairs.contains x then splitFail
        return .let d (← splitCode cx src k)
      | .erased =>
        modifyThe SplitSt fun st => { st with erased := st.erased.insert d.fvarId }
        return .let d (← splitCode cx src k)
      | _ => return .let d (← splitCode cx src k)
    | .jp d k =>
      -- The continuation first: its jumps say which parameters receive
      -- derived arrays (with their write counts).
      let k' ← splitCode cx src k
      let mut params := #[]
      for h : i in [:d.params.size] do
        let p := d.params[i]
        let seen := ((← getThe SplitSt).seen[(d.fvarId, i)]?).getD #[]
        let counts := seen.filterMap id
        if counts.isEmpty then
          params := params.push p
        else
          unless counts.size == seen.size && counts.all (· == counts[0]!) do splitFail
          let s ← mkFreshFVarId
          let t ← mkFreshFVarId
          params := params ++ #[{ p with fvarId := s, binderName := `src, type := mkApp (mkConst ``Array) cx.α },
            { p with fvarId := t, binderName := `dst, type := mkApp (mkConst ``Array) cx.β }]
          modifyThe SplitSt fun st => { st with pairs := st.pairs.insert p.fvarId (s, t), count := st.count.insert p.fvarId counts[0]! }
      let value ← splitCode cx src d.value
      let res := (splitArrows d.type d.params.size).2
      let ty := params.foldr (fun p acc => .forallE p.binderName p.type acc .default) res
      return .jp (FunDecl.mk d.fvarId d.binderName params ty value) k'
    | .fun d k _ =>
      -- A closure must not capture a derived array.
      for x in (← getThe SplitSt).pairs.keys do
        if hasFVarIn x d.value then splitFail
      return .fun d (← splitCode cx src k)
    | .cases cs =>
      if (← getThe SplitSt).pairs.contains cs.discr then splitFail
      let alts ← cs.alts.mapM fun
        | .alt ctor ps code _ => return .alt ctor ps (← splitCode cx src code)
        | .default code => return .default (← splitCode cx src code)
        | a => return a
      let resTy ← try replaceArrayAny cs.resultType cx.β catch _ => pure cs.resultType
      return .cases ⟨cs.typeName, resTy, cs.discr, alts⟩
    | .jmp j args =>
      let mut args' := #[]
      for h : i in [:args.size] do
        let a := args[i]
        let entry ← match ← chain? a with
          | some y =>
            let some (ys, yd) := (← getThe SplitSt).pairs[y]? | splitFail
            args' := args' ++ #[.fvar ys, .fvar yd]
            pure (some (((← getThe SplitSt).count[y]?).getD 0))
          | none =>
            args' := args'.push a
            pure none
        modifyThe SplitSt fun st => { st with seen := st.seen.insert (j, i) (((st.seen[(j, i)]?).getD #[]).push entry) }
      return .jmp j args'
    | .return x =>
      match (← getThe SplitSt).pairs[x]? with
      | some (_, xd) => return .return xd
      | none => return .return x
    | c => return c
where
  hasFVarIn (x : FVarId) (c : Code .pure) : Bool :=
    (codeFVars c {}).contains x
  codeFVars (c : Code .pure) (acc : FVarIdSet) : FVarIdSet :=
    match c with
    | .let d k =>
      let acc := match d.value with
        | .const _ _ args _ | .fvar _ args => args.foldl (fun s a => match a with | .fvar y => s.insert y | _ => s) acc
        | .proj _ _ y => acc.insert y
        | _ => acc
      let acc := match d.value with | .fvar g _ => acc.insert g | _ => acc
      codeFVars k acc
    | .jp d k | .fun d k _ => codeFVars k (codeFVars d.value acc)
    | .cases cs => cs.alts.foldl (fun s alt => codeFVars alt.getCode s) (acc.insert cs.discr)
    | .jmp _ args => args.foldl (fun s a => match a with | .fvar y => s.insert y | _ => s) acc
    | .return y => acc.insert y
    | _ => acc
end

/-- The entry calls of split `map` loops in `c` (an index argument bound to
the literal `0` and a source array of a precise type `Array α`): rewritten to
call the split instance with a new empty result array whose capacity is the
source's size. -/
partial def splitEntries (types : Types) (zeros : FVarIdSet) (shapes : NameMap LoopShape)
    (src : NameMap (Decl .pure × Types)) (c : Code .pure) : MRetypeM (Code .pure) := do
  match c with
  | .let d k =>
    let k' ← splitEntries types zeros shapes src k
    let .const f us args _ := d.value | return .let d k'
    let some sh := shapes.find? f | return .let d k'
    unless args.size == ((← get).sigs[f]?.map (·.params.size)).getD 0 do return .let d k'
    let .fvar x := args[sh.arrPos]! | return .let d k'
    let .fvar i := args[sh.idxPos]! | return .let d k'
    unless zeros.contains i do return .let d k'
    let xt := (types.getD x anyExpr).consumeMData.headBeta
    unless xt.isAppOfArity ``Array 1 do return .let d k'
    let α := xt.appArg!
    if ← unknown α then return .let d k'
    let some name ← ensureSplit f α sh.elem shapes src | return .let d k'
    let n ← mkFreshFVarId
    let e ← mkFreshFVarId
    let sizeI ← arrayExternAt ``Array.size α
    let emptyI ← arrayExternAt ``Array.emptyWithCapacity sh.elem
    let nd : LetDecl .pure := { fvarId := n, binderName := `_x, type := mkConst ``Nat,
                                value := .const sizeI [] #[.erased, .fvar x] }
    let ed : LetDecl .pure := { fvarId := e, binderName := `_x, type := mkApp (mkConst ``Array) sh.elem,
                                value := .const emptyI [] #[.erased, .fvar n] }
    let args' := args[:sh.arrPos].toArray ++ #[.fvar x, .fvar e] ++ args[sh.arrPos + 1:].toArray
    return .let nd (.let ed (.let { d with value := .const name us args' } k'))
  | .jp d k =>
    let v ← splitEntries types zeros shapes src d.value
    return .jp (FunDecl.mk d.fvarId d.binderName d.params d.type v) (← splitEntries types zeros shapes src k)
  | .fun d k _ =>
    let v ← splitEntries types zeros shapes src d.value
    return .fun (FunDecl.mk d.fvarId d.binderName d.params d.type v) (← splitEntries types zeros shapes src k)
  | .cases cs =>
    let alts ← cs.alts.mapM fun
      | .alt ctor ps code _ => return .alt ctor ps (← splitEntries types zeros shapes src code)
      | .default code => return .default (← splitEntries types zeros shapes src code)
      | a => return a
    return .cases ⟨cs.typeName, cs.resultType, cs.discr, alts⟩
  | c => return c

/-- Variables of `c` that hold the `USize` literal `0`: bound to it, or
join-point parameters that every jump passes such a variable. -/
partial def usizeZeros (c : Code .pure) : FVarIdSet := Id.run do
  let (lits, jps, jumps) := scan c ({}, #[], #[])
  let mut zeros := lits
  for _ in [:8] do
    let before := zeros.size
    for (j, ps) in jps do
      for h : i in [:ps.size] do
        let args := jumps.filterMap fun (j', as) => if j' == j then some as[i]? else none
        if !args.isEmpty && args.all (fun a => match a with | some (.fvar x) => zeros.contains x | _ => false) then
          zeros := zeros.insert ps[i]
    if zeros.size == before then break
  return zeros
where
  scan (c : Code .pure) (acc : FVarIdSet × Array (FVarId × Array FVarId) × Array (FVarId × Array (Arg .pure))) :
      FVarIdSet × Array (FVarId × Array FVarId) × Array (FVarId × Array (Arg .pure)) :=
    match c with
    | .let d k =>
      let (l, j, m) := acc
      scan k (if d.value matches .lit (.usize 0) then l.insert d.fvarId else l, j, m)
    | .jp d k =>
      let (l, j, m) := scan d.value acc
      scan k (l, j.push (d.fvarId, d.params.map (·.fvarId)), m)
    | .fun d k _ => scan k (scan d.value acc)
    | .cases cs => cs.alts.foldl (fun acc alt => scan alt.getCode acc) acc
    | .jmp j args => let (l, js, m) := acc; (l, js, m.push (j, args))
    | _ => acc

/-- Split the `map` loops whose element representation changes (see above):
rewrite their entry calls, add the split instances, and drop the original
loops that nothing reachable calls any more. -/
def splitMapLoops (decls : Array (Decl .pure)) (types : Array Types) (roots : Array Name) :
    MRetypeM (Array (Decl .pure)) := do
  let keys := (← get).keys
  let mut src : NameMap (Decl .pure × Types) := {}
  for h : i in [:decls.size] do
    let d := decls[i]
    if d.value matches .code _ && isMapLoop keys d.name then src := src.insert d.name (d, types[i]!)
  if src.isEmpty then return decls
  let mut shapes : NameMap LoopShape := {}
  for _ in [:3] do
    for (n, (d, ts)) in src.toList do
      unless shapes.contains n do
        if let some s ← loopShape? d ts shapes then shapes := shapes.insert n s
  if shapes.isEmpty then return decls
  let mut out := #[]
  for h : i in [:decls.size] do
    let d := decls[i]
    match d.value with
    | .code c => out := out.push { d with value := .code (← splitEntries types[i]! (usizeZeros c) shapes src c) }
    | _ => out := out.push d
  -- The split instances are built from the loops as they were, so a map
  -- loop entered inside another one's body (`a.map (·.map f)`) is still
  -- entered unsplit there: rewrite their entry calls too, until no new
  -- instance appears (each one is added to `splitDecls` as it is built).
  let mut added : Array (Decl .pure) := #[]
  let mut done := 0
  repeat
    let splits := (← get).splitDecls
    if done ≥ splits.size then break
    for h : j in [done:splits.size] do
      let (d, _, ts) ← localRetype splits[j]
      match d.value with
      | .code c => added := added.push { d with value := .code (← splitEntries ts (usizeZeros c) shapes src c) }
      | _ => added := added.push d
    done := splits.size
  if added.isEmpty then return decls
  let all := out ++ added
  -- Original loops nothing reachable calls any more.
  let bodies : NameMap (Code .pure) := all.foldl (fun m d => match d.value with
    | .code c => m.insert d.name c
    | _ => m) {}
  let mut live : NameSet := {}
  let mut work := roots.toList
  while !work.isEmpty do
    let n :: rest := work | break
    work := rest
    if live.contains n then continue
    live := live.insert n
    let some c := bodies.find? n | continue
    for (f, _, _) in constApps c #[] do
      unless live.contains f do work := f :: work
  return all.filter fun d => !(shapes.contains d.name) || live.contains d.name

/-- Registry entry point. -/
def Opt.SplitMapLoops.install (c : PassConfig) : PassConfig :=
  let prev := c.stage3.splitMapLoops
  { c with stage3 := { c.stage3 with splitMapLoops := fun decls types roots => do
      splitMapLoops (← prev decls types roots) types roots } }

end LeanToReussir
