import LeanToReussir.Lower.ExternCall

/-!
# Borrowed parameters: when resources are released

Native Lean passes some parameters *borrowed* (its `inferBorrow`, plus `@&`
annotations): the callee does not consume the argument, and the caller
releases it after the call, when the call was its last use. Reussir passes
every argument owned and releases a value at its last use, so a value
whose last use is inside the callee is released there, earlier than
natively. For most values nobody can tell. For resources whose release is
observable it shows (translation plan §5.8, §10): a file handle written and
dropped by a helper that then reads the same file (natively the data is
still in the handle's buffer), the stdin pipe of a child the helper then
waits for (natively the child does not see end of file), a promise whose
result task the helper then asks about (natively not resolved yet).

So for programs that create such resources (`resourceExterns`), lean2rr
runs Lean's own borrow inference on its mono declarations
(`inferBorrowedParams`) and emulates Lean's reference counting at the
calls where it matters:
- a direct call whose parameter is borrowed, with an argument the caller
  owns that may hold a resource, also inside a closure, a thunk or a task
  (`keepsAt`: by the flow analysis of Opt/ResourceFlow, in a program that
  casts by the mono type, `mayHoldRelease`), keeps the
  argument until the call returns (`l2r_release_after`), as Lean's
  `explicitRC` puts the caller's `dec` after the call; an argument the
  caller only borrows itself (a borrowed parameter, a field or array
  element of one, the value of a constant, a constructor without relevant
  fields: `borrowedVars`) is left alone, as natively (whoever lent it holds
  it), which also keeps tail calls of loops tail calls;
- a function value of such a declaration calls it through a `_boxed`
  variant that releases the borrowed arguments after the call, as Lean's
  `_boxed` functions do for closures.
-/

namespace LeanToReussir
open Lean Compiler LCNF

/-- C symbols of the externs that create resources whose release is
observable: files (closed and flushed with their last reference), child
processes (their pipes) and promises (the last reference to an unresolved
promise resolves its `result?` task with `none`, which `IO.hasFinished`,
`IO.wait` and the task's dependents see). -/
def resourceExterns : List String :=
  ["lean_io_prim_handle_mk", "lean_io_create_tempfile", "lean_io_process_spawn", "lean_io_promise_new"]

/-- Whether a declaration of the program calls an extern of
`resourceExterns`. -/
def programMakesResources (decls : NameMap (Decl .pure)) (keys : NameMap InstKey) : CoreM Bool := do
  let env ← getEnv
  for (_, d) in decls do
    let .code c := d.value | continue
    for f in codeConsts c #[] do
      let orig := (keys.find? f).map (·.decl) |>.getD f
      if let some sym := getExternNameFor env `c orig then
        if resourceExterns.contains sym then return true
  return false

/-- The declarations applied (`fap`) in impure code, with their numbers of
arguments. -/
partial def impureCalls (c : Code .impure) (acc : Array (Name × Nat)) : Array (Name × Nat) :=
  match c with
  | .let d k =>
    let acc := match d.value with
      | .fap f args => if args.isEmpty then acc else acc.push (f, args.size)
      | _ => acc
    impureCalls k acc
  | .jp d k => impureCalls k (impureCalls d.value acc)
  | .cases cs => cs.alts.foldl (fun acc alt => impureCalls alt.getCode acc) acc
  | .uset _ _ _ k _ | .sset _ _ _ _ _ k _ => impureCalls k acc
  | .inc _ _ _ _ k _ | .dec _ _ _ _ _ k _ => impureCalls k acc
  | .oset _ _ _ k _ | .setTag _ _ k _ | .del _ k _ => impureCalls k acc
  | _ => acc

/-- Lean's borrow inference on lean2rr's mono declarations `decls`: for each
declaration with code, which of its parameters Lean's `inferBorrow` marks
borrowed. Copies of the declarations go through the rest of Lean's
pipeline up to `inferBorrow`, as Lean compiles its own declarations after
`saveMono`: `toImpure`, then the impure passes before `inferBorrow`
(projections pushed into branches, reset/reuse inserted: a value reused in
place is owned). Extern instances get the borrow annotations (`@&`) of
their extern; a callee with no known signature takes its arguments owned.
The environment is restored afterwards. A failure is an error: the emulation is all or nothing, and the program
would silently get Reussir's release times. -/
def inferBorrowedParams (decls : Array (Decl .pure)) (keys : NameMap InstKey) :
    CoreM (NameMap (Array Bool)) := do
  withoutModifyingEnv do
    let fail (why : MessageData) : CoreM (NameMap (Array Bool)) :=
      throwError m!"lean2rr: Lean's borrow inference failed on this program ({why}), so the release \
        times of borrowed resources (files, child processes, promises) cannot be emulated (Lower/Borrow, \
        translation plan §5.8); internal error"
    let m ← getPassManager
    let some toImp := m.monoPassesNoLambda.find? (·.name == `toImpure) | fail "no `toImpure` pass"
    let some bi := m.impurePasses.findIdx? (·.name == `inferBorrow) | fail "no `inferBorrow` pass"
    let impure := m.impurePasses.extract 0 (bi + 1)
    -- Lean's inference takes every parameter of an exported declaration
    -- (`@[export]`, and `main`) owned (`isExport`), which it decides by
    -- name: so an instance of one is marked exported too (in this copy of
    -- the environment only).
    let env ← getEnv
    for d in decls do
      let .code _ := d.value | continue
      let orig := (keys.find? d.name).map (·.decl) |>.getD d.name
      if isExport env orig && !isExport (← getEnv) d.name then
        match exportAttr.setParam (← getEnv) d.name ((getExportNameFor? env orig).getD orig) with
        | .ok env' => setEnv env'
        | .error e => return ← fail m!"cannot mark {d.name} exported: {e}"
    try
      CompilerM.run (phase := .mono) do
        let names := decls.foldl (fun s d => s.insert d.name) ({} : NameSet)
        let mut ds := #[]
        for d in decls do
          let d ← match d.value, keys.find? d.name with
            | .extern _, some k =>
              match ← getImpureSignature? k.decl with
              | some sig =>
                pure { d with params := d.params.mapIdx fun i p =>
                  { p with borrow := (sig.params[i]?.map (·.borrow)).getD false } }
              | none => pure d
            | _, _ => pure d
          let d ← d.internalize
          -- Every declaration of the batch has a signature for `toImpure`.
          d.saveMono
          ds := ds.push d
        let mut state : (pu : Purity) × Array (Decl pu) := ⟨.pure, ds⟩
        for pass in #[toImp] ++ impure do
          if pass.name == `inferBorrow then
            -- Callees outside the batch without a signature: owned
            -- parameters.
            let st := state
            let impDecls ← st.fst.withAssertPurity .impure fun h => pure (h ▸ st.snd)
            for d in impDecls do
              if let .code c := d.value then
                for (f, n) in impureCalls c #[] do
                  unless names.contains f || (← getImpureSignature? f).isSome do
                    let ps ← (List.range n).toArray.mapM fun _ => do
                      return ({ fvarId := ← mkFreshFVarId, binderName := `x, type := ImpureType.object, borrow := false } : Param .impure)
                    let base : Decl .impure := default
                    let sig : Decl .impure := { base with name := f, params := ps, type := ImpureType.object, value := .extern { entries := [] } }
                    sig.saveImpure
          let st := state
          let out ← withPhase pass.phase do
            st.fst.withAssertPurity pass.phase.toPurity fun h => pass.run (h ▸ st.snd)
          state := ⟨_, out⟩
        let st := state
        let out ← st.fst.withAssertPurity .impure fun h => pure (h ▸ st.snd)
        return out.foldl (init := ({} : NameMap (Array Bool))) fun m d =>
          match d.value with
          | .code _ => m.insert d.name (d.params.map (·.borrow))
          | _ => m
    catch e => fail (← e.toMessageData.toString)

/-- The variables of declaration `d` that it only borrows (given which of
its parameters are borrowed), the values Lean's inference does not make
owned and after which its `explicitRc` puts no `dec`:
- its borrowed parameters;
- the fields and array elements read from such values (Lean's forward
  ownership propagation through projections, `cases` and `Array` reads); an
  element read with `a[i]!` (`Array.get!Internal α inst a i`) derives from
  the array and from the `Inhabited` instance, whose value it is when `i` is
  out of bounds, so both must be such values (Lean's `explicitRc` takes it
  as borrowed only while all its parents are, its inference owns it when
  either is owned);
- the values of constants (`isConst`: a declaration without parameters, a
  closed term, an `initialize` constant; Lean's `fap c #[]`: a constant
  stays alive);
- a constructor applied to no variable (`isCtor`): it holds nothing.
  Without relevant fields (`none`) it is Lean's scalar constructor, which
  nothing owns (`explicitRc` adds no `dec` for a value that is not a
  reference); with relevant fields that are all `◾` it allocates natively,
  but its release frees nothing observable, wherever it happens;
- the parameters of join points to which every jump passes such a value or
  no variable (`◾`): Lean infers a join point's parameter owned only when
  some jump passes an owned variable.
Whoever lent them still holds them (or they hold nothing). -/
partial def borrowedVars (keys : NameMap InstKey) (isConst isCtor : Name → Bool) (d : Decl .pure)
    (borrowed : Array Bool) : FVarIdSet := Id.run do
  let .code c := d.value | return {}
  let mut s := (d.params.zip borrowed).foldl (fun s (p, b) => if b then s.insert p.fvarId else s) {}
  -- Join points' parameters and the arguments of the jumps to them.
  let jps := joinPoints c {}
  let jumps := jumpArgs c {}
  repeat
    let s' := go c s
    let s' := jps.fold (init := s') fun s' j ps =>
      let argss := jumps.getD j #[]
      ps.zipIdx.foldl (init := s') fun s' (p, i) =>
        if !argss.isEmpty && argss.all (fun as => match as[i]? with
            | some (.fvar y) => s'.contains y
            | some _ => true
            | none => false) then s'.insert p else s'
    if s'.size == s.size then break
    s := s'
  return s
where
  -- The positions of the values an array read derives from: `getInternal`
  -- and `uget` take `α a i h` (the array), `get!Internal` takes
  -- `α inst a i` (the instance and the array).
  arrayRead (f : Name) : Option (Array Nat) :=
    let orig := (keys.find? f).map (·.decl) |>.getD f
    if orig == ``Array.getInternal || orig == ``Array.uget then some #[1]
    else if orig == ``Array.get!Internal then some #[1, 2]
    else none
  joinPoints (c : Code .pure) (m : Std.HashMap FVarId (Array FVarId)) : Std.HashMap FVarId (Array FVarId) :=
    match c with
    | .let _ k => joinPoints k m
    | .jp d k => joinPoints k (joinPoints d.value (m.insert d.fvarId (d.params.map (·.fvarId))))
    | .fun d k _ => joinPoints k (joinPoints d.value m)
    | .cases cs => cs.alts.foldl (fun m alt => joinPoints alt.getCode m) m
    | _ => m
  jumpArgs (c : Code .pure) (m : Std.HashMap FVarId (Array (Array (Arg .pure)))) :
      Std.HashMap FVarId (Array (Array (Arg .pure))) :=
    match c with
    | .let _ k => jumpArgs k m
    | .jp d k => jumpArgs k (jumpArgs d.value m)
    | .fun d k _ => jumpArgs k (jumpArgs d.value m)
    | .cases cs => cs.alts.foldl (fun m alt => jumpArgs alt.getCode m) m
    | .jmp j args => m.insert j ((m.getD j #[]).push args)
    | _ => m
  go (c : Code .pure) (s : FVarIdSet) : FVarIdSet :=
    match c with
    | .let d k =>
      let s := match d.value with
        | .proj _ _ y => if s.contains y then s.insert d.fvarId else s
        | .const f _ args _ =>
          if args.isEmpty && isConst f then s.insert d.fvarId
          else if isCtor f && args.all (!· matches .fvar _) then s.insert d.fvarId
          else match arrayRead f with
          | some ps =>
            -- Every parent such a value (a parent that is no variable
            -- holds nothing).
            if ps.all (fun i => match args[i]? with
                | some (.fvar y) => s.contains y
                | some _ => true
                | none => false) then s.insert d.fvarId else s
          | none => s
        | _ => s
      go k s
    | .cases cs =>
      let lent := s.contains cs.discr
      cs.alts.foldl (fun s alt =>
        let s := if lent then alt.getParams.foldl (fun s p => s.insert p.fvarId) s else s
        go alt.getCode s) s
    | .jp d k => go k (go d.value s)
    | .fun d k _ => go k (go d.value s)
    | _ => s

/-- Lean's borrow results for the program (computed once, when the program
creates resources), and the variables each declaration borrows. -/
def borrowInfo : LowerM (NameMap (Array Bool) × FVarIdSet) := do
  if let some r := (← get).borrowInfo then return r
  let ctx ← read
  let r ← if ← programMakesResources ctx.decls ctx.keys then
      let flags ← inferBorrowedParams (ctx.decls.foldl (fun a _ d => a.push d) #[]) ctx.keys
      let initSlots := (← get).initSlots
      let isConst (f : Name) : Bool :=
        initSlots.contains f || (ctx.decls.find? f).any (·.params.isEmpty)
      -- A constructor that is not a call (constructors that Lean's runtime
      -- implements, `Int.ofNat`, are externs).
      let env ← getEnv
      let isCtor (f : Name) : Bool :=
        (match env.find? f with | some (.ctorInfo _) => true | _ => false) && !isExtern env f
      let lent := ctx.decls.foldl (init := ({} : FVarIdSet)) fun s n d =>
        match flags.find? n with
        | some b => (borrowedVars ctx.keys isConst isCtor d b).foldl (fun s x => s.insert x) s
        | none => s
      pure (flags, lent)
    else pure ({}, {})
  modify fun s => { s with borrowInfo := some r }
  return r

/-- The answers of `mayHoldResource`, by mono type (after
`consumeMData.headBeta`), for the rest of the process: Opt/UnreadFields asks
it before Stage 4. An answer depends only on the type and on the
inductives of the environment, which only grows meanwhile: Opt/Flatten adds
its tuples, Opt/ModPow2, Opt/PreludeIntOps and Opt/Utf8SizeAdd add their
externs, and none of these changes an inductive that exists. One lean2rr
process translates one program (`Main.lean`: `run`), so the table never
mixes two environments. -/
initialize resourceTypeCache : IO.Ref (Std.HashMap Expr Bool) ← IO.mkRef {}

/-- The answers of `mayHoldResource` with `closures` (`mayHoldRelease`), as
`resourceTypeCache`'s: flatten-structs' type rule (in a program that casts),
the release order at a branch's start (`armReleaseVars`, `noteArmFields`)
and, in a program that casts, the lowering of borrowed arguments
(`keepsAt`) ask it. -/
initialize releaseTypeCache : IO.Ref (Std.HashMap Expr Bool) ← IO.mkRef {}

/-- Whether a value of mono type `e` may hold a resource with an
observable release (see `resourceExterns`): a handle (`IO.FS.Handle`, whose
mono type is `lcAny`), so also any value of unknown type (`lcAny`), or a
value of an inductive or array with such a field or element at its type
arguments (a reference is `lcAny` in mono code) (`IO.Process.Child` holds its pipes in `lcAny` fields;
`List Nat` holds none). Decided on mono types, not Reussir types: a field
of a parameter's type is a `Box` in every instantiation (one type per
inductive), which would make every container look like a handle's.
Closures, thunks and tasks are not looked into: with `closures`
(`mayHoldRelease`) each of them counts as one that may hold a resource. So:
whether a type that holds a resource is reachable from `e` through array
elements and constructor fields.

A plain reachability with one visited set per question (linear in the
types it reaches), memoized (`resourceTypeCache`, with `closures` `releaseTypeCache`) as rule 4's `mayHoldFn`:
a `true` holds for every type on the path that found it, a `false` for
every type the search visited. (Until 2026-10-26 the lowering searched
along every simple path, cutting a cycle on the path only, without a table:
a program that imports `Cslib.Init` spent 52 s of the 76 s it lowered
declarations there; then the searches kept a `false` only where the search
below met no type above it on the path, still exponential in the size of a
dense mutual block: RtResDenseMutual's eight members.) -/
partial def mayHoldResource (e : Expr) (closures : Bool := false) : CoreM Bool := do
  let cache := if closures then releaseTypeCache else resourceTypeCache
  let visited ← IO.mkRef ({} : Std.HashSet Expr)
  let found ← go cache e visited
  unless found do
    let vs ← visited.get
    cache.modify fun c => vs.fold (fun c t => c.insert t false) c
  return found
where
  /-- Whether a type that holds a resource is reachable from `e` through
  types not visited yet; `true` is kept for `e`. -/
  go (cache : IO.Ref (Std.HashMap Expr Bool)) (e : Expr) (visited : IO.Ref (Std.HashSet Expr)) : CoreM Bool := do
    let e := e.consumeMData.headBeta
    if let some r := (← cache.get)[e]? then return r
    if (← visited.get).contains e then return false
    visited.modify (·.insert e)
    let r ← search cache e visited
    if r then cache.modify (·.insert e true)
    return r
  /-- The rules for `e`, its array element and its constructors' fields
  through `go`. -/
  search (cache : IO.Ref (Std.HashMap Expr Bool)) (e : Expr) (visited : IO.Ref (Std.HashSet Expr)) : CoreM Bool := do
    if e.isSort then return false
    if e.isForall then return closures
    let .const n _ := e.getAppFn | return true
    if n == ``lcAny || n == ``IO.FS.Handle then return true
    if closures && (n == ``Thunk || n == ``Task) then return true
    let args := e.getAppArgs
    if n == ``Array then
      return ← match args[0]? with
        | some a => go cache a visited
        | none => pure true
    if n == ``lcErased || n == ``lcVoid || builtinTypeNames.contains n then return false
    let env ← getEnv
    let some ival := (match env.find? (n ++ `_impl), env.find? n with
        | some (.inductInfo iv), _ => some iv
        | _, some (.inductInfo iv) => some iv
        | _, _ => none) | return true
    if ival.type.getForallBody.isProp then return false
    let params := (List.range ival.numParams).toArray.map fun i => (args[i]?.getD anyExpr).consumeMData
    for c in ival.ctors do
      let mut ty ← instantiateForall (← getOtherDeclBaseType c []) params
      repeat
        match ty.headBeta with
        | .forallE _ d b _ =>
          let m ← toMonoTypeKeep d
          if !(m.isErased || m == mkConst ``lcVoid) then
            if ← go cache m visited then return true
          ty := b.instantiate1 anyExpr
        | _ => break
    return false

/-- Whether a value of mono type `e` may hold something whose release
shows: a resource (`mayHoldResource`), or a closure, a thunk or a task, which
may hold one (`mayHoldResource` does not look into them). -/
def mayHoldRelease (e : Expr) : CoreM Bool := mayHoldResource e (closures := true)

/-- The binders of code `c` with their mono types, in binding order: a
`let` before its continuation, the fields a `cases` binds before its
alternative's code, in field order, a local function (a closure) before
its continuation, the parameters of a join point or local function before
its body. A join point's continuation comes before its body: lean2rr can
copy the body to a jump in the continuation (J1, J1′), where the body's
variables then count as newer than the continuation's (natively the two
are never in scope together). -/
partial def armBinders (c : Code .pure) (acc : Array (FVarId × Expr)) : Array (FVarId × Expr) :=
  match c with
  | .let d k => armBinders k (acc.push (d.fvarId, d.type))
  | .jp d k =>
    armBinders d.value (d.params.foldl (fun a p => a.push (p.fvarId, p.type)) (armBinders k acc))
  | .fun d k _ =>
    armBinders d.value (d.params.foldl (fun a p => a.push (p.fvarId, p.type))
      (armBinders k (acc.push (d.fvarId, d.type))))
  | .cases cs => cs.alts.foldl (fun acc alt =>
      armBinders alt.getCode (alt.getParams.foldl (fun a p => a.push (p.fvarId, p.type)) acc)) acc
  | _ => acc

/-- For the release order at the start of a branch (Emit/ArmRelease): the
variables of the program that may hold something whose release shows
(`mayHoldRelease` of their mono type) and that their code owns, not those it
only borrows (`borrowInfo`'s lent variables: whoever lent them releases
them, so their release by this code is never the last one), each with its
binding order: its position in `armBinders` of its declaration (after the
declaration's parameters), the order of native Lean's binding indices
(`ExplicitRC`), on which the variables that lean2rr binds again (a field
converted to its own type, a field a `lazy-fields` match binds later, a
join point's parameter at an inlined jump) keep their place. Empty in a
program that makes no resources (`programMakesResources`: `borrowInfo` then
has no borrow flags, while it has them for every declaration with code,
`main` included, in one that does). Computed once, before the declarations
are lowered (`LowerState.armVars`). -/
def armReleaseVars : LowerM (Std.HashMap FVarId Nat) := do
  let (flags, lent) ← borrowInfo
  if flags.isEmpty then return {}
  let mut out : Std.HashMap FVarId Nat := {}
  let mut k := 0
  for (_, d) in (← read).decls do
    let .code c := d.value | continue
    for (x, ty) in armBinders c (d.params.map fun p => (p.fvarId, p.type)) do
      k := k + 1
      if !lent.contains x && (← mayHoldRelease ty) then out := out.insert x k
  return out

/-- For the release order at the start of a branch (Emit/ArmRelease):
which binders of the arm of variant `variant` of a `match` on `scrut` (the
Reussir name of Lean variable `discr`) may hold something whose release
shows (`mayHoldRelease`), recorded (`LowerState.armFields`) when the matched
value may (`armVars`).
The arm's fields are `ps`, at the binder positions `fields` gives
(`CtorLayout.fields`); a hidden field (an entry after the last of `ps`,
`IO.Process.Child`'s) counts as one that may. -/
def noteArmFields (discr : FVarId) (scrut variant : String) (ps : Array (Param .pure))
    (fields : Array (Option (Nat × RR.Ty))) (nbinders : Nat) : LowerM Unit := do
  unless (← getPart (·.armVars.contains discr)) do return
  let mut flags := Array.replicate nbinders false
  for h : i in [:fields.size] do
    if let some (j, _) := fields[i] then
      let may ← match ps[i]? with
        | some p => mayHoldRelease p.type
        | none => pure true
      if may then flags := flags.set! j true
  modify fun s => { s with armFields := s.armFields.insert (scrut, variant) flags }

/-- Whether an argument passed to parameter `p` of declaration `f`, which
Lean borrows, is kept until the call returns: when the parameter may hold
a resource. In a program that does not cast, by the flow analysis that
guards flatten-structs, run on the lowered declarations
(`LowerCtx.resourceHeld?`): it follows closures, thunks and tasks, so a
`Thunk IO.FS.Handle`, an `IO.FS.Stream` over a file or a callback that
captured a handle is kept, as natively, and a value that holds none is
not. Only for such parameters is lean2rr's code Lean's: flatten-structs
leaves alone the declarations whose parameters may hold one (and the
callees whose flags decide theirs), so the inference infers there what
native Lean infers. Elsewhere lean2rr's code differs (a split structure's
constructor is gone), and the inference can take a parameter borrowed that
native Lean takes owned: keeping its argument then broke a tail call that
native Lean makes (a cycle of tail calls that passes a new closure, thunk,
task or `lcAny` value, which the callee stores in a structure whose
reader flatten-structs splits, overflowed the stack: test
`RtBorrowCycleFlatten`); not keeping it releases a value that holds no
resource, which nobody can tell, but a pure task: its release time is
lean2rr's (plan §10, "Release time of pure tasks"). In a program that casts
(no flow analysis), by type (`mayHoldRelease`), as flatten-structs decides
there: what it may split holds nothing that the type rule counts. A
declaration the analysis did not see (none at present: it runs on the
declarations that are lowered) falls back to the type rule. -/
def keepsAt (f : Name) (p : Param .pure) : LowerM Bool := do
  let ctx ← read
  match ctx.resourceHeld? with
  | some held => if ctx.decls.contains f then return held.contains (f, p.fvarId) else mayHoldRelease p.type
  | none => mayHoldRelease p.type

/-- The arguments of a call of declaration `f` (arguments `args`, the
first `n` passed to `f`) that the caller keeps until the call returns: the
variables (name, type) the caller owns that are passed to a parameter Lean
borrows (at any position: `f x x` with the second parameter borrowed keeps
`x`) that may hold a resource (`keepsAt` of the first borrowed parameter it
is passed to). In the order of their first occurrence in
`args`, as Lean's `addDecAfterFullApp` visits them (`releaseAfter`
releases them in reverse). -/
def borrowKeeps (ctx : CodeCtx) (f : Name) (args : Array (Arg .pure)) (n : Nat) :
    LowerM (Array (String × RR.Ty)) := do
  let (flags, lent) ← borrowInfo
  let some bs := flags.find? f | return #[]
  let d? := (← read).decls.find? f
  let args := args.extract 0 n
  let mut out := #[]
  for h : i in [:args.size] do
    let .fvar x := args[i] | continue
    -- Its first occurrence only (Lean's `isFirstOcc`).
    if (args.extract 0 i).contains (.fvar x) then continue
    -- Passed to a borrowed parameter somewhere (Lean's `isBorrowParam`):
    -- the first such position.
    let some j := args.zipIdx.findSome? (fun (a, j) => if a == .fvar x && bs[j]?.getD false then some j else none)
      | continue
    if lent.contains x then continue
    let some (v, t) := ctx.vars[x]? | continue
    if out.any (·.1 == v) then continue
    -- The borrowed parameter it is passed to.
    let some p := (d?.bind (·.params[j]?)) | continue
    if ← keepsAt f p then out := out.push (v, t)
  return out

/-- `call` (of type `ret`) followed by the release of `keeps`: the value of
the call, with the kept variables released once it returns, **last first**.
Lean's `addDecAfterFullApp` visits the arguments in order and *prepends*
each `dec` to the code after the call, so the `dec`s run in the reverse
order of the arguments' first occurrences: `put3 a b c` with three dead
borrowed handles closes `c`, then `b`, then `a` (cross-test XT-1). Lean's
`_boxed` functions get the same treatment (`explicitRc` runs on them), so
`boxedTarget`'s wrappers release last parameter first too. -/
def releaseAfter (call : RR.Expr) (ret : RR.Ty) (keeps : Array (String × RR.Ty)) : LowerM RR.Expr := do
  if keeps.isEmpty then return call
  let r ← fresh "bw"
  let mut lets := #[(r, some ret, call)]
  for (v, t) in keeps.reverse do
    lets := lets.push (← fresh "bk", some (.named "u64"), .call "l2r_release_after" #[t] #[.var v])
  return .block ⟨lets, .var r⟩

/-- The function a function value of declaration `f` (Reussir function
`fn`, parameter types `params` by Lean position, of which it takes those
`keep` marks (rule 4a; empty: all), result `ret`) calls: `fn` itself, or,
when Lean borrows a parameter that may hold a resource (`keepsAt`, as
`borrowKeeps`), `fn_boxed`, which
releases the borrowed arguments after the call (Lean's `_boxed`). Lean's
borrow flags are by Lean position. -/
def boxedTarget (f : Name) (fn : String) (params : Array RR.Ty) (keep : Array Bool) (ret : RR.Ty) :
    LowerM String := do
  let (flags, _) ← borrowInfo
  let some bs := flags.find? f | return fn
  let some d := (← read).decls.find? f | return fn
  -- The parameters `fn` takes, with their Lean positions.
  let taken := params.zipIdx.filter fun (_, i) => keep[i]?.getD true
  let mut kept := #[]
  for h : k in [:taken.size] do
    let (_, i) := taken[k]
    if bs[i]?.getD false then
      let some p := d.params[i]? | continue
      if ← keepsAt f p then kept := kept.push k
  if kept.isEmpty then return fn
  let name := fn ++ "_boxed"
  unless (← hasFn name) do
    let ps := taken.mapIdx fun k (t, _) => (s!"a{k}", t)
    let body ← releaseAfter (.call fn #[] (ps.map (.var ·.1))) ret (kept.map fun k => (s!"a{k}", taken[k]!.1))
    modify fun s => { s with fns := s.fns.push (.fn name ps ret (.ofExpr body)) }
  return name

end LeanToReussir
