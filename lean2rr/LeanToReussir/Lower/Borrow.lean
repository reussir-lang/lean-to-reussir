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
waits for (natively the child does not see end of file).

So for programs that create such resources (`resourceExterns`), lean2rr
runs Lean's own borrow inference on its mono declarations
(`inferBorrowedParams`) and emulates Lean's reference counting at the
calls where it matters:
- a direct call whose parameter is borrowed, with an argument the caller
  owns of a type that may hold a resource (`mayHoldResource`, on mono
  types), keeps the
  argument until the call returns (`l2r_release_after`), as Lean's
  `explicitRC` puts the caller's `dec` after the call; an argument the
  caller only borrows itself (a borrowed parameter, or a field or array
  element of one) is left alone, as natively (whoever lent it holds it),
  which also keeps tail calls of loops tail calls;
- a function value of such a declaration calls it through a `_boxed`
  variant that releases the borrowed arguments after the call, as Lean's
  `_boxed` functions do for closures.
-/

namespace LeanToReussir
open Lean Compiler LCNF

/-- C symbols of the externs that create resources whose release is
observable: files (closed and flushed with their last reference) and child
processes (their pipes). -/
def resourceExterns : List String :=
  ["lean_io_prim_handle_mk", "lean_io_create_tempfile", "lean_io_process_spawn"]

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
        times of borrowed resources (files, child processes) cannot be emulated (Lower/Borrow, \
        translation plan §5.8); internal error"
    let m ← getPassManager
    let some toImp := m.monoPassesNoLambda.find? (·.name == `toImpure) | fail "no `toImpure` pass"
    let some bi := m.impurePasses.findIdx? (·.name == `inferBorrow) | fail "no `inferBorrow` pass"
    let impure := m.impurePasses.extract 0 (bi + 1)
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
its parameters are borrowed): its borrowed parameters, the fields and array
elements read from those (Lean's forward ownership propagation through
projections, `cases` and `Array` reads), and the parameters of join points
that every jump passes such a variable (Lean infers a join point's
parameter owned only when some jump passes an owned value). Lean has no
`dec` for them after a call: whoever lent them still holds them. -/
partial def borrowedVars (keys : NameMap InstKey) (d : Decl .pure) (borrowed : Array Bool) : FVarIdSet := Id.run do
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
            | _ => false) then s'.insert p else s'
    if s'.size == s.size then break
    s := s'
  return s
where
  arrayRead (f : Name) : Option Nat :=
    let orig := (keys.find? f).map (·.decl) |>.getD f
    if orig == ``Array.getInternal || orig == ``Array.get!Internal || orig == ``Array.uget then some 1
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
          match arrayRead f with
          | some i => match args[i]? with
            | some (.fvar y) => if s.contains y then s.insert d.fvarId else s
            | _ => s
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
      let lent := ctx.decls.foldl (init := ({} : FVarIdSet)) fun s n d =>
        match flags.find? n with
        | some b => (borrowedVars ctx.keys d b).foldl (fun s x => s.insert x) s
        | none => s
      pure (flags, lent)
    else pure ({}, {})
  modify fun s => { s with borrowInfo := some r }
  return r

/-- Whether a value of mono type `e` may hold a resource with an
observable release (see `resourceExterns`): a handle (`IO.FS.Handle`, whose
mono type is `lcAny`), so also any value of unknown type (`lcAny`), or a
value of an inductive or array with such a field or element at its type
arguments (a reference is `lcAny` in mono code) (`IO.Process.Child` holds its pipes in `lcAny` fields;
`List Nat` holds none). Decided on mono types, not Reussir types: a field
of a parameter's type is a `Box` in every instantiation (one type per
inductive), which would make every container look like a handle's.
Closures, thunks and tasks are not looked into. Types already being
examined count as not holding one (the least fixed point). -/
partial def mayHoldResource (e : Expr) (seen : Array Expr := #[]) : LowerM Bool := do
  let e := e.consumeMData.headBeta
  if seen.contains e then return false
  let seen := seen.push e
  if e.isForall || e.isSort then return false
  let .const n _ := e.getAppFn | return true
  if n == ``lcAny || n == ``IO.FS.Handle then return true
  let args := e.getAppArgs
  if n == ``Array then
    return ← match args[0]? with
      | some a => mayHoldResource a seen
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
          if ← mayHoldResource m seen then return true
        ty := b.instantiate1 anyExpr
      | _ => break
  return false

/-- The arguments of a call of declaration `f` (arguments `args`, the
first `n` passed to `f`) that the caller keeps until the call returns: the
variables (name, type) the caller owns that are passed to a parameter Lean
borrows (at any position: `f x x` with the second parameter borrowed keeps
`x`), of a type that may hold a resource. In the order of their first
occurrence in `args`, as Lean's `addDecAfterFullApp` visits them
(`releaseAfter` releases them in reverse). -/
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
    -- Passed to a borrowed parameter somewhere (Lean's `isBorrowParam`).
    unless args.zipIdx.any (fun (a, j) => a == .fvar x && bs[j]?.getD false) do continue
    if lent.contains x then continue
    let some (v, t) := ctx.vars[x]? | continue
    if out.any (·.1 == v) then continue
    -- The type of the parameter it is passed to (the variable's).
    let some p := (d?.bind (·.params[i]?)) | continue
    if ← mayHoldResource p.type then out := out.push (v, t)
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
when Lean borrows a parameter that may hold a resource, `fn_boxed`, which
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
      if ← mayHoldResource p.type then kept := kept.push k
  if kept.isEmpty then return fn
  let name := fn ++ "_boxed"
  unless (← hasFn name) do
    let ps := taken.mapIdx fun k (t, _) => (s!"a{k}", t)
    let body ← releaseAfter (.call fn #[] (ps.map (.var ·.1))) ret (kept.map fun k => (s!"a{k}", taken[k]!.1))
    modify fun s => { s with fns := s.fns.push (.fn name ps ret (.ofExpr body)) }
  return name

end LeanToReussir
