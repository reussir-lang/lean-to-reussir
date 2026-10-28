import Lean
import LeanToReussir.Collect
import LeanToReussir.Mono
import LeanToReussir.Passes
import LeanToReussir.CompileRecord
import LeanToReussir.ExtractClosedK
import LeanToReussir.MonoTypesKeep

/-!
# Stage 2: Lean's own mono pipeline, driven by lean2rr

Runs the passes Lean runs between `saveBase` and `saveMono`, plus
`extractClosed`, on the closed monomorphic program produced by Stage 1
(translation plan §3). The passes are taken from Lean's pass manager, so
their order and configuration are exactly Lean's, except for the edits of
`Stage2Config` (two passes replaced by lean2rr's copies, two not run; see
Opt/Registry.lean). Like
`PassManager.run`, the driver:

* processes strongly connected groups bottom-up (callees first), so that
  each pass can inline already-processed callees;
* runs each pass in its phase and checks the result with LCNF's checker;
* splits groups again after lambda lifting (`splitScc`).

Closed-term extraction (`extractClosed`, the last pass) runs at the end,
over all declarations, as Lean ran it (`extractLikeLean`).

Not run: module-visibility bookkeeping (`inferVisibility`), which does not
transform code, and everything from `toImpure` on — memory management
belongs to Reussir.
-/

namespace LeanToReussir
open Lean Compiler LCNF

/-- The three pass sequences of Stage 2, cut out of Lean's pass manager. -/
structure Stage2Passes where
  /-- `saveBase`, `toMono`. -/
  toMono : Array Pass
  /-- Lean's `monoPasses` (ends with lambda lifting). -/
  mono : Array Pass
  /-- Lean's `monoPassesNoLambda` up to `saveMono` (`extractClosed` runs
  separately, `extractLikeLean`). -/
  monoNoLambda : Array Pass

/-- An edit of Lean's pass lists for Stage 2, with its reason (the edits
are listed in Opt/Registry.lean). -/
inductive Stage2Edit where
  /-- Lean's pass `pass` is replaced by lean2rr's `by_`. -/
  | replace (pass : Name) (by_ : Pass) (why : String)
  /-- Lean's pass `pass` is not run. -/
  | skip (pass : Name) (why : String)

/-- lean2rr's edits of Lean's pass lists for Stage 2. -/
abbrev Stage2Config := Array Stage2Edit

/-- The three pass sequences of Stage 2: Lean's, edited by `cfg`. -/
def stage2Passes (cfg : Stage2Config) : CoreM Stage2Passes := do
  let m ← getPassManager
  let skipped (p : Pass) : Bool := cfg.any fun | .skip n _ => n == p.name | _ => false
  let replacement (p : Pass) : Option Pass := cfg.findSome? fun
    | .replace n q _ => if n == p.name then some q else none
    | _ => none
  let edit (ps : Array Pass) : Array Pass :=
    ps.filter (!skipped ·) |>.map fun p => (replacement p).getD p
  let some i := m.basePasses.findIdx? (·.name == `saveBase)
    | throwError "lean2rr: Lean's pass manager has no saveBase pass"
  return {
    toMono := edit m.basePasses[i:].toArray
    mono := edit m.monoPasses
    monoNoLambda := edit m.monoPassesNoLambda
  }

/-- Names of instance declarations called from `decl`. -/
def calledDecls (names : NameSet) (decl : Decl .pure) : List Name :=
  match decl.value with
  | .code c => (codeConsts c #[]).toList.filter names.contains
  | .extern _ => []

/-- Strongly connected groups of `decls`, callees before callers. -/
def sccsBottomUp (decls : Array (Decl .pure)) : Array (Array (Decl .pure)) :=
  let names := decls.foldl (fun s d => s.insert d.name) ({} : NameSet)
  let byName := decls.foldl (fun m d => m.insert d.name d) ({} : NameMap (Decl .pure))
  let groups := Lean.SCC.scc (decls.toList.map (·.name)) fun n =>
    match byName.find? n with
    | some d => calledDecls names d
    | none => []
  groups.toArray.map fun g => g.toArray.filterMap byName.find?

/-- The declarations in a cycle of direct calls (a strongly connected group
of more than one, or one that calls itself), each with the names of its
group. -/
def callCycles (decls : Array (Decl .pure)) : NameMap NameSet := Id.run do
  let names := decls.foldl (fun s d => s.insert d.name) ({} : NameSet)
  let mut out : NameMap NameSet := {}
  for g in sccsBottomUp decls do
    let loops := g.size > 1 || g.any fun d => (calledDecls names d).contains d.name
    if loops then
      let members := g.foldl (fun s d => s.insert d.name) ({} : NameSet)
      for d in g do out := out.insert d.name members
  return out

/-- The name in Lean's own compilation of the declaration a Stage 2
declaration comes from, and the key of its instance: an instance `f._l2r.k`
comes from `f` (`keys`), and a declaration a pass made from an instance
has the instance's name with suffixes (`f._l2r.k._lam_0` comes from
`f._lam_0`). -/
partial def leanNameOf (keys : NameMap InstKey) (n : Name) : Option (Name × InstKey) :=
  match keys.find? n with
  | some k => some (k.decl, k)
  | none =>
    let (p, s) : Name × Option String :=
      if n.hasMacroScopes then
        let v := extractMacroScopes n
        match v.name with
        | .str p s => ({ v with name := p }.review, some s)
        | .num p _ => ({ v with name := p }.review, none)
        | .anonymous => (.anonymous, none)
      else match n with
        | .str p s => (p, some s)
        | .num p _ => (p, none)
        | .anonymous => (.anonymous, none)
    if p.isAnonymous then none
    else (leanNameOf keys p).map fun (q, k) => (s.map (q ++ Name.mkSimple ·) |>.getD q, k)

/-- A marker of `closedMonoKey` (a name no program can declare: its last
component is a number). -/
def closedInstMarker : Expr := .const (Name.mkNum `_l2r_closed_inst 0) []

/-- The key under which `extractLikeLean` caches closed term `e` (its code
as an expression, `Code.toExpr`, of type `ty`) besides Lean's own cache:
`e` with each instance `f._l2r.k`, and its `_redArg` (Lean's `reduceArity`
copy), replaced by `f` (or `f._redArg`), the mono images of its type
arguments (`toMonoTypeKeep`) and its static dictionaries. Natively one
function serves every type, and Lean's closed-term cache compares mono
terms, in which type arguments are erased and types are mono types: `mk 5`
at `Option (Fin 3)`, at `Option Nat` and at `Option W` (`structure W where
x : Nat`) is one term, `mk ◾ 5 : Option Nat`, made once (bug hunt of the
extern routing, test `RtClosedMonoEqual`); Stage 1 gives the calls
instances at `Fin 3`, `Nat` and `W`, whose code is the same mono code. The
key is used only when its instances' images are precise and `ty` serves at
itself (`serves`, so it mentions no `lcAny`, which could hide a type
argument): `none` when `e` names no instance, when an image has an `lcAny`
that its type argument has not (the instance at a type former such as `fun
α => Nat → α × Nat`, whose image is `lcAny`, has code of its own; an
argument that is `lcAny` itself, a hidden or uniform one, is the same in
both instances), or when `ty` does not serve. Other
declarations a pass made from an instance (`_lam_N`, `_closed_N`) are
compared by name, as Lean's cache does: their numbering follows the
extraction's order, not only the instance. Used only in a declaration whose
code is concrete natively too (`monoOwner`). -/
def closedMonoKey (keys : NameMap InstKey) (e ty : Expr) : CoreM (Option Expr) := do
  let mut images : NameMap Expr := {}
  for c in e.getUsedConstants do
    let (inst, suffix) : Name × Name := match c with
      | .str p "_redArg" => if keys.contains p then (p, `_redArg) else (c, .anonymous)
      | _ => (c, .anonymous)
    let some key := keys.find? inst | continue
    let tys ← key.typeArgs.mapM toMonoTypeKeep
    -- An `lcAny` the image introduced loses what tells instances apart
    -- (one already in the type argument is the same in both).
    if (key.typeArgs.zip tys).any (fun (t, i) => mentionsAny i && t != i) then return none
    let dicts := key.dicts.map (·.getD erasedExpr)
    images := images.insert c
      (mkApp3 closedInstMarker (.const (key.decl ++ suffix) []) (mkAppN (.const ``Array.mk []) tys)
        (mkAppN (.const ``List.cons []) dicts))
  if images.isEmpty then return none
  unless ← (serves ty ty).run' {} do return none
  return some (e.replace fun x => match x with
    | .const c _ => images.find? c
    | _ => none)

/-- Is declaration `n` (Stage 2's) made from an instance without type
arguments, or with `lcAny` for each (`leanNameOf`)? Natively such code has
the types it has here (a monomorphic declaration, or one of Lean's
specializations), so its closed terms are the mono terms Lean's cache
compares. An instance of a generic declaration has concrete types where
the generic code native Lean runs has `lcAny`: `mk2 7` in `gen {α}` at
`W` is natively a term at `Option lcAny`, which Lean's cache does not
share with `user`'s `mk2 7 : Option Nat`, so `closedMonoKey` would share
more than native (review of the bug hunt of the extern routing,
2026-10-28). -/
def monoOwner (keys : NameMap InstKey) (n : Name) : Bool :=
  match leanNameOf keys n with
  | some (_, key) => key.typeArgs.all (· == anyExpr)
  | none => false

/-- Closed-term extraction as Lean ran it, on the declarations Stage 2's
other passes produced (`sccs`, Stage 2's groups after lambda lifting).
Lean runs `extractClosed` module by module, in compilation order, with a
cache of the closed terms the module made so far: a declaration with a
term equal to an earlier one's reads the earlier one's (and, making none
of its own, keeps the values the extraction left dead), and Lean's option
`compiler.extract_closed false` turns it off. So does lean2rr, from the
record of each declaration's module (`closedRecord`):
* the declarations whose extraction made closed terms (`d._closed_N` among
  the module's IR-only declarations) are extracted first, in the order
  Lean made their first closed term, with one cache per module, so the same
  declarations own the shared terms and read them as Lean's did;
* then the others: one whose IR reads a closed term (it only found terms in
  the cache) is extracted, and keeps the calls the extraction left dead
  but not the dead reads of closed terms, which Lean's impure phase drops
  (`Decl.elimDeadLikeImpure`); one whose IR reads none is left as it is. Lean
  extracted nothing there: there was nothing to extract, or extraction was
  off, and either way Lean's code computes at each call what an instance
  here might have as a closed term (also a dictionary built from instances
  known here). When the module's IR bodies are unknown, a module where
  Lean made no closed term at all is left as it is.
Extracted as usual, as nothing in the record applies: a declaration Lean
compiled to no IR (lean2rr translates the reference definition of an
`@[implemented_by]` declaration), and the Lean definition of an extern of
the program (`Mono.ExternRoute.body`), which Lean compiled to an extern
declaration without a body: lean2rr compiles it as if it were not an
extern, so its closed terms are extracted as Lean would extract them. A
declaration Lean's compilation does not have (one a pass made only here)
follows the one it comes from. -/
def extractLikeLean (keys : NameMap InstKey) (sccs : Array (Array (Decl .pure))) :
    CompilerM (Array (Decl .pure)) := do
  unless (← getConfig).extractClosed do return sccs.flatten
  let env ← getEnv
  let leanName (n : Name) : Name := (keys.find? n).map (·.decl) |>.getD n
  let mut records : Std.HashMap Nat ClosedRecord := {}
  -- (module, order key, original index, scc index, extract?) per declaration.
  let mut items : Array (Option Nat × Nat × Nat × Nat × Bool) := #[]
  let flat := sccs.flatten
  let mut sccOf : Array Nat := #[]
  for h : i in [:sccs.size] do
    for _ in sccs[i] do sccOf := sccOf.push i
  for h : i in [:flat.size] do
    let d := flat[i]
    let some (nat, key) := leanNameOf keys d.name
      | items := items.push (none, i, i, sccOf[i]!, true); continue
    let some midx := env.getModuleIdxFor? key.decl
      | items := items.push (none, i, i, sccOf[i]!, true); continue
    let midx := midx.toNat
    unless records.contains midx do records := records.insert midx (← closedRecord midx)
    let record := records.getD midx {}
    -- The declaration of Lean's compilation it follows: itself, or the one
    -- a pass made it from.
    let src := (compiledOwner (fun n => record.known.contains n || env.contains n) nat).getD key.decl
    let extract :=
      if record.makers.contains src then true
      else if !record.known.contains src then true
      -- Code of an extern: the Lean definition of an extern of the program.
      else if isExtern env src then true
      else match record.readers with
        | some rs => rs.contains src
        | none => !record.makers.isEmpty
    let order := if record.makers.contains src then record.firstClosed.getD src 0
      else record.firstClosed.size + flat.size
    items := items.push (some midx, order, i, sccOf[i]!, extract)
  -- Module by module, each with a fresh cache.
  let sorted := items.qsort fun (m1, k1, i1, _, _) (m2, k2, i2, _, _) =>
    let (a, b) := (m1.map (· + 1) |>.getD 0, m2.map (· + 1) |>.getD 0)
    a < b || (a == b && (k1 < k2 || (k1 == k2 && i1 < i2)))
  let mut results : Std.HashMap Nat (Array (Decl .pure)) := {}
  let mut current : Option (Option Nat) := none
  -- The module's closed terms by `closedMonoKey`, besides Lean's cache.
  let monoCache ← IO.mkRef ({} : Std.HashMap Expr Name)
  for (m, _, i, sccIdx, extract) in sorted do
    if current != some m then
      modifyEnv (closedTermCacheExt.setState · {})
      monoCache.set {}
      current := some m
    let d := flat[i]!
    -- Only a declaration whose code is concrete natively too (`monoOwner`)
    -- looks up or adds terms under `closedMonoKey`.
    let monoKey (e ty : Expr) : CompilerM (Option Expr) :=
      if monoOwner keys d.name then closedMonoKey keys e ty else pure none
    let res ← if extract then withPhase .mono (d.extractClosedK sccs[sccIdx]! leanName monoKey monoCache)
      else pure #[d]
    -- What Lean's impure phase then drops (see `Decl.elimDeadLikeImpure`).
    results := results.insert i (← res.mapM (·.elimDeadLikeImpure))
  -- In Stage 2's order, each declaration after the closed terms it made.
  let mut out := #[]
  for h : i in [:flat.size] do out := out ++ results.getD i #[flat[i]]
  return out

/-- The variables of `targets` that code `c` uses, each once, in the order of
their first use, appended to `acc` (it stops when it has found them all). -/
partial def firstUses (targets : Std.HashSet FVarId) (c : Code .pure) (acc : Array FVarId) : Array FVarId :=
  let use (acc : Array FVarId) (x : FVarId) : Array FVarId :=
    if targets.contains x && !acc.contains x then acc.push x else acc
  let useArgs (acc : Array FVarId) (args : Array (Arg .pure)) : Array FVarId :=
    args.foldl (fun acc a => match a with | .fvar x => use acc x | _ => acc) acc
  if acc.size == targets.size then acc else
  match c with
  | .let d k =>
    let acc := match d.value with
      | .proj _ _ x => use acc x
      | .const _ _ args => useArgs acc args
      | .fvar f args => useArgs (use acc f) args
      | _ => acc
    firstUses targets k acc
  | .fun d k _ | .jp d k => firstUses targets k (firstUses targets d.value acc)
  | .jmp _ args => useArgs acc args
  | .cases cs => cs.alts.foldl (fun acc alt => firstUses targets alt.getCode acc) (use acc cs.discr)
  | .return x => use acc x
  | _ => acc

/-- `ty` (a function type of at least `n` arguments) with its first `n`
domains in the order `perm`; `none` if one of them, or the rest of the
type, depends on one of them. -/
def permuteDomains (ty : Expr) (n : Nat) (perm : Array Nat) : Option Expr := Id.run do
  let mut doms : Array (Name × Expr × BinderInfo) := #[]
  let mut t := ty
  for _ in [:n] do
    let .forallE x d b bi := t | return none
    if d.hasLooseBVars then return none
    doms := doms.push (x, d, bi)
    t := b
  if t.hasLooseBVars then return none
  return some (perm.foldr (init := t) fun i acc =>
    let (x, d, bi) := doms[i]!
    .forallE x d acc bi)

/-- The order of join point `d`'s parameters by their first use in its
body `body` (`firstUses`; the unused ones last, in their order), and its
type with its domains in that order; `none` if that is its order, or if
its type depends on a parameter (`permuteDomains`). -/
def jpParamOrder? (d : FunDecl .pure) (body : Code .pure) : Option (Array Nat × Expr) := do
  let n := d.params.size
  guard (n ≥ 2)
  let order := firstUses (d.params.foldl (·.insert ·.fvarId) {}) body #[]
  let rank : Std.HashMap FVarId Nat := order.zipIdx.foldl (fun m (x, i) => m.insert x i) {}
  let key (i : Nat) : Nat := (rank[d.params[i]!.fvarId]?).getD (n + i)
  let perm := (Array.range n).qsort fun i j => key i < key j
  guard (perm != Array.range n)
  return (perm, ← permuteDomains d.type n perm)

/-- Code `c` with the parameters of each join point in the order of their
first use in its body (`jpParamOrder?`, after the same reordering inside
it), and the arguments of each jump in that order too; `perms`: the new
orders of the join points in scope. -/
partial def stableJpParamsCode (perms : Std.HashMap FVarId (Array Nat)) (c : Code .pure) : Code .pure :=
  match c with
  | .let d k => .let d (stableJpParamsCode perms k)
  | .fun d k _ =>
    .fun (.mk d.fvarId d.binderName d.params d.type (stableJpParamsCode perms d.value)) (stableJpParamsCode perms k)
  | .jp d k =>
    -- A join point's body does not jump to it (LCNF): only `k` does.
    let body := stableJpParamsCode perms d.value
    match jpParamOrder? d body with
    | some (perm, ty) =>
      .jp (.mk d.fvarId d.binderName (perm.map (d.params[·]!)) ty body)
        (stableJpParamsCode (perms.insert d.fvarId perm) k)
    | none => .jp (.mk d.fvarId d.binderName d.params d.type body) (stableJpParamsCode perms k)
  | .jmp j args =>
    match perms[j]? with
    | some perm => .jmp j (perm.map (args[·]!))
    | none => c
  | .cases cs => .cases (cs.updateAlts (cs.alts.map fun alt => alt.updateCode (stableJpParamsCode perms alt.getCode)))
  | c => c

/-- The program `decls` with the parameters of every join point that its
body uses in the order of their first use, and the unused ones last in
their old order (`stableJpParamsCode`): Lean's `extendJoinPointContext`
adds the variables a join point uses as its parameters in the order of a
hash map over their unique ids, which the one counter of Stage 2's session
draws for the whole program, so a definition added anywhere reordered them
(a join point's tuple type, an outlined function's parameters, a state
machine's slots). A join point whose type depends on its parameters keeps
its order. Known gap: the old order of the unused parameters is still
Lean's hash order. Lean runs no `reduceJpArity` after
`extendJoinPointContext`, and `elimDeadBranches` can make a use
unreachable, so a join point can keep unused parameters; two or more of
them can still change order when an unrelated definition is added (rare;
results are not affected). -/
def stableJpParams (decls : Array (Decl .pure)) : Array (Decl .pure) :=
  decls.map fun d => match d.value with
    | .code c => { d with value := .code (stableJpParamsCode {} c) }
    | _ => d

/-- Stage 2 on the output of Stage 1 (`keys`: Stage 1's instances).
Returns the mono declarations (instances plus the declarations passes
created: `_redArg`, `_lam_N`, `_closed_N`, …), the parameters of their join
points in a stable order (`stableJpParams`). -/
def runStage2 (cfg : Stage2Config) (decls : Array (Decl .pure)) (externs : Array (Decl .pure))
    (keys : NameMap InstKey) (check := true) : CoreM (Array (Decl .pure)) := do
  let passes ← stage2Passes cfg
  CompilerM.run (phase := .base) do
    let mut out := #[]
    -- Extern instances only need their signatures converted.
    -- Declarations come from separate Stage 1 contexts; like Lean's driver,
    -- internalize them into this context before running passes on them.
    unless externs.isEmpty do
      let externs ← externs.mapM (·.internalize)
      out := out ++ (← runPasses passes.toMono externs check)
    let mut sccs := #[]
    for group in sccsBottomUp decls do
      let group ← group.mapM (·.internalize)
      let group := markRecDecls group
      let group ← runPasses passes.toMono group check
      let group ← runPasses passes.mono group check
      for scc in ← splitScc group do
        sccs := sccs.push (← runPasses passes.monoNoLambda scc check)
    -- `extractClosed` (not in the pass lists, see Opt/Registry.lean) last,
    -- on Lean's own code; then the join points' parameters in a stable
    -- order.
    return stableJpParams (out ++ (← extractLikeLean keys sccs))

end LeanToReussir
