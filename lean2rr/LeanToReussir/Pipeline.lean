import Lean
import LeanToReussir.Collect
import LeanToReussir.Mono
import LeanToReussir.Passes
import LeanToReussir.CompileRecord
import LeanToReussir.ExtractClosedK

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
`@[extern]` or `@[implemented_by]` declaration). A declaration Lean's
compilation does not have (one a pass made only here) follows the one it
comes from. -/
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
  for (m, _, i, sccIdx, extract) in sorted do
    if current != some m then
      modifyEnv (closedTermCacheExt.setState · {})
      current := some m
    let d := flat[i]!
    let res ← if extract then withPhase .mono (d.extractClosedK sccs[sccIdx]! leanName) else pure #[d]
    -- What Lean's impure phase then drops (see `Decl.elimDeadLikeImpure`).
    results := results.insert i (← res.mapM (·.elimDeadLikeImpure))
  -- In Stage 2's order, each declaration after the closed terms it made.
  let mut out := #[]
  for h : i in [:flat.size] do out := out ++ results.getD i #[flat[i]]
  return out

/-- Stage 2 on the output of Stage 1 (`keys`: Stage 1's instances).
Returns the mono declarations (instances plus the declarations passes
created: `_redArg`, `_lam_N`, `_closed_N`, …). -/
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
    -- `extractClosed` (not in the pass lists, see Opt/Registry.lean) last.
    return out ++ (← extractLikeLean keys sccs)

end LeanToReussir
