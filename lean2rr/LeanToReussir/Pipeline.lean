import Lean
import LeanToReussir.TypedToMono
import LeanToReussir.TypedStructProjCases
import LeanToReussir.Collect
import LeanToReussir.Mono
import LeanToReussir.Passes

/-!
# Stage 2: Lean's own mono pipeline, driven by lean2rr

Runs the passes Lean runs between `saveBase` and `saveMono`, plus
`extractClosed`, on the closed monomorphic program produced by Stage 1
(translation plan §3). The passes are taken from Lean's pass manager, so
their order and configuration are exactly Lean's. Like
`PassManager.run`, the driver:

* processes strongly connected groups bottom-up (callees first), so that
  each pass can inline already-processed callees;
* runs each pass in its phase and checks the result with LCNF's checker;
* splits groups again after lambda lifting (`splitScc`).

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
  /-- Lean's `monoPassesNoLambda` up to `saveMono`, plus `extractClosed`. -/
  monoNoLambda : Array Pass

def stage2Passes : CoreM Stage2Passes := do
  let m ← getPassManager
  let skip (p : Pass) := p.name == `inferVisibility || p.name == `toImpure
  let some i := m.basePasses.findIdx? (·.name == `saveBase)
    | throwError "lean2rr: Lean's pass manager has no saveBase pass"
  return {
    -- Lean's `toMono`, with types that keep constant type families.
    toMono := m.basePasses[i:].toArray.filter (!skip ·) |>.map fun p =>
      if p.name == `toMono then Lean.Compiler.LCNF.toMonoK else p
    mono := m.monoPasses.filter (!skip ·) |>.map fun p =>
      if p.name == `structProjCases then Lean.Compiler.LCNF.structProjCasesK else p
    monoNoLambda := m.monoPassesNoLambda.filter (!skip ·) |>.map fun p =>
      if p.name == `structProjCases then Lean.Compiler.LCNF.structProjCasesK else p
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

/-- Stage 2 on the output of Stage 1. Returns the mono declarations
(instances plus the declarations passes created: `_redArg`, `_lam_N`,
`_closed_N`, …). -/
def runStage2 (decls : Array (Decl .pure)) (externs : Array (Decl .pure)) (check := true) :
    CoreM (Array (Decl .pure)) := do
  let passes ← stage2Passes
  CompilerM.run (phase := .base) do
    let mut out := #[]
    -- Extern instances only need their signatures converted.
    -- Declarations come from separate Stage 1 contexts; like Lean's driver,
    -- internalize them into this context before running passes on them.
    unless externs.isEmpty do
      let externs ← externs.mapM (·.internalize)
      out := out ++ (← runPasses passes.toMono externs check)
    for group in sccsBottomUp decls do
      let group ← group.mapM (·.internalize)
      let group := markRecDecls group
      let group ← runPasses passes.toMono group check
      let group ← runPasses passes.mono group check
      for scc in ← splitScc group do
        out := out ++ (← runPasses passes.monoNoLambda scc check)
    return out

end LeanToReussir
