import Lean

/-!
# Running Lean's LCNF passes

Shared by Stage 1 (compiling safe reference definitions) and Stage 2.
-/

namespace LeanToReussir
open Lean Compiler LCNF

/-- Run `passes` over `decls` exactly as `PassManager.runPassManagerPart`
does, but restricted to pure phases (base and mono). -/
def runPasses (passes : Array Pass) (decls : Array (Decl .pure)) (check : Bool) :
    CompilerM (Array (Decl .pure)) := do
  let mut state : (pu : Purity) × Array (Decl pu) := ⟨.pure, decls⟩
  for pass in passes do
    let decls ← withPhase pass.phase do
      state.fst.withAssertPurity pass.phase.toPurity fun h => pass.run (h ▸ state.snd)
    state := ⟨_, decls⟩
    if check || pass.shouldAlwaysRunCheck then
      withPhase pass.phaseOut do
        for decl in state.snd do decl.check
  return state.fst.withAssertPurity .pure fun h => h ▸ state.snd

end LeanToReussir
