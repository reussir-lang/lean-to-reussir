import Lean

/-!
# Loading a compiled program

lean2rr reads a program the way the Lean compiler left it: base-phase LCNF
persisted in each module's `.olean` (`Lean.Compiler.LCNF.baseExt`). The
program must have been compiled by the same Lean toolchain lean2rr is built
with (v4.33.0). Modules are located through `LEAN_PATH`, so a Lake project is
translated with `lake env lean2rr <Module>`.
-/

namespace LeanToReussir
open Lean

/-- Import `modules` and their transitive closure at `private` level. Only
this level exposes every module's complete base-LCNF bodies; the default
`exported` level replaces non-public bodies with opaque stubs.

Environment extensions are loaded (`loadExts`): without them every
extension keeps its initial state, and queries such as `isClass` — which
Lean's own compiler passes rely on — silently answer `false`. -/
def loadEnvironment (modules : Array Name) : IO Environment := do
  initSearchPath (← findSysroot)
  unsafe enableInitializersExecution
  importModules (modules.map ({ module := · })) {} (level := .private) (loadExts := true)

/-- Run a `CoreM` action against `env` without a heartbeat limit. -/
def runCoreM (env : Environment) (x : CoreM α) : IO α := do
  let ctx : Core.Context := { fileName := "<lean2rr>", fileMap := default, maxHeartbeats := 0 }
  let (a, _) ← x.toIO ctx { env }
  return a

end LeanToReussir
