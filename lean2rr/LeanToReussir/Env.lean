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

/-- Load the imported state of every persistent environment extension, like
`importModules (loadExts := true)`, but without running the imported
modules' `[init]` declarations: with `loadExts`, importing runs the
program's own `initialize` actions (through the interpreter) inside
lean2rr. Without any extension state, queries such as `isClass`, which
Lean's own compiler passes rely on, would silently answer `false`. -/
unsafe def loadExtensionStates (env : Environment) : IO Environment := do
  let mut env := env
  for extDescr in ← persistentEnvExtensionsRef.get do
    let s := extDescr.toEnvExtension.getState (asyncMode := .sync) env
    let newState ← extDescr.addImportedFn s.importedEntries { env := env, opts := {} }
    env := extDescr.toEnvExtension.setState (asyncMode := .sync) env { s with state := newState }
  return env

/-- lean2rr's shim library (`L2RShim`, built with lean2rr): Lean
implementations of `Std.Internal.UV`'s externs, exported under their C
symbols, so that the program's calls of those externs compile them (see
`Mono.redirectTarget`). Imported with the program when it is on the search
path (`scripts/l2r.py` adds lean2rr's build directory to `LEAN_PATH`). -/
def shimModules : IO (Array Name) := do
  match ← (← searchPathRef.get).findWithExt "olean" `L2RShim with
  | some _ => return #[`L2RShim]
  | none => return #[]

/-- Import `modules` and their transitive closure at `private` level. Only
this level exposes every module's complete base-LCNF bodies; the default
`exported` level replaces non-public bodies with opaque stubs.

lean2rr takes modules named `Init.*`, `Std.*`, `Lean.*` or `Lake.*` for Lean's
library (`isToolchainModule`: their constants are evaluated lazily, their
`initialize` actions run by the runtime, their `unsafe` code trusted), so a
program module named like one that is not the toolchain's own is an error
here rather than a silently different program. -/
def loadEnvironment (modules : Array Name) : IO Environment := do
  let sysroot ← findSysroot
  initSearchPath sysroot
  let env ← importModules ((modules ++ (← shimModules)).map ({ module := · })) {} (level := .private)
  let libDir ← IO.FS.realPath (← getLibDir sysroot)
  for m in env.header.moduleNames do
    unless m.getRoot ∈ [`Init, `Std, `Lean, `Lake] do continue
    let olean ← IO.FS.realPath (← findOLean m)
    unless olean.toString.startsWith (libDir.toString ++ System.FilePath.pathSeparator.toString) do
      throw <| IO.userError s!"module {m} ({olean}) is named like a module of Lean's library but is not \
        the toolchain's ({libDir}): lean2rr treats Init.*, Std.*, Lean.* and Lake.* modules as \
        Lean's library, so rename it"
  unsafe loadExtensionStates env

/-- Run a `CoreM` action against `env` without a heartbeat limit and,
in effect, without a recursion limit. -/
def runCoreM (env : Environment) (x : CoreM α) : IO α := do
  -- The program's own `maxRecDepth` is not in the `.olean`, and Lean's
  -- passes recurse once per nested `let` (a large literal), so any fixed
  -- limit rejects some program that Lean compiled; instances can also be
  -- deeper than anything Lean compiled. Only the stack bounds the depth
  -- (the driver gives lean2rr a 1 GiB stack). The limit is also reset from
  -- the options by `withOptions`.
  let depth := 100000000
  let ctx : Core.Context := { fileName := "<lean2rr>", fileMap := default, maxHeartbeats := 0,
                              maxRecDepth := depth, options := maxRecDepth.set {} depth }
  let (a, _) ← x.toIO ctx { env }
  return a

end LeanToReussir
