import LeanToReussir.CompileRecord

/-!
# Loading a compiled program

lean2rr reads a program the way the Lean compiler left it: base-phase LCNF
persisted in each module's `.olean` (`Lean.Compiler.LCNF.baseExt`). The
program must have been compiled by the same Lean toolchain lean2rr is built
with (v4.34.0, `lean2rr/lean-toolchain`). Modules are located through
`LEAN_PATH`, then in that toolchain's library and in lean2rr's shim, so a
Lake project is translated with `lake env lean2rr <Module>`.
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

/-- The system root of the Lean toolchain whose `lean` elaborates this
file: the toolchain lean2rr is built with. -/
elab "l2r_build_sysroot%" : term => return mkStrLit (← getBuildDir).toString

/-- The system root of the toolchain lean2rr is built with, whose `.olean`
files it reads (not the toolchain that `lean` or `LEAN_SYSROOT` names,
which can depend on the working directory's `lean-toolchain`); the one
`findSysroot` gives only if that toolchain has been removed. -/
def toolchainSysroot : IO System.FilePath := do
  let root : System.FilePath := ⟨l2r_build_sysroot%⟩
  if ← (← getLibDir root).isDir then return root
  findSysroot

/-- The directory of lean2rr's shim library (`L2RShim`, built with
lean2rr): Lean implementations of `Std.Internal.UV`'s externs, exported
under their C symbols, so that the program's calls of those externs compile
them (see `Mono.redirectTarget`). `L2R_SHIM_DIR` (`scripts/l2r.py` sets it),
else the library directory of lean2rr's own build (`lib/lean` next to
`bin/lean2rr`), and where it comes from. -/
def shimDir : IO (System.FilePath × String) := do
  if let some d ← IO.getEnv "L2R_SHIM_DIR" then return (d, s!"L2R_SHIM_DIR='{d}'")
  return (((← IO.appDir).parent.getD ".") / "lib" / "lean",
    "L2R_SHIM_DIR is unset: the lib/lean directory next to lean2rr's bin directory")

/-- Whether `a` and `b` are the same file: one path, another path to it (a
symbolic or a hard link), or a copy of it (the same contents). -/
def sameFile (a b : System.FilePath) : IO Bool := do
  unless (← a.pathExists) && (← b.pathExists) do return false
  if (← IO.FS.realPath a) == (← IO.FS.realPath b) then return true
  if (← a.metadata).byteSize != (← b.metadata).byteSize then return false
  return (← IO.FS.readBinFile a) == (← IO.FS.readBinFile b)

/-- How the module at `found` (an `.olean` path) differs from the module at
`expected`, if it does: `expected` is missing, or one of the files of the
module (`.olean`, and the `.olean.server` and `.olean.private` parts where
either module has them; lean2rr reads the private part) is not the same
file (`sameFile`). -/
def moduleDiff (found expected : System.FilePath) : IO (Option String) := do
  unless ← expected.pathExists do return some s!", which has no module of that name ({expected})"
  for ext in ["", "server", "private"] do
    let (a, b) := (found.addExtension ext, expected.addExtension ext)
    let (ea, eb) := (← a.pathExists, ← b.pathExists)
    if !ea && !eb then continue
    unless ea && eb && (← sameFile a b) do return some s!" but differs from it in {b}"
  return none

/-- Why a program module must not be named like a module of Lean's library
or of lean2rr's shim. -/
def reservedNames : String :=
  "lean2rr takes the modules named Init.*, Std.*, Lean.* and Lake.* for Lean's library and \
    L2RShim.* for its own shim, so a program module must not be named like them; rename it"

/-- The shim modules to import with the program, from the shim directory
`dir` (described by `src`), which must have them (otherwise a program that
calls a shimmed extern would fail only in rrc): `L2RShim`, the whole shim,
and `L2RShim.Core`, its part over `Init` only, which `L2RShim` imports
(`loadEnvironment` loads `L2RShim.Core` alone when `L2RShim` cannot be
loaded with the program). Each must also be the module of that name on the
search path (a program module named `L2RShim`, or a directory `L2RShim` of
program modules, earlier on the path would replace it). -/
def shimModules (dir : System.FilePath) (src : String) : IO (Name × Name) := do
  for m in [`L2RShim, `L2RShim.Core] do
    let shim := modToFilePath dir m "olean"
    unless ← shim.pathExists do
      throw <| IO.userError s!"lean2rr's shim library ({m}.olean) is not in {dir} ({src}): \
        set L2R_SHIM_DIR to the lib/lean directory of lean2rr's build, as scripts/l2r.py does"
    if let some found ← (← searchPathRef.get).findWithExt "olean" m then
      if (← moduleDiff found shim).isSome then
        throw <| IO.userError s!"{found.parent.getD "."} holds program modules named L2RShim or \
          L2RShim.*, like lean2rr's shim ({shim}): {reservedNames}"
  return (`L2RShim, `L2RShim.Core)

/-- Import `modules` and their transitive closure at `private` level. Only
this level exposes every module's complete base-LCNF bodies; the default
`exported` level replaces non-public bodies with opaque stubs.

lean2rr takes modules named `Init.*`, `Std.*`, `Lean.*` or `Lake.*` for Lean's
library, and `L2RShim.*` for its shim (`isToolchainModule`: their constants
are evaluated lazily, only their `initialize` declarations run at startup,
their `unsafe` code trusted), so a program module named like one is an error
here rather than a silently different program: each such module must be the
module of that name in the library of lean2rr's toolchain (or in the shim
directory), its files reached by any path (a link, a copy; `moduleDiff`).

A program that imports a module of the `Lean` package natively initializes
all of `Init` and `Std` before anything else (`lean_initialize`;
`Emit/Startup.lean`: `leanInitModules`): when its imports do not reach the
modules `Init` and `Std`, they are loaded too, each one that can be loaded
with the program (`Std`'s modules can clash with it, see below; that
changes nothing at startup, since Lean 4.34.0's `Std` has no
initializer).

The shim (`shimModules`) is loaded with the program. `L2RShim` imports
modules of `Std` that the program may not import, and a declaration of
theirs can have the name of one of the program's (`Std.Data.ByteSlice`'s
`ByteSlice`, which `Std.Internal.UV` imports): natively that is no clash,
since the program does not import them, but imported together they are an
error. Then lean2rr loads `L2RShim.Core` (the part over `Init` only) in its
place, and says so: the externs of the `Std` modules that `L2RShim`
implements are then missing (a program that calls one is rejected,
naming it). -/
def loadEnvironment (modules : Array Name) : IO Environment := do
  let sysroot ← toolchainSysroot
  let (shim, shimSrc) ← shimDir
  initSearchPath sysroot
  searchPathRef.modify (· ++ [shim])
  let (whole, core) ← shimModules shim shimSrc
  let imp (mods : Array Name) : IO Environment :=
    importModules (mods.map ({ module := · })) {} (level := .private)
  -- With `L2RShim`, else (its imports clash with the program) with
  -- `L2RShim.Core`; an error of the second import is the program's own.
  let (env0, shimMods) ← try pure ((← imp (modules.push whole)), #[whole]) catch e => do
    let env ← imp (modules.push core)
    IO.eprintln s!"lean2rr: note: lean2rr's shim {whole} is not loaded, only {core}: {e}; \
      the externs of Std that {whole} implements (Std.Internal.UV, Std.Net, Std.Time) are missing"
    pure (env, #[core])
  let mut env := env0
  let missing := #[`Init, `Std].filter (env.getModuleIdx? · |>.isNone)
  if env.header.moduleNames.any (`Lean).isPrefixOf && !missing.isEmpty then
    -- Each that can be loaded with the program (`Std`'s modules can clash
    -- with it, as the shim's can; neither has an initializer in Lean
    -- 4.34.0, so the startup is the same without it).
    let mut added := #[]
    for m in missing do
      try
        env ← imp (modules ++ added ++ #[m] ++ shimMods)
        added := added.push m
      catch e =>
        IO.eprintln s!"lean2rr: note: module {m}, which a program of the Lean package initializes \
          natively, is not loaded: {e}"
  let libDir ← getLibDir sysroot
  for m in env.header.moduleNames do
    unless isToolchainModule m do continue
    let (dir, what) := if m.getRoot == `L2RShim then (shim, "lean2rr's shim") else (libDir, "Lean's library")
    let found ← findOLean m
    if let some diff ← moduleDiff found (modToFilePath dir m "olean") then
      throw <| IO.userError s!"module {m} ({found}) is named like a module of {what}{diff}: {reservedNames}"
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
