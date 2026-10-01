import Lean
import LeanToReussir.Emit.Startup

/-!
# Program entry

The entry point (translation plan §5.11): the startup chain, then the
translated `main` with the argument list (if it takes one) and the world
`()`, then native Lean's process behaviour: run the pending tasks, exit with
the returned code, or report an uncaught exception and exit with 1.
-/

namespace LeanToReussir
open Lean Compiler LCNF

/-- Roots besides `main` that the entry point needs. -/
def entryRoots : Array Name := #[``IO.Error.toString]

/-- The entry point. `mainInst`/`errStr` are instance names; `startup` is
run first, in order (see `StartupItem`); an error in an initializer is
reported like an uncaught exception of `main`. -/
def lowerEntry (mainInst errStr : Name) (startup : Array StartupStep) : LowerM RR.Item := do
  let some mainDecl := (← read).decls.find? mainInst | throwError "lean2rr: no main"
  let (ps, _) := splitFnType mainDecl.type mainDecl.params.size
  let (outTy, okV, errV, okField) ← ioResultOf mainInst
  let exitCode := match okField with
    | some (.named "u32") => "l2r_exit(v)"
    | _ => "l2r_exit(0)"
  let takesArgs := ps.size == 2
  let mut pre := ""
  let mut argExpr := ""
  if takesArgs then
    let listTy ← lowerType ps[0]!
    let .named lt := listTy | throwError "lean2rr: bad main argument type"
    let some linfo := (← get).typeInfos[lt]? | throwError "lean2rr: bad main argument type"
    let nilV := (linfo.ctors.find? ``List.nil).map (·.variant) |>.getD "c_nil"
    let consV := (linfo.ctors.find? ``List.cons).map (·.variant) |>.getD "c_cons"
    pre := s!"fn l2r_mk_args(i : u64, acc : {lt}) -> {lt} \{\n    if i == 0 \{ acc } else \{ l2r_mk_args(i - 1, {lt}::{consV}\{l2r_argv(i - 1), acc}) }\n}\n\n"
    argExpr := s!"l2r_mk_args(l2r_argc(), {lt}::{nilV}\{}), "
  let uncaught (e : String) := s!"l2r_uncaught_exception({fnName errStr}({e}))"
  -- IO tasks are deferred once `main` starts (before, during
  -- initialization, Lean has no task manager and runs them at once). After
  -- `main` returns, whatever its result, the tasks still pending run, as
  -- `lean_finalize_task_manager` waits for them before the exception is
  -- reported or the process exits; they see Lean's shutdown flag (§5.14).
  -- (`l2r_run_pending_tasks` is generated at the end, `taskDispatchFns`.)
  let drain := "let sd : u64 = l2r_task_shutdown();\nlet pt : u64 = l2r_run_pending_tasks();\n"
  let mainCode := s!"let tm : u64 = l2r_task_manager_start();\nlet se : u64 = l2r_std_enter();\nlet r = {fnName mainInst}({argExpr}L2RUnit::u\{});\nlet sl : u64 = l2r_std_leave();\n{drain}match r \{\n{outTy}::{okV}(v) => \{ {exitCode} },\n{outTy}::{errV}(e) => \{ {uncaught "e"} }\n}"
  -- The startup chain (`startupChain`), then `main`.
  let body := (← startupChain errStr startup) ++
    s!"fn l2r_main_body() \{\n{mainCode}\n}\n"
  -- Like Lean's runtime: the module initializers run on the process's main
  -- thread (8 MiB stack) with `IO.initializing` true; then `main` runs on a
  -- thread with a big stack (1 GiB, `LEAN_STACK_SIZE_KB`,
  -- `LEAN_MAIN_USE_THREAD`). A stack overflow is reported as Lean does.
  -- `leanrt::rt::run_main2` implements all of this.
  -- The runtime writes its own diagnostics (index out of bounds, …) with
  -- `l2r_stderr_put` through this trampoline, called from Rust, so that
  -- Reussir sees no call cycle through the stream code.
  let entry := "extern \"C\" trampoline \"l2r_stderr_put_c\" = l2r_stderr_put;\n" ++
    "extern \"C\" trampoline \"l2r_init_body\" = l2r_init_body;\n" ++
    "extern \"C\" trampoline \"l2r_main_body\" = l2r_main_body;\n\n" ++
    "#[ffi(import)]\nfn l2r_init_done() -> unit [{ leanrt::rt::set_initializing(false) }];\n\n" ++
    "#[ffi(import)]\nfn l2r_init_failed(msg : LStr) -> u64 [{ leanrt::uncaught_exception(&msg) }];\n\n" ++
    "#[ffi(import)]\nfn l2r_run_main() [{ {\n" ++
    "    extern \"C\" { fn l2r_init_body(); fn l2r_main_body(); }\n" ++
    "    leanrt::rt::run_main2(|| unsafe { l2r_init_body() }, || unsafe { l2r_main_body() })\n} }];\n\n" ++
    "#[main]\npub fn lean_main_entry() { l2r_run_main() }\n"
  return .raw (pre ++ body ++ "\n" ++ entry)

end LeanToReussir
