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

/-- The roots Stage 1 starts from: `main`, the entry point's own roots
(`entryRoots`), then the startup items (`startupItems`): those
`lean_initialize()` runs first (`leanInit`), then the others. -/
def programRoots (main : Name) (leanInit items : Array StartupItem) : Array Name :=
  #[main] ++ entryRoots ++ (leanInit ++ items).map (·.root)

/-- The startup steps, with instance names: in a program that uses the
`Lean` package, what `lean_initialize()` runs first (`leanInit`: the
initializers of `Init` and `Std`), then the `Lean` package's `initialize`
constants that the program uses (in module order); then the startup items
in order (`items`: the program's, and the initializers of `Init` and `Std`
at their modules' places). `rootInsts` are the instances of
`programRoots main leanInit items`, `st` Stage 1's state. -/
def startupSteps (leanInit items : Array StartupItem) (rootInsts : Array Name) (st : MonoState) :
    CoreM (Array StartupStep) := do
  let all := leanInit ++ items
  let inits := all.filterMap fun | .init d _ => some d | _ => none
  let mut tool := #[]
  for (d, f) in st.initConsts do
    unless inits.contains d do
      let some inst := st.names[({ decl := f, typeArgs := #[] } : InstKey)]? | continue
      tool := tool.push (d, inst, ← declOrder d)
  let toolSorted := tool.qsort fun (_, _, k1) (_, _, k2) => lexLtNat k1 k2
  let base := 1 + entryRoots.size
  let steps := all.zipIdx.map fun (it, i) =>
    let inst := rootInsts[base + i]!
    match it with
    | .caf _ => StartupStep.caf inst
    | .ioUnit _ => .ioUnit inst
    | .init d _ => .init d inst
  return steps.extract 0 leanInit.size ++ toolSorted.map (fun (d, inst, _) => StartupStep.init d inst) ++
    steps.extract leanInit.size steps.size

/-- The entry point. `mainInst`/`errStr` are instance names; `startup` is
run first, in order (see `StartupItem`); an error in an initializer is
reported like an uncaught exception of `main`. -/
def lowerEntry (mainInst errStr : Name) (startup : Array StartupStep) : LowerM RR.Item := do
  let some mainDecl := (← read).decls.find? mainInst | throwError "lean2rr: no main"
  let (ps, _) := splitFnType mainDecl.type mainDecl.params.size
  let (outTy, okV, errV, okField, payTy) ← ioResultOf mainInst
  -- The exit code: a `UInt32` result, held boxed in the result's field
  -- (`l2r_main_code` unboxes it).
  let mut exitCode := "l2r_exit(0)"
  if payTy == .named "u32" then
    let ft := okField.getD payTy
    let code ← coerce (.var "v") ft payTy
    modify fun s => { s with fns := s.fns.push (.fn "l2r_main_code" #[("v", ft)] payTy (.ofExpr code)) }
    exitCode := "l2r_exit(l2r_main_code(v))"
  let takesArgs := ps.size == 2
  let mut argExpr := ""
  if takesArgs then
    -- `l2r_mk_args(i, acc)`: the arguments `i - 1` down to 0 consed onto
    -- `acc`, each string boxed into the list's head field.
    let listTy ← lowerType ps[0]!
    let .named lt := listTy | throwError "lean2rr: bad main argument type"
    let some linfo := (← get).typeInfos[lt]? | throwError "lean2rr: bad main argument type"
    let nilV := (linfo.ctors.find? ``List.nil).map (·.variant) |>.getD "c_nil"
    let headTy := ((← ctorFieldTys listTy ``List.cons)[0]?).getD (.named "LStr")
    let hd ← coerce (.call "l2r_argv" #[] #[.atom "i - 1"]) (.named "LStr") headTy
    let cons ← ctorValue listTy ``List.cons #[hd, .var "acc"]
    let u64 := RR.Ty.named "u64"
    let body : RR.Block := .ofExpr (.ite (.atom "i == 0") (.ofExpr (.var "acc"))
      (.ofExpr (.call "l2r_mk_args" #[] #[.atom "i - 1", cons])))
    modify fun s => { s with fns := s.fns.push (.fn "l2r_mk_args" #[("i", u64), ("acc", listTy)] listTy body) }
    argExpr := s!"l2r_mk_args(l2r_argc(), {lt}::{nilV}\{}), "
  let errFn ← errStringFn errStr outTy
  let uncaught (e : String) := s!"l2r_uncaught_exception({errFn}({e}))"
  -- IO tasks are deferred once `main` starts (before, during
  -- initialization, Lean has no task manager and runs them at once). After
  -- `main` returns, whatever its result, the tasks still pending run, as
  -- `lean_finalize_task_manager` waits for them before the exception is
  -- reported or the process exits; they see Lean's shutdown flag (§5.14).
  -- (`l2r_run_pending_tasks` is generated at the end, `taskDispatchFns`.)
  let drain := "let sd : u64 = l2r_task_shutdown();\nlet pt : u64 = l2r_run_pending_tasks();\n"
  -- `main` gets standard streams of its own (a fresh stream context,
  -- `l2r_std_enter`) only when it runs on a thread of its own: with
  -- `LEAN_MAIN_USE_THREAD=0` it runs on the initializers' thread and keeps
  -- the streams they left (§5.11).
  let mainCode := s!"let tm : u64 = l2r_task_manager_start();\nlet mt : u64 = l2r_main_on_thread();\nlet se : u64 = l2r_std_enter_if(mt);\nlet r = {fnName mainInst}({argExpr}L2RUnit::u\{});\nlet sl : u64 = l2r_std_leave_if(mt);\n{drain}match r \{\n{outTy}::{okV}(v) => \{ {exitCode} },\n{outTy}::{errV}(e) => \{ {uncaught "e"} }\n}"
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
    "#[ffi(import)]\nfn l2r_main_on_thread() -> u64 [{ leanrt::rt::main_on_thread() as u64 }];\n\n" ++
    "#[ffi(import)]\nfn l2r_run_main() [{ {\n" ++
    "    extern \"C\" { fn l2r_init_body(); fn l2r_main_body(); }\n" ++
    "    leanrt::rt::run_main2(|| unsafe { l2r_init_body() }, || unsafe { l2r_main_body() })\n} }];\n\n" ++
    "#[main]\npub fn lean_main_entry() { l2r_run_main() }\n"
  return .raw (body ++ "\n" ++ entry)

end LeanToReussir
