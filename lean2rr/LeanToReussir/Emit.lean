import Lean
import LeanToReussir.Lower
import LeanToReussir.MonoRetype

/-!
# Program assembly

Lowers all mono declarations and assembles the `.rr` program: the runtime
prelude, generated types (including `Box`), functions, and the entry point
(translation plan §5.11). The entry point calls the translated `main` with
the argument list (if it takes one) and the world `()`, then reproduces
native Lean's process behaviour: exit with the returned code, or report an
uncaught exception and exit with 1.
-/

namespace LeanToReussir
open Lean Compiler LCNF

/-- Roots besides `main` that the entry point needs. -/
def entryRoots : Array Name := #[``IO.Error.toString]

/-- Whether a module belongs to the Lean toolchain (its constants are
evaluated lazily; see translation plan §5.12). -/
def isToolchainModule (m : Name) : Bool :=
  m.getRoot ∈ [`Init, `Std, `Lean, `Lake]

/-- What a program does at startup, before `main`, like Lean's module
initializers: for each module in import order, for each declaration in
order, run an `initialize` action, or run the init function of an
`initialize c : T ← act` constant and store its result, or evaluate a
constant (native Lean evaluates every constant of a module, used or not,
instances included: their fields may compute or trace). -/
inductive StartupItem where
  | caf (decl : Name)
  | ioUnit (fn : Name)
  | init (decl fn : Name)
  deriving Inhabited

def StartupItem.root : StartupItem → Name
  | .caf d => d
  | .ioUnit f => f
  | .init _ f => f

/-- Position of a declaration for ordering: module index, then source
position (line and column, so declarations on one line keep their order). -/
def declOrder (n : Name) : CoreM (Nat × Nat) := do
  let idx := ((← getEnv).getModuleIdxFor? n).map (·.toNat) |>.getD 0
  -- An auxiliary declaration (`main.unsafe_1`, `f.match_1`, …) has no
  -- range of its own; Lean adds it while elaborating its parent, just
  -- before the parent.
  let rec find (m : Name) (aux : Bool) (fuel : Nat) : CoreM Nat := do
    match fuel with
    | 0 => return 0
    | fuel + 1 =>
      match ← findDeclarationRanges? m with
      | some r => return 2 * (r.range.pos.line * 100000 + r.range.pos.column) + (if aux then 0 else 1)
      | none => if m.isAnonymous then return 0 else find m.getPrefix true fuel
  -- A specialization `f._at_.g.spec_N` is compiled with `g`, before it.
  let n' := (atParent? n).getD n
  return (idx, ← find n' (n' != n) 16)
where
  /-- The declaration after the last `_at_` component, if any. -/
  atParent? (n : Name) : Option Name := Id.run do
    let cs := n.components
    let some i := (List.range cs.length).reverse.find? (cs[·]! == `_at_) | return none
    let rest := cs.drop (i + 1)
    if rest.isEmpty then return none
    return some (rest.foldl (fun acc c => acc ++ c) .anonymous)

/-- The startup items of the program's own (non-toolchain) modules, in
order. Constants are the module's compiled zero-parameter declarations
(as native Lean's module initializer), so compiler-generated ones such as
specializations with every parameter fixed are included. -/
def startupItems : CoreM (Array StartupItem) := do
  let env ← getEnv
  let mut out : Array (StartupItem × Nat × Nat) := #[]
  for (n, _) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let some modName := env.header.moduleNames[idx.toNat]? | continue
    if isToolchainModule modName then continue
    let item? :=
      if isIOUnitInitFn env n then some (StartupItem.ioUnit n)
      else if let some f := getInitFnNameFor? env n then some (.init n f)
      else none
    let some item := item? | continue
    let (m, pos) ← declOrder n
    out := out.push (item, m, pos)
  for h : idx in [:env.header.moduleNames.size] do
    if isToolchainModule env.header.moduleNames[idx] then continue
    for d in baseExt.getModuleEntries env idx (level := .private) do
      let n := d.name
      unless d.value matches .code _ && d.params.isEmpty do continue
      if isIOUnitInitFn env n || (getInitFnNameFor? env n).isSome then continue
      let (m, pos) ← declOrder n
      out := out.push (.caf n, m, pos)
  let sorted := out.qsort fun (_, m1, p1) (_, m2, p2) => m1 < m2 || (m1 == m2 && p1 < p2)
  return sorted.map (·.1)

/-- A startup step with instance names (see `StartupItem`). -/
inductive StartupStep where
  | caf (inst : Name)
  | ioUnit (inst : Name)
  | init (decl inst : Name)
  deriving Inhabited

/-- The IO result type of an instance and its `ok`/`error` variants. -/
def ioResultOf (inst : Name) : LowerM (String × String × String × Option RR.Ty) := do
  let some d := (← read).decls.find? inst | throwError "lean2rr: no declaration {inst}"
  let (_, r) := splitFnType d.type d.params.size
  let .named outTy ← lowerType r | throwError "lean2rr: {inst} does not return an IO result"
  let some info := (← get).typeInfos[outTy]? | throwError "lean2rr: {inst} does not return EST.Out"
  let okV := (info.ctors.find? ``EST.Out.ok).map (·.variant) |>.getD "c_ok"
  let errV := (info.ctors.find? ``EST.Out.error).map (·.variant) |>.getD "c_error"
  let okField := (info.ctors.find? ``EST.Out.ok).bind (·.fields[0]?) |>.join |>.map (·.2)
  return (outTy, okV, errV, okField)

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
  let tags := (← get).taskTags
  let mut drain := ""
  if !tags.isEmpty then
    let mut chain := "let none : u64 = 0;\n    none"
    for h : i in [:tags.size] do
      let j := tags.size - 1 - i
      let z := tags[j]!
      let get ← lazyGetFn z
      let (_, t) ← lazyInfo z
      chain := s!"if tag == {j} \{\n    let c : LCell<{z}> = l2r_task_take<{z}>();\n    let v : {t.render} = {get}(c);\n    l2r_run_pending_tasks()\n    } else \{\n    {chain}\n    }"
    pre := pre ++ s!"fn l2r_run_pending_tasks() -> u64 \{\n    let tag : u64 = l2r_task_next_tag();\n    {chain}\n}\n\n"
    drain := "let sd : u64 = l2r_task_shutdown();\nlet pt : u64 = l2r_run_pending_tasks();\n"
  let mainCode := s!"let tm : u64 = l2r_task_manager_start();\nlet r = {fnName mainInst}({argExpr}L2RUnit::u\{});\n{drain}match r \{\n{outTy}::{okV}(v) => \{ {exitCode} },\n{outTy}::{errV}(e) => \{ {uncaught "e"} }\n}"
  -- The startup chain ends by clearing `IO.initializing`; an error stops
  -- the program before main (`l2r_uncaught_exception` exits).
  let mut code := "l2r_init_done()"
  -- Build the startup chain from the last step outwards.
  for h : i in [:startup.size] do
    let j := startup.size - 1 - i
    match startup[j]! with
    | .caf inst => code := s!"let caf{j} = {fnName inst}();\n" ++ code
    | .ioUnit inst =>
      let (t, ok, err, _) ← ioResultOf inst
      code := s!"match {fnName inst}(L2RUnit::u\{}) \{\n{t}::{ok}(v{j}) => \{\n{code}\n},\n{t}::{err}(e{j}) => \{ {uncaught s!"e{j}"} }\n}"
    | .init decl inst =>
      let (t, ok, err, field) ← ioResultOf inst
      let some slot := (← get).initSlots.find? decl | throwError "lean2rr: no slot for {decl}"
      let vt := field.getD RR.Ty.unit
      let (st, boxed) ← arrayElemTy vt
      let stored := if boxed then match st with | .named bn => s!"{bn}\{v{j}}" | _ => s!"v{j}" else s!"v{j}"
      code := s!"match {fnName inst}(L2RUnit::u\{}) \{\n{t}::{ok}(v{j}) => \{\nlet s{j} : {st.render} = l2r_once_set<{st.render}>({slot}, {stored});\n{code}\n},\n{t}::{err}(e{j}) => \{ {uncaught s!"e{j}"} }\n}"
  let body := s!"fn l2r_init_body() \{\nlet si : u64 = l2r_set_initializing(true);\n{code}\n}\n\n" ++
    s!"fn l2r_main_body() \{\n{mainCode}\n}\n"
  -- Like Lean's runtime: the module initializers run on the process's main
  -- thread (8 MiB stack) with `IO.initializing` true; then `main` runs on a
  -- thread with a big stack (1 GiB, `LEAN_STACK_SIZE_KB`,
  -- `LEAN_MAIN_USE_THREAD`). A stack overflow is reported as Lean does.
  -- `leanrt::rt::run_main2` implements all of this.
  let entry := "extern \"C\" trampoline \"l2r_init_body\" = l2r_init_body;\n" ++
    "extern \"C\" trampoline \"l2r_main_body\" = l2r_main_body;\n\n" ++
    "#[ffi(import)]\nfn l2r_init_done() -> unit [{ leanrt::rt::set_initializing(false) }];\n\n" ++
    "#[ffi(import)]\nfn l2r_run_main() [{ {\n" ++
    "    extern \"C\" { fn l2r_init_body(); fn l2r_main_body(); }\n" ++
    "    leanrt::rt::run_main2(|| unsafe { l2r_init_body() }, || unsafe { l2r_main_body() })\n} }];\n\n" ++
    "#[main]\npub fn lean_main_entry() { l2r_run_main() }\n"
  return .raw (pre ++ body ++ "\n" ++ entry)

/-- The externs a program calls: Lean name, C symbol, mono signature, and
type arguments for extern instances (development aid for the runtime). -/
def externReport (decls : Array (Decl .pure)) (keys : NameMap InstKey) : CoreM String := do
  let byName := decls.foldl (fun m d => m.insert d.name d) ({} : NameMap (Decl .pure))
  let mut seen : NameSet := {}
  let mut lines := #[]
  for d in decls do
    let .code c := d.value | continue
    for f in codeConsts c #[] do
      if seen.contains f then continue
      seen := seen.insert f
      let (orig, targs, sig) ← match byName.find? f with
        | some e =>
          match e.value with
          | .extern _ =>
            let k := keys.find? f
            pure (some ((k.map (·.decl)).getD f), (k.map (·.typeArgs)).getD #[], e.type)
          | _ => pure (none, #[], default)
        | none =>
          if (← getEnv).isConstructor f then pure (none, #[], default)
          else match ← getMonoDecl? f with
            | some e => pure (some f, #[], e.type)
            | none => pure (none, #[], default)
      if let some o := orig then
        let sym := (getExternNameFor (← getEnv) `c o).getD "?"
        let targsStr := if targs.isEmpty then "" else s!" @[{", ".intercalate (targs.toList.map toString)}]"
        lines := lines.push s!"{o}{targsStr}  [{sym}]  : {sig}"
  return "\n".intercalate (lines.qsort (· < ·)).toList ++ "\n"

/-- The generic functions of the prelude that are plain Reussir code over
values: not FFI imports, and no type application in their signature (a
parameter `RVec<T>` makes `T` an array storage type, as for
`lean_array_push<T>`). lean2rr instantiates them at the value types of the
extern's type arguments (see `lowerExternCall`). Name ↦ number of type
parameters. -/
def valueGenericPreludeFns (prelude : String) : Std.HashMap String Nat := Id.run do
  let mut out : Std.HashMap String Nat := {}
  let mut prev := ""
  for line in prelude.splitOn "\n" do
    if line.startsWith "fn " && prev != "#[ffi(import)]" then
      let rest := (line.drop 3).toString
      let name := (rest.takeWhile fun c => c.isAlphanum || c == '_').toString
      let after := (rest.drop name.length).toString
      if after.startsWith "<" then
        let gens := ((after.drop 1).takeWhile (· != '>')).toString
        let sig := ((after.drop (gens.length + 2)).takeWhile (· != '{')).toString
        unless sig.contains '<' || sig.contains '[' do
          out := out.insert name (gens.splitOn ",").length
    unless line.all Char.isWhitespace do prev := line
  return out

/-- For the prelude functions of `valueGenericPreludeFns`: which parameters
are Reussir closures (a function value passed there is converted). -/
def valueGenericClosureParams (prelude : String) : Std.HashMap String (Array Bool) := Id.run do
  let mut out : Std.HashMap String (Array Bool) := {}
  for line in prelude.splitOn "\n" do
    if line.startsWith "fn " then
      let rest := (line.drop 3).toString
      let name := (rest.takeWhile fun c => c.isAlphanum || c == '_').toString
      let params := ((rest.dropWhile (· != '(')).drop 1 |>.takeWhile (· != ')')).toString
      let ps := if params.trim.isEmpty then [] else params.splitOn ","
      out := out.insert name (ps.map (·.contains '-')).toArray
  return out

/-- Lower a whole program. -/
def lowerProgram (prelude : String) (mainInst errStr : Name) (startup : Array StartupStep) (decls : Array (Decl .pure))
    (keys : NameMap InstKey) : CoreM String := do
  let table ← programRelevance decls
  let roots := #[mainInst, errStr] ++ startup.map fun
    | .caf i | .ioUnit i | .init _ i => i
  let (decls, keys) ← retypeMono table decls keys roots
  -- Function names the prelude defines (`fn NAME`).
  let preludeFns := (prelude.splitOn "fn ").foldl (init := ({} : Std.HashSet String)) fun acc chunk =>
    let name := chunk.takeWhile fun c => c.isAlphanum || c == '_'
    if name.isEmpty then acc else acc.insert name.toString
  -- Result types from the prelude's one-line signatures (`fn f(…) -> T …`).
  let preludeRets := prelude.splitOn "\n" |>.foldl (init := ({} : Std.HashMap String RR.Ty)) fun acc line =>
    let line := line.trimLeft
    let line := if line.startsWith "pub fn " then (line.drop 4).toString else line
    if !line.startsWith "fn " then acc else
    let name := ((line.drop 3).takeWhile fun c => c.isAlphanum || c == '_').toString
    match line.splitOn ") -> " with
    | _ :: rest@(_ :: _) =>
      let r := rest.getLast!
      let r := ((r.splitOn " [{").head!.splitOn " {").head!.trim
      match RR.parseTy r with
      | some t => acc.insert name t
      | none => acc
    | _ => acc
  -- Parameter types of the non-generic prelude functions (`fn f(a : T, …)`).
  let preludeParams := prelude.splitOn "\n" |>.foldl (init := ({} : Std.HashMap String (Array RR.Ty))) fun acc line =>
    let line := line.trimLeft
    let line := if line.startsWith "pub fn " then (line.drop 4).toString else line
    if !line.startsWith "fn " then acc else
    let rest := (line.drop 3).toString
    let name := (rest.takeWhile fun c => c.isAlphanum || c == '_').toString
    let rest := (rest.drop name.length).toString
    if !rest.startsWith "(" then acc else
    let inner := ((rest.drop 1).takeWhile (· != ')')).toString
    let parts := if inner.trim.isEmpty then [] else inner.splitOn ","
    match parts.mapM (fun p => match p.splitOn ":" with | [_, t] => RR.parseTy t | _ => none) with
    | some tys => acc.insert name tys.toArray
    | none => acc
  -- The `IO.Error` builders' instances (monomorphic, so keyed by declaration).
  let byDecl : NameMap Name := keys.foldl (init := {}) fun m inst k =>
    if k.typeArgs.isEmpty && k.dicts.isEmpty then m.insert k.decl inst else m
  let exports ← (exportMap.run' {config := {}} : CoreM _)
  let ioErrorBuilders := ioErrorBuilderSyms.map fun sym => (exports.get? sym).bind byDecl.find?
  let valueGenericFns := valueGenericPreludeFns prelude
  let valueGenericCls := valueGenericClosureParams prelude
  let ctx : LowerCtx := { table, decls := decls.foldl (fun m d => m.insert d.name d) {}, keys, preludeFns,
                          preludeRets, preludeParams, ioErrorBuilders, valueGenericFns, valueGenericCls }
  let act : LowerM (Array RR.Item) := do
    -- `Box` always exists (with at least the unit variant, `box(0)`): types
    -- may mention it even when nothing is ever boxed.
    let _ ← boxVariant .unit
    -- Once-cells of `initialize` constants (read by `calleeOf`).
    for st in startup do
      if let .init decl _ := st then
        modify fun s => { s with initSlots := s.initSlots.insert decl s.cafSlots, cafSlots := s.cafSlots + 1 }
    for d in decls do lowerDecl d
    let entry ← lowerEntry mainInst errStr startup
    modify fun s => { s with fns := s.fns.push entry }
    -- Converters and application functions can need each other.
    repeat
      finishUnboxFns
      unless ← finishFnValues do break
    return ← fnTypeItems
  let (fnItems, st) ← (act.run ctx).run {}
  let mut out := prelude ++ "\n// ---- generated types ----\n\n"
  for it in st.typeItems do out := out ++ it.render ++ "\n"
  for it in fnItems do out := out ++ it.render ++ "\n"
  out := out ++ (RR.Item.enum boxName false (st.boxVariants.map fun (t, v) => (v, #[t]))).render ++ "\n"
  out := out ++ "// ---- generated functions ----\n\n"
  for f in st.fns do out := out ++ f.render ++ "\n"
  unless st.strLits.isEmpty do out := out ++ strLitTable st.strLits
  return out

end LeanToReussir
