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

/-- Constants (zero-parameter declarations with code) of user modules, in
source order. Native Lean evaluates all of them at startup, even unused ones,
so they are roots and are forced before `main`. Type-class instances are
skipped: building a dictionary has no observable effect. -/
def userConstants : CoreM (Array Name) := do
  let env ← getEnv
  let mut out : Array (Name × Nat × Nat) := #[]
  for (n, _) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let some modName := env.header.moduleNames[idx.toNat]? | continue
    if isToolchainModule modName then continue
    let some d ← getBaseDecl? n | continue
    let .code _ := d.value | continue
    unless d.params.isEmpty do continue
    if (← isClass? d.type).isSome then continue
    let pos := match ← findDeclarationRanges? n with
      | some r => r.range.pos.line
      | none => 0
    out := out.push (n, idx.toNat, pos)
  let sorted := out.qsort fun (_, m1, p1) (_, m2, p2) => m1 < m2 || (m1 == m2 && p1 < p2)
  return sorted.map (·.1)

/-- The entry point. `mainInst`/`errStr` are instance names; `eager` are the
instances of user constants, forced before `main` like native Lean does. -/
def lowerEntry (mainInst errStr : Name) (eager : Array Name) : LowerM RR.Item := do
  let some mainDecl := (← read).decls.find? mainInst | throwError "lean2rr: no main"
  let (ps, r) := splitFnType mainDecl.type mainDecl.params.size
  let resTy ← lowerType r
  let .named outTy := resTy | throwError "lean2rr: unexpected main result type {resTy.render}"
  let some info := (← get).typeInfos[outTy]? | throwError "lean2rr: main result is not EST.Out"
  let okV := (info.ctors.find? ``EST.Out.ok).map (·.variant) |>.getD "c_ok"
  let errV := (info.ctors.find? ``EST.Out.error).map (·.variant) |>.getD "c_error"
  let okField := (info.ctors.find? ``EST.Out.ok).bind (·.fields[0]?) |>.join
  let exitCode := match okField with
    | some (_, .named "u32") => "l2r_exit(v)"
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
  let mut forced := ""
  for h : i in [:eager.size] do
    forced := forced ++ s!"    let caf{i} = {fnName eager[i]}();\n"
  let body := s!"fn l2r_main_body() \{\n{forced}    let r = {fnName mainInst}({argExpr}L2RUnit::u\{});\n    match r \{\n        {outTy}::{okV}(v) => \{ {exitCode} },\n        {outTy}::{errV}(e) => \{ l2r_uncaught_exception({fnName errStr}(e)) }\n    }\n}\n"
  -- Like Lean's runtime, run the program on a thread with a 1 GiB stack
  -- (deep non-tail recursion is common in Lean programs).
  let entry := "extern \"C\" trampoline \"l2r_main_body\" = l2r_main_body;\n\n" ++
    "#[ffi(import)]\nfn l2r_run_main() [{ {\n" ++
    "    extern \"C\" { fn l2r_main_body(); }\n" ++
    "    ::std::thread::Builder::new().name(\"main\".into()).stack_size(1 << 30)\n" ++
    "        .spawn(|| unsafe { l2r_main_body() }).unwrap().join().unwrap()\n} }];\n\n" ++
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

/-- Lower a whole program. -/
def lowerProgram (prelude : String) (mainInst errStr : Name) (eager : Array Name) (decls : Array (Decl .pure))
    (keys : NameMap InstKey) : CoreM String := do
  let table ← programRelevance decls
  let decls ← retypeMono table decls
  -- Function names the prelude defines (`fn NAME`).
  let preludeFns := (prelude.splitOn "fn ").foldl (init := ({} : Std.HashSet String)) fun acc chunk =>
    let name := chunk.takeWhile fun c => c.isAlphanum || c == '_'
    if name.isEmpty then acc else acc.insert name.toString
  let ctx : LowerCtx := { table, decls := decls.foldl (fun m d => m.insert d.name d) {}, keys, preludeFns }
  let act : LowerM Unit := do
    for d in decls do lowerDecl d
    let entry ← lowerEntry mainInst errStr eager
    modify fun s => { s with fns := s.fns.push entry }
    finishUnboxFns
  let ((), st) ← (act.run ctx).run {}
  let mut out := prelude ++ "\n// ---- generated types ----\n\n"
  for it in st.typeItems do out := out ++ it.render ++ "\n"
  unless st.boxVariants.isEmpty do
    out := out ++ (RR.Item.enum boxName false (st.boxVariants.map fun (t, v) => (v, #[t]))).render ++ "\n"
  out := out ++ "// ---- generated functions ----\n\n"
  for f in st.fns do out := out ++ f.render ++ "\n"
  unless st.strLits.isEmpty do out := out ++ strLitTable st.strLits
  return out

end LeanToReussir
