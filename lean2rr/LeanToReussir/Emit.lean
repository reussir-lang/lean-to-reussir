import Lean
import LeanToReussir.Lower

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

/-- The entry point. `mainInst`/`errStr` are instance names. -/
def lowerEntry (mainInst errStr : Name) : LowerM RR.Item := do
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
  let body := s!"#[main]\npub fn lean_main_entry() \{\n    let r = {fnName mainInst}({argExpr}L2RUnit::u\{});\n    match r \{\n        {outTy}::{okV}(v) => \{ {exitCode} },\n        {outTy}::{errV}(e) => \{ l2r_uncaught_exception({fnName errStr}(e)) }\n    }\n}\n"
  return .raw (pre ++ body)

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
def lowerProgram (prelude : String) (mainInst errStr : Name) (decls : Array (Decl .pure))
    (keys : NameMap InstKey) : CoreM String := do
  let table ← programRelevance decls
  let ctx : LowerCtx := { table, decls := decls.foldl (fun m d => m.insert d.name d) {}, keys }
  let act : LowerM Unit := do
    for d in decls do lowerDecl d
    let entry ← lowerEntry mainInst errStr
    modify fun s => { s with fns := s.fns.push entry }
  let ((), st) ← (act.run ctx).run {}
  let mut out := prelude ++ "\n// ---- generated types ----\n\n"
  for it in st.typeItems do out := out ++ it.render ++ "\n"
  unless st.boxVariants.isEmpty do
    out := out ++ (RR.Item.enum boxName false (st.boxVariants.map fun (t, v) => (v, #[t]))).render ++ "\n"
  out := out ++ "// ---- generated functions ----\n\n"
  for f in st.fns do out := out ++ f.render ++ "\n"
  return out

end LeanToReussir
