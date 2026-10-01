import Lean
import LeanToReussir.Emit.Entry
import LeanToReussir.PassConfig
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
def lowerProgram (cfg : PassConfig) (prelude : String) (mainInst errStr : Name) (startup : Array StartupStep)
    (decls : Array (Decl .pure)) (keys : NameMap InstKey) : CoreM String := do
  let table ← programRelevance decls
  let roots := #[mainInst, errStr] ++ startup.map fun
    | .caf i | .ioUnit i | .init _ i => i
  let (decls, keys) ← retypeMono cfg.stage2 table decls keys roots
  -- The registry's passes over mono LCNF (`Opt/FloatLits`: float literals
  -- become bit patterns).
  let decls := cfg.monoPasses.foldl (fun ds p => p keys ds) decls
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
  -- Constants not cached (`Opt/ClosedChains`: closed terms used once, by
  -- another constant).
  let uncachedConsts := cfg.uncachedConsts decls roots
  let ctx : LowerCtx := { table, decls := decls.foldl (fun m d => m.insert d.name d) {}, keys, preludeFns,
                          preludeRets, preludeParams, ioErrorBuilders, valueGenericFns, valueGenericCls,
                          uncachedConsts }
  let act : LowerM (Array RR.Item) := do
    -- `Box` always exists (with at least the unit variant, `box(0)`): types
    -- may mention it even when nothing is ever boxed.
    let _ ← boxVariant .unit
    -- Once-cells of `initialize` constants (read by `calleeOf`).
    for st in startup do
      if let .init decl _ := st then
        modify fun s => { s with initSlots := s.initSlots.insert decl s.cafSlots, cafSlots := s.cafSlots + 1 }
    for d in decls do lowerDecl cfg.lower d
    let entry ← lowerEntry mainInst errStr startup
    modify fun s => { s with fns := s.fns.push entry }
    -- Converters and application functions can need each other.
    repeat
      finishUnboxFns
      unless ← finishFnValues do break
    -- Only now is every use of the standard streams lowered (function
    -- values' targets included), so the diagnostics writer and the stream
    -- contexts know whether the program has stream cells.
    let put ← stderrPutFn
    modify fun s => { s with fns := s.fns.push put }
    let ctxFns ← stdContextFns
    modify fun s => { s with fns := s.fns ++ ctxFns }
    repeat
      finishUnboxFns
      unless ← finishFnValues do break
    -- Every task type is known now: the functions running queued tasks.
    let disp ← taskDispatchFns
    modify fun s => { s with fns := s.fns ++ disp }
    repeat
      finishUnboxFns
      unless ← finishFnValues do break
    return ← fnTypeItems
  let (fnItems, st) ← (act.run ctx).run {}
  let boxItem := RR.Item.enum boxName false (st.boxVariants.map fun (t, v) => (v, #[t]))
  -- The registry's passes over the generated functions (`Opt/SinkProj`:
  -- projections sunk into the branches that use them; `Opt/Outline`: deep
  -- and long tail paths cut into chains of functions, for rrc).
  let rrProg : RRProgram := { prelude, preludeFns, types := st.typeItems ++ fnItems |>.push boxItem }
  let fns := cfg.rrPasses.foldl (fun fns p => p rrProg fns) st.fns
  let mut out := prelude ++ "\n// ---- generated types ----\n\n"
  for it in st.typeItems do out := out ++ it.render ++ "\n"
  for it in fnItems do out := out ++ it.render ++ "\n"
  out := out ++ boxItem.render ++ "\n"
  out := out ++ "// ---- generated functions ----\n\n"
  for f in fns do out := out ++ f.render ++ "\n"
  unless st.strLits.isEmpty do out := out ++ strLitTable st.strLits
  return out

end LeanToReussir
