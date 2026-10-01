import Lean
import LeanToReussir.Emit.Entry
import LeanToReussir.PassConfig
import LeanToReussir.Outline
import LeanToReussir.ArrayLits
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

/-- The closed terms of `decls` referenced exactly once, from a constant
(not from a function, and not a root of the entry point): they are
evaluated where they are used instead of cached in a once-cell (translation
plan §5.12). Lean's `extractClosed` turns an array literal into a chain of
closed terms, `_closed_k := push _closed_(k-1) e_k`, and caching every step
kept every intermediate array alive: memory quadratic in the literal's
length (10000 elements: 1036 MB instead of 7 MB). A chain step still runs
once, at the same point. -/
def chainConsts (decls : Array (Decl .pure)) (roots : Array Name) : NameSet := Id.run do
  let mut uses : NameMap Nat := {}
  let mut fromFunction : NameSet := {}
  for d in decls do
    let .code c := d.value | continue
    for n in codeConsts c #[] do
      uses := uses.insert n (uses.getD n 0 + 1)
      unless d.params.isEmpty do fromFunction := fromFunction.insert n
  let isClosed (n : Name) : Bool := match n with
    | .str _ s => s.startsWith "_closed"
    | _ => false
  return decls.foldl (init := ({} : NameSet)) fun acc d =>
    if d.params.isEmpty && isClosed d.name && uses.getD d.name 0 == 1 && !fromFunction.contains d.name
      && !roots.contains d.name then acc.insert d.name else acc

/-- `v` with its free variables renamed by `ren`. -/
def renameLetValue (ren : Std.HashMap FVarId FVarId) (v : LetValue .pure) : LetValue .pure :=
  let r (x : FVarId) : FVarId := ren.getD x x
  let ra (a : Arg .pure) : Arg .pure := match a with
    | .fvar x => .fvar (r x)
    | a => a
  match v with
  | .proj t i s _ => .proj t i (r s)
  | .const n us args _ => .const n us (args.map ra)
  | .fvar f args => .fvar (r f) (args.map ra)
  | v => v

/-- Whether code `c` is straight-line: `let`s, then `return`. -/
partial def straightLine : Code .pure → Bool
  | .let _ k => straightLine k
  | .return _ => true
  | _ => false

/-- If closed term `n` of `inline` can be spliced into its use (see
`spliceChainConsts`): the type of the value it returns, which its body
binds by its last `let`. -/
def spliceable (byName : NameMap (Decl .pure)) (inline : NameSet) (n : Name) : Option Expr := do
  guard (inline.contains n)
  let cd ← byName.find? n
  let .code body := cd.value | none
  let rec last : Code .pure → Option Expr
    | .let d (.return x) => if x == d.fvarId then some d.type else none
    | .let _ k => last k
    | _ => none
  last body

/-- The variables a `let` value reads. -/
def letValueFVars (v : LetValue .pure) : Array FVarId :=
  let args (as : Array (Arg .pure)) : Array FVarId := as.filterMap fun | .fvar x => some x | _ => none
  match v with
  | .proj _ _ s _ => #[s]
  | .const _ _ as _ => args as
  | .fvar f as => #[f] ++ args as
  | _ => #[]

/-- A suspended part of `spliceChains`: the rest of a body, its renaming,
and the binder that receives the value of the closed term being spliced. -/
structure SpliceFrame where
  code : Code .pure
  ren : Std.HashMap FVarId FVarId
  binder : FVarId

/-- The `let`s of straight-line code `c` and the variable it returns, with
the closed terms it reads that can be spliced (`spliceable`, with the type
of the binder that reads them) spliced in, recursively: their `let`s in
place of the read, the variable they return in place of the read's
variable; and the closed terms spliced. A literal `let` is placed right
before its first use (a chain step reads its element before the previous
step, so the elements would otherwise all come first, each live across the
whole literal). An explicit stack and one accumulator: a chain of `n`
closed terms costs time linear in `n`. -/
def spliceChains (byName : NameMap (Decl .pure)) (inline : NameSet) (c : Code .pure) :
    Array (LetDecl .pure) × FVarId × NameSet := Id.run do
  let mut acc : Array (LetDecl .pure) := #[]
  let mut spliced : NameSet := {}
  let mut pending : Std.HashMap FVarId (LetDecl .pure) := {}
  let mut stack : Array SpliceFrame := #[]
  let mut code := c
  let mut ren : Std.HashMap FVarId FVarId := {}
  repeat
    match code with
    | .let d k =>
      let d := { d with value := renameLetValue ren d.value }
      match d.value with
      | .lit _ =>
        pending := pending.insert d.fvarId d
        code := k
      | v =>
        if let .const n _ #[] _ := v then
          if (spliceable byName inline n) == some d.type then
            if let some { value := .code body, .. } := byName.find? n then
              spliced := spliced.insert n
              stack := stack.push { code := k, ren, binder := d.fvarId }
              code := body
              ren := {}
              continue
        -- Place the pending literals the value reads.
        for x in letValueFVars v do
          if let some l := pending[x]? then
            pending := pending.erase x
            acc := acc.push l
        acc := acc.push d
        code := k
    | .return x =>
      let y := ren.getD x x
      match stack.back? with
      | some fr =>
        -- The value of a spliced closed term stays pending until its use.
        stack := stack.pop
        code := fr.code
        ren := fr.ren.insert fr.binder y
      | none =>
        if let some l := pending[y]? then acc := acc.push l
        return (acc, y, spliced)
    -- Not reached: the code is straight-line (`straightLine`, `spliceable`).
    | _ => return (acc, default, spliced)
  return (acc, default, spliced)

/-- Splice the chains of closed terms evaluated where they are used
(`chainConsts`) into the constants that use them. Lean's `extractClosed`
makes an `n`-element literal (`#[…]`, `[…]`, a `ByteArray`) a chain of `n`
closed terms, `_closed_k := push _closed_(k-1) e_k`, and rrc compiles
about 80 functions per second: a 100000-element array literal took ten
minutes to build as 100000 functions calling each other. Spliced, the
literal is one straight-line body (cut into parts by `Outline`), evaluated
as before: once, where the constant using it is evaluated. Code that is not
straight-line is left as it is. -/
def spliceChainConsts (decls : Array (Decl .pure)) (inline : NameSet) : Array (Decl .pure) := Id.run do
  if inline.isEmpty then return decls
  let byName := decls.foldl (fun m d => m.insert d.name d) ({} : NameMap (Decl .pure))
  let mut spliced : NameSet := {}
  let mut out := #[]
  for d in decls do
    match d.value with
    | .code c =>
      -- From the constants that are not themselves spliced (each chain
      -- once, from its end).
      if !d.params.isEmpty || inline.contains d.name || !straightLine c then
        out := out.push d
        continue
      let (lets, y, s) := spliceChains byName inline c
      if s.isEmpty then
        out := out.push d
      else
        -- (A literal never read is dropped: it has no effect.)
        spliced := s.foldl (·.insert ·) spliced
        let body := lets.foldr (fun l k => Code.let l k) (Code.return y)
        out := out.push { d with value := .code body }
    | _ => out := out.push d
  return out.filter fun d => !spliced.contains d.name

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
  -- Closed terms used once, by another constant, are not cached; those
  -- read by straight-line code are spliced into it.
  let uncachedConsts := chainConsts decls roots
  let decls := spliceChainConsts decls uncachedConsts
  let ctx : LowerCtx := { table, decls := decls.foldl (fun m d => m.insert d.name d) {}, keys, preludeFns,
                          preludeRets, preludeParams, ioErrorBuilders, valueGenericFns, valueGenericCls,
                          uncachedConsts, preludeReplacements := cfg.preludeReplacements,
                          valueStructs := cfg.valueStructs, fieldOrder := cfg.fieldOrder }
  let act : LowerM (Array RR.Item × Std.HashSet String) := do
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
    return (← fnTypeItems, ← anchoredFns)
  let ((fnItems, anchored), st) ← (act.run ctx).run {}
  let boxItem := RR.Item.enum boxName false (st.boxVariants.map fun (t, v) => (v, #[t]))
  -- Deep and long tail paths and `let` values cut into functions, for rrc
  -- (`Outline`; first, so that the passes after it see bounded functions),
  -- then the registry's passes over the generated functions
  -- (`Opt/SinkProj`: projections sunk into the branches that use them).
  let types := st.typeItems ++ fnItems |>.push boxItem
  -- Runs of pushed `Nat` literals (a spliced `Array Nat` literal) as tables.
  let (fns, natTables) := ArrayLits.natArrLits st.fns
  let (fns, stepItems) := Outline.outlineFns {} (Outline.variantTable types prelude)
    (Outline.takenNames preludeFns fns) fns
  let rrProg : RRProgram := { prelude, preludeFns, types := types ++ stepItems }
  let fns := cfg.rrPasses.foldl (fun fns p => p rrProg fns) fns
  let mut out := prelude ++ "\n// ---- generated types ----\n\n"
  for it in st.typeItems do out := out ++ it.render ++ "\n"
  for it in fnItems do out := out ++ it.render ++ "\n"
  for it in stepItems do out := out ++ it.render ++ "\n"
  out := out ++ boxItem.render ++ "\n"
  out := out ++ "// ---- generated functions ----\n\n"
  -- `#[transform_anchor]` keeps a function out of Reussir's MLIR inliner (a
  -- transform anchor stays a function for transform scripts; lean2rr has
  -- none, and LLVM still inlines it): see `anchoredFns`.
  for f in fns do
    let anchor := match f with
      | .fn n .. => anchored.contains n
      | _ => false
    out := out ++ (if anchor then "#[transform_anchor]\n" else "") ++ f.render ++ "\n"
  unless st.strLits.isEmpty do out := out ++ strLitTable st.strLits
  unless natTables.isEmpty do out := out ++ ArrayLits.natLitTable natTables
  return out

end LeanToReussir
