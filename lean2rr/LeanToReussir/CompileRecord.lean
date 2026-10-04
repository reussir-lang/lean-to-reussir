import Lean

/-!
# What the `.olean` records of Lean's compilation

A module's `.olean` keeps, besides each declaration's LCNF and IR, the list
of its IR declarations that are not kernel constants (`extraConstNames`:
closed terms, `_boxed` wrappers, lifted lambdas, specializations), newest
first. Lean adds a command's IR when it compiles the command, so the list
gives the order in which Lean compiled the module's declarations (used for
the startup order, translation plan §5.12) and which closed terms each
declaration made (used to extract closed terms as Lean did, §3). The IR
bodies, kept in the `.olean` of a module that is not a `module` file, say
which closed terms each declaration reads (a `module` file keeps them in
its `.ir` file).
-/

namespace LeanToReussir
open Lean Compiler LCNF

/-- Whether a module belongs to the Lean toolchain (its constants are
evaluated lazily; see translation plan §5.12). -/
def isToolchainModule (m : Name) : Bool :=
  m.getRoot ∈ [`Init, `Std, `Lean, `Lake, `L2RShim]

/-- Whether a toolchain module belongs to the part of Lean's library that
lean2rr supports, `Init` and `Std`: its `initialize` declarations run at
startup, used or not, at the module's place (`libraryModuleItems`, §5.12). -/
def isLibraryModule (m : Name) : Bool :=
  m.getRoot ∈ [`Init, `Std]

/-- The declaration that compiled to the IR-only declaration `n`: `n`
without the suffixes the compiler appends (`c._closed_3`, `c._boxed`,
`c._lam_0`, `f._at_.c.spec_2._redArg`), the nearest prefix that `known`
accepts. A hygienic name keeps its macro scopes at the end
(`zz._closed_0._@.M._hyg.3` is a closed term of `zz._@.M._hyg.3`). -/
partial def compiledOwner (known : Name → Bool) (n : Name) : Option Name :=
  if known n then some n
  else if n.hasMacroScopes then
    let v := extractMacroScopes n
    match v.name with
    | .str p _ | .num p _ => compiledOwner known { v with name := p }.review
    | .anonymous => none
  else match n with
    | .str p _ | .num p _ => compiledOwner known p
    | .anonymous => none

/-- Lean's compilation order of a module's declarations, as far as the
`.olean` records it: the module's `extraConstNames` are its IR
declarations that are not kernel constants (closed terms, `_boxed`
wrappers, lifted lambdas, specializations), newest first, and Lean adds a
command's IR when it compiles the command. So each declaration that
compiled to at least one of them (nearly every constant whose value
calls a function) gets the index of its first one; the specializations
made while compiling a declaration come right before it. Native Lean runs
the module's initializers in exactly this order (`EmitC.emitInitFn`). -/
def compileOrder (idx : Nat) : CoreM (Std.HashMap Name Nat) := do
  let env ← getEnv
  let some md := env.header.moduleData[idx]? | return {}
  let mut baseNames : Std.HashSet Name := {}
  for d in baseExt.getModuleEntries env idx (level := .private) do
    baseNames := baseNames.insert d.name
  let known (n : Name) : Bool := baseNames.contains n || env.contains n
  let extra := md.extraConstNames
  let mut out : Std.HashMap Name Nat := {}
  for i in [:extra.size] do
    if let some d := compiledOwner known extra[extra.size - 1 - i]! then
      unless out.contains d do out := out.insert d i
  return out

/-- `n` without a last `_closed_N` component (macro scopes kept at the
end), if it has one: the declaration whose extraction made the closed term
`n`. -/
def closedTermOwner? (n : Name) : Option Name :=
  if n.hasMacroScopes then
    let v := extractMacroScopes n
    match v.name with
    | .str p s => if s.startsWith "_closed_" then some { v with name := p }.review else none
    | _ => none
  else match n with
    | .str p s => if s.startsWith "_closed_" then some p else none
    | _ => none

/-- How Lean extracted the closed terms of one module's declarations (Lean's
`extractClosed` keeps a cache of the closed terms made so far while it
compiles a module, so a later declaration with an equal term reads the
earlier one's). Declarations are named as in the IR (`f`, `f._lam_0`,
`f._at_.g.spec_2`). -/
structure ClosedRecord where
  /-- The compilation order (`compileOrder`). -/
  order : Std.HashMap Name Nat := {}
  /-- The declarations whose extraction made closed terms (`d._closed_N`). -/
  makers : Std.HashSet Name := {}
  /-- For each of those, the index of its first closed term in the record
  (closed terms are recorded in the order Lean made them). -/
  firstClosed : Std.HashMap Name Nat := {}
  /-- The declarations whose IR reads a closed term, when the IR bodies are
  known (in the `.olean`, or for a `module` file in its `.ir` file). -/
  readers : Option (Std.HashSet Name) := none
  /-- The module's IR declarations. -/
  known : Std.HashSet Name := {}
  deriving Inhabited

/-- The IR declarations of a `module` file, from its `.ir` file next to its
`.olean` (its `.olean` keeps only their signatures), if there is one. -/
unsafe def moduleIRDeclsImpl (mod : Name) : IO (Array IR.Decl) := do
  let olean ← findOLean mod
  let ir := olean.withExtension "ir"
  unless ← ir.pathExists do return #[]
  -- The region stays mapped: the declarations point into it.
  let (md, _) ← readModuleData ir
  let some (_, es) := md.entries.find? (·.1 == ``IR.declMapExt) | return #[]
  return es.map fun e => unsafeCast e

@[implemented_by moduleIRDeclsImpl]
opaque moduleIRDecls (mod : Name) : IO (Array IR.Decl)

/-- The closed-term record of module `idx`. -/
def closedRecord (idx : Nat) : CoreM ClosedRecord := do
  let env ← getEnv
  let some md := env.header.moduleData[idx]? | return {}
  let mut makers : Std.HashSet Name := {}
  let mut firstClosed : Std.HashMap Name Nat := {}
  let mut closed : Std.HashSet Name := {}
  let extra := md.extraConstNames
  for i in [:extra.size] do
    let n := extra[extra.size - 1 - i]!
    if let some d := closedTermOwner? n then
      makers := makers.insert d
      unless firstClosed.contains d do firstClosed := firstClosed.insert d i
      closed := closed.insert n
  let mut known : Std.HashSet Name := extra.foldl (·.insert ·) {}
  let mut decls := IR.declMapExt.getModuleEntries env idx
  for d in decls do known := known.insert d.name
  unless decls.any (· matches .fdecl ..) do
    let mod := env.header.moduleNames[idx]!
    decls ← (try moduleIRDecls mod catch _ => pure #[])
  let mut readers : Std.HashSet Name := {}
  let mut bodies := false
  for d in decls do
    let .fdecl .. := d | continue
    bodies := true
    if (IR.collectUsedDecls env [d]).any closed.contains then readers := readers.insert d.name
  return { order := ← compileOrder idx, makers, firstClosed, known,
           readers := if bodies then some readers else none }

end LeanToReussir
