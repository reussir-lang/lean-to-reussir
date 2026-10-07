import Lean
import LeanToReussir.Collect
import LeanToReussir.Relevance
import LeanToReussir.Passes
import LeanToReussir.CompileRecord
import LeanToReussir.Env

/-!
# Stage 1: monomorphization

Turns the reachable part of a program's base-phase LCNF into a closed,
monomorphic program (translation plan §2):

* every declaration is copied once per list of type arguments it is used
  at — an *instance* — under a fresh name, so that Lean's passes in Stage 2
  only ever see these copies, never Lean's persisted polymorphic versions;
* instantiation is the substitution Lean's own specializer performs
  (`Specialize.mkSpecDecl`): type-former parameters are replaced by their
  arguments and dropped, and all types are re-normalized (beta);
* Lean's base `simp` then runs on each instance, which inlines statically
  known type-class instances and folds dictionary projections into direct
  calls;
* finally every call is redirected to the instance of its callee.

A type argument that is not statically known (it mentions a local type
variable, or it keeps growing under polymorphic recursion) is replaced by
`lcAny`; values of that type later use the uniform `Box` representation.
Nothing is rejected.
-/

namespace LeanToReussir
open Lean Compiler LCNF

/-- An instance: a declaration and the (normalized, ground) arguments of its
type-former parameters, in parameter order. -/
structure InstKey where
  decl : Name
  typeArgs : Array Expr
  /-- For each class-typed parameter (in order): the statically known
  dictionary passed for it, if any (see `DictExpr`). Empty when none is. -/
  dicts : Array (Option Expr) := #[]
  deriving BEq, Hashable, Inhabited

def InstKey.describe (k : InstKey) : String :=
  if k.typeArgs.isEmpty then toString k.decl
  else s!"{k.decl} [{", ".intercalate (k.typeArgs.toList.map toString)}]"

structure MonoConfig where
  /-- Type arguments larger than this (in expression nodes) are replaced by
  `lcAny`; this bounds instantiation under polymorphic recursion. -/
  maxTypeArgSize : Nat := 64
  /-- A declaration with more instances than this gets further instances at
  `lcAny` only. -/
  maxInstancesPerDecl : Nat := 1024
  /-- Run Lean's base `simp` on each instance (dictionary folding). -/
  simp : Bool := true
  /-- Replace type-unsafe library implementations by their safe sources
  (recompiling tainted callers). Not needed for correctness: lean2rr
  represents Lean's uniform-representation code with `Box` (see
  `uniformCode`) and placeholders. -/
  safeSources : Bool := false
  /-- The functions the prelude (`runtime/prelude.rr`) declares
  (`preludeFnDecls`): which symbols lean2rr's runtime implements
  (`computeExternRoute`'s hint). -/
  preludeFns : Std.HashSet String := {}

/-- The functions a prelude declares: the names of its lines that start
with `fn NAME` or `pub fn NAME`, outside the Rust code of its textures
(`[{ … }]`, which declares C functions such as `gettid` for itself). Both
Stage 1 (`computeExternRoute`'s hint) and the lowering (`LowerCtx.preludeFns`)
decide from this set whether lean2rr implements a symbol. -/
def preludeFnDecls (prelude : String) : Except String (Std.HashSet String) := do
  let mut out : Std.HashSet String := {}
  let mut depth : Int := 0
  let mut lineNo := 0
  for line in prelude.splitOn "\n" do
    lineNo := lineNo + 1
    if depth == 0 then
      let rest := if line.startsWith "pub fn " then some (line.drop 7).toString
        else if line.startsWith "fn " then some (line.drop 3).toString else none
      if let some rest := rest then
        let name := (rest.takeWhile fun c => c.isAlphanum || c == '_').toString
        unless name.isEmpty do out := out.insert name
    -- Texture delimiters outside `//` comments.
    let code := (line.splitOn "//").head!
    depth := depth + ((code.splitOn "[{").length - 1 : Nat) - ((code.splitOn "}]").length - 1 : Nat)
    if depth < 0 then throw ("prelude line " ++ toString lineNo ++ ": `}]` without a texture to close")
  if depth != 0 then throw ("prelude: " ++ toString depth ++ " texture(s) (`[{`) not closed by `}]`")
  return out

/-- `preludeFnDecls` in `CoreM`: a prelude whose textures do not balance is
an error. -/
def preludeFnDeclsM (prelude : String) : CoreM (Std.HashSet String) := do
  match preludeFnDecls prelude with
  | .ok s => return s
  | .error e => throwError "cannot read the prelude's functions: {e}"

/-- How lean2rr implements an extern that is not of Lean's library (an
extern of the program or of a package it uses; `externRoute`). -/
inductive ExternRoute where
  /-- `@[implemented_by g]`: calls of the extern call `g`, as natively. -/
  | implementedBy (g : Name)
  /-- Its C symbol is the `@[export]` of `g`, which passes the binding
  tests: the extern is a `noinline` declaration calling `g`
  (`exportForwardDecl`). -/
  | «export» (g : Name)
  /-- Its Lean definition, compiled by lean2rr (`MonoState.extraBase`). -/
  | body
  /-- None of the above: refused, with the reason (`LowerCtx.externRefusals`). -/
  | refused (why : String)
  deriving Inhabited

structure MonoState where
  config : MonoConfig
  /-- Instance key ↦ fresh instance name. -/
  names : Std.HashMap InstKey Name := {}
  /-- Instances per original declaration, for the per-declaration cap. -/
  perDecl : NameMap Nat := {}
  work : Array (InstKey × Name) := #[]
  /-- Instance declarations with code, in creation order. -/
  decls : Array (Decl .pure) := #[]
  /-- Extern instances: polymorphic externs at ground types. -/
  externs : Array (Decl .pure) := #[]
  /-- Monomorphic externs referenced (kept under their own names). -/
  monoExterns : NameSet := {}
  /-- Instance name ↦ key, for diagnostics and statistics. -/
  keys : NameMap InstKey := {}
  /-- Number of type arguments replaced by `lcAny`. -/
  uniformArgs : Nat := 0
  /-- `unsafe` implementation ↦ the safe declaration it implements
  (`@[implemented_by]`), built on first use. -/
  unsafeImpls : Option (NameMap Name) := none
  /-- Export symbol ↦ declaration (lazily computed). -/
  exports : Option (Std.HashMap String Name) := none
  /-- Constants defined by `initialize`/`builtin_initialize` that the
  program references, with their init functions (in discovery order). -/
  initConsts : Array (Name × Name) := #[]
  /-- The instance being built (for detecting polymorphic recursion). -/
  current : Option InstKey := none
  /-- Its name. -/
  currentInst : Option Name := none
  /-- Instance ↦ the instance whose code first asked for it: the
  instantiation path, along which polymorphic recursion is detected. -/
  parentOf : NameMap Name := {}
  /-- Base declarations compiled by lean2rr itself (safe reference
  definitions of unsafe implementations, and their auxiliary declarations). -/
  extraBase : NameMap (Decl .pure) := {}
  /-- Safe definitions that could not be compiled (the unsafe version stays). -/
  uncompilable : NameSet := {}
  /-- The externs of Lean's library by C symbol (lazily computed). -/
  toolchainExterns : Option (Std.HashMap String (Array Name)) := none
  /-- The C symbols of the externs in the source of Lean's whole library,
  imported or not, with the module declaring each (lazily read,
  `librarySourceExternSyms`). -/
  librarySourceExterns : Option (Std.HashMap String Name) := none
  /-- How each extern of the program met so far is implemented
  (`externRoute`). -/
  externRoutes : NameMap ExternRoute := {}
  /-- Externs of the program compiled from their Lean definition, with
  their symbols (`externLabel`), in the order met. -/
  externBodies : Array (String × Name) := #[]
  /-- Those of `externBodies` whose C symbol natively runs a function of
  Lean's library (`nativeLibraryFunction?`: "Lean's runtime function" or
  "Lean's library function"), for lean2rr's note. -/
  externBodiesOfRuntime : NameMap String := {}
  /-- Externs of the program that run their Lean definition although their
  C symbol is the `@[export]` of another declaration of the program whose
  binding's tests fail: the reasons, for lean2rr's warning (natively the
  call runs that definition). -/
  externBindingWarnings : Array (Name × Array String) := #[]

abbrev MonoM := StateRefT MonoState CoreM

/-- Replace universe levels by `0`: representation never depends on them. -/
def eraseLevels (e : Expr) : Expr :=
  e.replace fun
    | .const n (_ :: _) => some (.const n [])
    | .sort (.succ _) => some (.sort levelOne)
    | .sort (.param _) | .sort (.max ..) | .sort (.imax ..) => some (.sort levelOne)
    | _ => none

/-- The number of nodes of `e` as a tree, counting up to `cap` (a type
built by polymorphic recursion such as `α × α` doubles at each step, so
its tree size, which later stages traverse, is exponential in its depth). -/
partial def treeSizeUpTo (e : Expr) (cap : Nat) : Nat :=
  go e 0
where
  go (e : Expr) (acc : Nat) : Nat :=
    if acc ≥ cap then acc else
    match e with
    | .app f a => go a (go f (acc + 1))
    | .forallE _ d b _ | .lam _ d b _ => go b (go d (acc + 1))
    | .mdata _ b => go b (acc + 1)
    | _ => acc + 1

/-- Normalize a type argument: beta, erase levels, and replace anything that
is not statically known, or too large, by `lcAny`. -/
def normTypeArg (e : Expr) : MonoM Expr := do
  let e ← Core.betaReduce e
  let e := eraseLevels e
  let known := !e.hasFVar && !e.hasLooseBVars && !e.hasMVar
  let cap := (← get).config.maxTypeArgSize
  if !known || e.approxDepth.toNat > cap || treeSizeUpTo e (4 * cap) ≥ 4 * cap then
    modify fun s => { s with uniformArgs := s.uniformArgs + 1 }
    return anyExpr
  return e

/-- A fresh name for an instance of `decl`. Appending a numeric component
keeps the original name readable in dumps and cannot clash with any Lean
declaration. -/
def freshInstName (decl : Name) (k : Nat) : Name :=
  .num (decl ++ `_l2r) k

/-- Look up (or create and enqueue) the instance for `key`. -/
def instanceName (key : InstKey) : MonoM Name := do
  if let some n := (← get).names[key]? then return n
  -- Polymorphic recursion: an instance of `d` asking for `d` at type
  -- arguments that strictly contain its own (`Nest α` → `Nest (List α)`)
  -- would create a new instance per level; use the uniform one at once. A
  -- type function (a monad `m` → `StateT Nat m`) no longer contains the
  -- caller's argument once beta-reduced, so there a strictly larger
  -- argument counts as growth.
  let grows (a b : Expr) : Bool :=
    a != b && a != anyExpr &&
      ((b.find? (· == a)).isSome ||
       ((a.isLambda || b.isLambda) && treeSizeUpTo b 1000 > treeSizeUpTo a 1000))
  -- The request can come from another declaration of the cycle (a `where`
  -- helper, a mutual partner: `nestI` → `nestI.helper` → `nestI` at
  -- `StateT Nat m`), so it is compared with the instances of the same
  -- declaration on the path that led to the requesting instance, up to the
  -- nearest uniform one. A request made under the uniform instance at a
  -- type built from its `lcAny` (`List lcAny`, `lcAny × lcAny`) is the same
  -- recursion, and goes to the uniform instance too: a typed instance at
  -- that type would receive whatever the uniform code passes there, and a
  -- value only `unsafeCast` to it (natively any object) could not be
  -- converted at all. A type function
  -- (a monad `m` → `OptionT m`) instead gets one typed instance at
  -- `F lcAny`, whose own request `F (F lcAny)` grows: the uniform instance
  -- has no static dictionary, and the typed one adapts the dictionary it
  -- receives.
  let s ← get
  let onPath : Bool := Id.run do
    let mut inst := s.currentInst
    let mut fuel := 100000
    while fuel > 0 do
      let some n := inst | return false
      if let some k := s.keys.find? n then
        if k.decl == key.decl && k.typeArgs.size == key.typeArgs.size then
          if k.typeArgs.all (· == anyExpr) then
            return key.typeArgs.any fun b => b != anyExpr && !b.isLambda && (b.find? (· == anyExpr)).isSome
          if (k.typeArgs.zip key.typeArgs).any (fun (a, b) => grows a b) then return true
      inst := s.parentOf.find? n
      fuel := fuel - 1
    return false
  let key ← if !key.typeArgs.isEmpty && onPath then
      modify fun s => { s with uniformArgs := s.uniformArgs + key.typeArgs.size }
      pure { key with typeArgs := key.typeArgs.map fun _ => anyExpr, dicts := #[] }
    else pure key
  if let some n := (← get).names[key]? then return n
  let count := (← get).perDecl.getD key.decl 0
  let key ← if count ≥ (← get).config.maxInstancesPerDecl &&
       !(key.typeArgs.all (· == anyExpr) && key.dicts.isEmpty) then
      -- Past the cap: the uniform instance (no static dictionaries either,
      -- which can grow without bound under polymorphic recursion too).
      modify fun s => { s with uniformArgs := s.uniformArgs + key.typeArgs.size }
      pure { key with typeArgs := key.typeArgs.map fun _ => anyExpr, dicts := #[] }
    else pure key
  if let some n := (← get).names[key]? then return n
  let n := freshInstName key.decl count
  modify fun s => { s with
    names := s.names.insert key n
    perDecl := s.perDecl.insert key.decl (count + 1)
    work := s.work.push (key, n)
    keys := s.keys.insert n key
    parentOf := match s.currentInst with
      | some p => s.parentOf.insert n p
      | none => s.parentOf }
  return n

/-- `unsafe` implementations of `@[implemented_by]` declarations, mapped to
the safe declaration they implement. -/
def unsafeImplMap : MonoM (NameMap Name) := do
  if let some m := (← get).unsafeImpls then return m
  let env ← getEnv
  let mut m : NameMap Name := {}
  for (n, _) in env.constants.map₁.toList do
    if let some impl := Compiler.getImplementedBy? env n then
      if let some ci := env.find? impl then
        if ci.isUnsafe && !(env.find? n |>.map (·.isUnsafe) |>.getD true) then
          m := m.insert impl n
  modify fun s => { s with unsafeImpls := some m }
  return m

/-- C symbol ↦ the Lean definition exported under it (`@[export sym]`). -/
def exportMap : MonoM (Std.HashMap String Name) := do
  if let some m := (← get).exports then return m
  let env ← getEnv
  let mut m : Std.HashMap String Name := {}
  for i in [:env.header.moduleNames.size] do
    for (decl, sym) in exportAttr.ext.getModuleEntries env i do
      m := m.insert (sym.toString (escape := false)) decl
  modify fun s => { s with exports := some m }
  return m

/-- Whether a constant's definition casts through `unsafeCast`/`NonScalar`. -/
def usesCast (c : Name) : CoreM Bool := do
  let some ci := (← getEnv).find? c | return false
  let some v := ci.value? (allowOpaque := true) | return false
  return v.foldConsts false fun k b => b || k == ``unsafeCast || k == ``NonScalar || k == ``PNonScalar

/-- The declaration a name belongs to, for auxiliary names: the user-facing
name without the private prefix. -/
def userName (n : Name) : Name := (privateToUserName? n).getD n

/-- Type-unsafe implementations: `unsafe` `@[implemented_by]` targets whose
code (or auxiliary code) casts through `unsafeCast`/`NonScalar`, so that
their LCNF types are not the types of the values. `Array.mapMUnsafe`
stores a `String` into what its types call an `Array Nat`. Other unsafe
implementations, like `partial`'s `_unsafe_rec`, are type-correct. -/
def isTypeUnsafeImpl (c : Name) : MonoM Bool := do
  unless (← unsafeImplMap).contains c do return false
  if ← usesCast c then return true
  let some ci := (← getEnv).find? c | return false
  let some v := ci.value? (allowOpaque := true) | return false
  let aux := v.foldConsts #[] fun k acc => if (userName c).isPrefixOf (userName k) && k != c then acc.push k else acc
  aux.anyM fun k => usesCast k

/-- Is `c` a type-unsafe implementation or one of its auxiliary declarations? -/
def isTypeUnsafeCode (c : Name) : MonoM Bool := do
  if ← isTypeUnsafeImpl c then return true
  let u := userName c
  for (impl, _) in (← unsafeImplMap).toList do
    if (userName impl).isPrefixOf u && u != userName impl then
      if ← isTypeUnsafeImpl impl then return true
  return false

/-- The origin of a specialization name `X._at_.Y.spec_N`: `X`, rebuilt
component by component (`X` can be hygienic, `helper._@.M._hyg.3`: Lean puts
`_at_` after the macro scopes; round 9 RV9S-01). -/
def specOrigin? (n : Name) : Option Name :=
  let comps := n.components
  match comps.idxOf? `_at_ with
  | some i => some (nameOfComponents (comps.take i))
  | none => none

/-- A persisted base declaration is *tainted* when its body reaches
type-unsafe code, directly or through specializations Lean derived from it. -/
partial def isTainted (d : Decl .pure) (visiting : NameSet := {}) : MonoM Bool := do
  let .code c := d.value | return false
  for k in codeConsts c #[] do
    if ← isTypeUnsafeCode k then return true
    if let some o := specOrigin? k then
      if ← isTypeUnsafeCode o then return true
      if !visiting.contains k then
        if let some kd ← getBaseDecl? k then
          if ← isTainted kd (visiting.insert k) then return true
  return false

/-- Rename the targets of constant applications. -/
partial def renameConsts (rename : Name → Name) : Code .pure → Code .pure
  | .let d k =>
    let d := match d.value with
      | .const f us args _ => { d with value := .const (rename f) us args }
      | _ => d
    .let d (renameConsts rename k)
  | .fun d k _ => .fun (FunDecl.mk d.fvarId d.binderName d.params d.type (renameConsts rename d.value)) (renameConsts rename k)
  | .jp d k => .jp (FunDecl.mk d.fvarId d.binderName d.params d.type (renameConsts rename d.value)) (renameConsts rename k)
  | .cases cs => .cases ⟨cs.typeName, cs.resultType, cs.discr, cs.alts.map fun
      | .alt c ps k _ => .alt c ps (renameConsts rename k)
      | .default k => .default (renameConsts rename k)
      | a => a⟩
  | c => c

/-- The base-pass pipeline lean2rr uses to compile a declaration from
source: Lean's base passes before `saveBase`, except that
* `implemented_by` replacement is done by lean2rr's own pass, which skips
  type-unsafe implementations and maps them back to their safe declaration;
* nothing pulls in persisted callee bodies (no inlining of definitions, no
  `specialize`), since those may already contain type-unsafe code. -/
def recompilePasses : MonoM (Array Pass) := do
  let implOf ← unsafeImplMap
  let mut unsafeTargets : NameSet := {}
  for (impl, _) in implOf.toList do
    if ← isTypeUnsafeImpl impl then unsafeTargets := unsafeTargets.insert impl
  let env ← getEnv
  let rename (n : Name) : Name :=
    if unsafeTargets.contains n then (implOf.find? n).getD n
    else match Compiler.getImplementedBy? env n with
      | some impl => if unsafeTargets.contains impl then n else impl
      | none => n
  let implPass : Pass := {
    name := `l2rImplementedBy, phase := .base
    run := fun decls => return decls.map fun d => { d with value := d.value.mapCode (renameConsts rename) } }
  let m ← getPassManager
  let some i := m.basePasses.findIdx? (·.name == `saveBase) | throwError "lean2rr: no saveBase pass"
  let mut out := #[]
  -- `simp` must not inline persisted bodies here: Lean's persisted callers
  -- already call type-unsafe implementations, and inlining them would bring
  -- their untypable code back. Callees are instantiated (and recompiled if
  -- tainted) on their own; Stage 2 inlines lean2rr's safe instances.
  for p in m.basePasses[:i] do
    if p.name == `simp && p.occurrence == 1 then
      out := out.push implPass
      out := out.push (LCNF.simp { etaPoly := true, inlinePartial := true, implementedBy := false, inlineDefs := false } (occurrence := 1))
    else if p.name == `simp then
      out := out.push (LCNF.simp { inlineDefs := false } (occurrence := p.occurrence))
    else if p.name == `specialize then
      -- Lean's specializer instantiates persisted callee bodies, which may be
      -- tainted; lean2rr instantiates (and recompiles) callees itself.
      out := out.push implPass
    else out := out.push p
  return out

/-- Compile a declaration from its source definition with `recompilePasses`.
New auxiliary declarations (lambda lifting, specializations) are recorded
too. Returns `false` if Lean cannot compile it. -/
def recompile (n : Name) : MonoM Bool := do
  if (← get).extraBase.contains n then return true
  if (← get).uncompilable.contains n then return false
  let passes ← recompilePasses
  try
    let decls ← (do
        let d ← toDecl n
        runPasses passes (markRecDecls #[d]) false : CompilerM _).run (phase := .base)
    modify fun s => { s with extraBase := decls.foldl (fun m d => m.insert d.name d) s.extraBase }
    return true
  catch e =>
    if (← IO.getEnv "L2R_DEBUG").isSome then IO.eprintln s!"lean2rr: cannot recompile {n}: {← e.toMessageData.toString}"
    modify fun s => { s with uncompilable := s.uncompilable.insert n }
    return false

/-- One identification of `toMono` (`toMonoType`, `toMonoTypeKeep`) at the
head of `t` (`monoHead`): `.ok (some u)` when `t` is identified with `u` (a
trivial structure, such as `Subtype`, `Fin`, a one-field structure or a
one-method class, with its field's type; `Decidable` with `Bool`;
`NonScalar` and `PNonScalar` with `lcAny`), `.ok none` when none applies,
`.error ()` when the field's type depends on another field (unclassified). -/
def monoHeadStep (t : Expr) : CoreM (Except Unit (Option Expr)) := do
  let .const n _ := t.getAppFn | return .ok none
  if n == ``Decidable then return .ok (some (mkConst ``Bool))
  if n == ``NonScalar || n == ``PNonScalar then return .ok (some anyExpr)
  let some info ← hasTrivialStructure? n | return .ok none
  let ctorType ← getOtherDeclBaseType info.ctorName []
  let some field := (getParamTypes (← instantiateForall ctorType t.getAppArgs[:info.numParams].toArray))[info.fieldIdx]?
    | return .error ()
  if field.hasLooseBVars then return .error ()
  return .ok (some field)

/-- `t` with the identifications of `toMono` (`toMonoType`, `toMonoTypeKeep`)
applied at its head, until none applies: a trivial structure (`Subtype`,
`Fin`, a one-field structure, a one-method class) is its field's type,
`Decidable` is `Bool`, `NonScalar` and `PNonScalar` are `lcAny`. `none`
when the field's type depends on another field (unclassified). -/
partial def monoHead (t : Expr) (fuel : Nat := 32) : CoreM (Option Expr) := do
  let t := t.consumeMData.headBeta
  match ← monoHeadStep t with
  | .error _ => return none
  | .ok none => return some t
  | .ok (some u) =>
    if (t.getAppFn.constName? |>.any fun n => n == ``Decidable || n == ``NonScalar || n == ``PNonScalar) then
      return some u
    if fuel == 0 then return none
    monoHead u (fuel - 1)

/-! ## Externs: Lean's runtime library, else Lean code

lean2rr compiles Lean code, and Lean's runtime library is the only native
code it uses (the owner's decision of 2026-10-03; translation plan §5.8,
"Lean-only target"). An extern of Lean's library, declared in a module of
the toolchain (`isToolchainDecl`), is served by lean2rr's runtime: one the
runtime lacks is reported by the lowering, never replaced by its Lean
body, which is often a slow reference definition (the gap is the
runtime's). Any other extern, of the program or of a package it uses,
takes the first of these routes that applies (`externRoute`); its C code
is never called, compiled or linked:
1. `@[implemented_by g]`: `g`, as natively.
2. A binding of its C symbol to the `@[export]` of another declaration `g`
   of the program (not of Lean's library, review REB-14), the function
   native Lean's call is linked to (the extern becomes a
   `noinline` declaration calling `g`, `exportForwardDecl`). The binding
   holds when two tests pass (`bindingFailure?`): its type is an instance
   of `g`'s, and one compiled signature. A Lean body the extern has is
   then not used: natively the linked function runs.
3. Its Lean definition, compiled as if the attribute were not there
   (`externBodyDecl`), also when its C symbol is that of an extern of
   Lean's runtime library: an extern of the program is never bound to
   Lean's runtime (the owner's decision of 2026-10-04).
4. Otherwise it is refused: the lowering reports it with the reason
   (`LowerCtx.externRefusals`), naming any binding test that failed and,
   for a symbol of Lean's runtime library, the declaration to call
   instead. -/

/-- The externs declared by Lean's library (`Init`, `Std`, `Lean`, `Lake`),
by C symbol. -/
def toolchainExternSyms : MonoM (Std.HashMap String (Array Name)) := do
  if let some s := (← get).toolchainExterns then return s
  let env ← getEnv
  let mut s : Std.HashMap String (Array Name) := {}
  for i in [:env.header.moduleNames.size] do
    unless isToolchainModule env.header.moduleNames[i]! do continue
    for (n, _) in externAttr.ext.getModuleEntries env i do
      if let some sym := getExternNameFor env `c n then s := s.insert sym ((s.getD sym #[]).push n)
  modify fun st => { st with toolchainExterns := some s }
  return s

/-- The string literals of the `@[extern …]` (or `attribute [extern …]`)
attributes on a line of Lean source: those after the word `extern`, up to
the attribute's `]`. -/
def externAttrStrings (line : String) : List String :=
  match line.splitOn "extern" with
  | [] | [_] => []
  | _ :: rest => rest.flatMap fun part =>
    let attr := (part.splitOn "]").head!
    (attr.splitOn "\"").zipIdx.filterMap fun (t, i) => if i % 2 == 1 then some t else none

/-- The C symbols of the `@[extern]` declarations in the source of Lean's
library, each with the module that declares it, (`src/lean/{Init,Std,Lean}` and `src/lean/lake/Lake` of the
toolchain lean2rr is built with), whether or not the program imports their
modules: read from the source text (`externAttrStrings`), since an `.olean`
the program does not import is not loaded. Symbolic links to directories
are not followed (a cycle would recurse without end, review REB-09). Empty
when the toolchain ships no source. Used only for the message of a refused
extern whose symbol is a prelude function (`computeExternRoute`). -/
def librarySourceExternSyms : MonoM (Std.HashMap String Name) := do
  if let some s := (← get).librarySourceExterns then return s
  let mut out : Std.HashMap String Name := {}
  try
    let src := (← toolchainSysroot) / "src" / "lean"
    let notLink (d : System.FilePath) : IO Bool := do
      return (← d.symlinkMetadata).type != .symlink
    -- (directory, the directory module names are relative to)
    for (dir, base) in [(src / "Init", src), (src / "Std", src), (src / "Lean", src),
        (src / "lake" / "Lake", src / "lake")] do
      unless ← dir.isDir do continue
      for f in ← dir.walkDir notLink do
        unless f.extension == some "lean" do continue
        let rel := (f.withExtension "").toString.drop (base.toString.length + 1)
        let mod := (rel.toString.splitOn "/").foldl (fun n c => Name.mkStr n c) .anonymous
        let text ← try IO.FS.readFile f catch _ => pure ""
        for line in text.splitOn "\n" do
          for sym in externAttrStrings line do
            unless out.contains sym do out := out.insert sym mod
  catch _ => pure ()
  modify fun st => { st with librarySourceExterns := some out }
  return out

/-- Whether `n` is declared in Lean's library or in lean2rr's shim: in a
module named `Init.*`, `Std.*`, `Lean.*`, `Lake.*` or `L2RShim.*`
(`isToolchainModule`). `Env.loadEnvironment` checks that each module so
named is the file of that name in the library of lean2rr's toolchain (or in
the shim directory), so the name decides it. -/
def isToolchainDecl (n : Name) : CoreM Bool := do
  let env ← getEnv
  match env.getModuleIdxFor? n with
  | some i => return isToolchainModule env.header.moduleNames[i.toNat]!
  | none => return false

/-- `e` without metadata, such as the borrow marks `@&`. -/
partial def stripMData (e : Expr) : Expr :=
  e.replace fun
    | .mdata _ b => some (stripMData b)
    | _ => none

/-- What a C function of declaration `n` takes and returns, from Lean's
compiled (impure-phase) signature of `n`: its parameters that are not void
(the IO world), each with its borrow mark, and its result type. An extern's
C call passes no erased argument either (`keepErased := false`); an
`@[export]` function takes its erased parameters (`keepErased := true`). -/
def compiledSig? (n : Name) (keepErased : Bool) : CoreM (Option (Array (Expr × Bool) × Expr)) := do
  let some s ← getImpureSignature? n | return none
  let ps := s.params.filter fun p => !p.type.isVoid && (keepErased || !p.type.isErased)
  return some (ps.map fun p => (p.type, p.borrow), s.type)

/-- A compiled signature, for messages: `(@& obj, tobj) → tobj`. -/
def renderCompiledSig (ps : Array (Expr × Bool)) (r : Expr) : String :=
  let p := ps.toList.map fun (t, b) => (if b then "@& " else "") ++ toString t
  s!"({", ".intercalate p}) → {r}"

/-- Is the result type `fr` of the extern `g`'s result type `gr`, with the
identifications of `toMono` that make `g`'s value one of `fr`'s (applied to
`gr`, at its head, one after the other): a trivial structure is its single
relevant field (`{n : Nat // n = 32 ∨ n = 64}` is a `Nat`), `Decidable p` is
`Bool`. -/
partial def resultInstance (fr gr : Expr) (fuel : Nat := 8) : MetaM Bool := do
  if ← Meta.isDefEq fr gr then return true
  if fuel == 0 then return false
  let gr ← Meta.whnf gr
  if gr.getAppFn.constName? |>.any fun n => n == ``NonScalar || n == ``PNonScalar then return false
  match ← monoHeadStep gr.headBeta with
  | .ok (some u) => resultInstance fr u (fuel - 1)
  | _ => return false

/-- Is `fr` `gr`, parameter by parameter (definitionally), with `g`'s result
type identified as `resultInstance` allows? Identifications apply to the
result only: on a parameter they would let the extern pass a value that
breaks `g`'s invariant (`UInt32` is not `Char`: `0xD800` is no character). -/
partial def typeMatches (fr gr : Expr) : MetaM Bool := do
  if ← Meta.isDefEq fr gr then return true
  match ← Meta.whnf fr, ← Meta.whnf gr with
  | .forallE n d b bi, .forallE _ d' b' _ =>
    unless ← Meta.isDefEq d d' do return false
    Meta.withLocalDecl n bi d fun x => typeMatches (b.instantiate1 x) (b'.instantiate1 x)
  | .forallE .., _ | _, .forallE .. => return false
  | f', g' => resultInstance f' g'

/-- Test 1 of `bindingFailure?`: is `fty` an instance of `gty` (universe
parameters `gus`), at transparency `all`: `gty` with `g`'s universe
parameters instantiated as needed (`{α : Type}` is `{α : Type u}`), and its
result type identified as `toMono` does (`resultInstance`), its parameter
types not (`typeMatches`)? `g`'s implicit type parameters need no
instantiating: they would be erased parameters of `g`'s `@[export]`
function, which no extern's call passes, so test 2 would fail. Borrow marks
(metadata) are ignored. `.error` names why not. -/
def typeInstance (fty gty : Expr) (gus : List Name) : MetaM (Except String Unit) :=
    Meta.withTransparency .all do
  let fty := stripMData fty
  let gty := stripMData gty
  let same ← try
      (do
        let us ← gus.mapM fun _ => Meta.mkFreshLevelMVar
        typeMatches fty (gty.instantiateLevelParams gus us))
    catch _ => pure false
  if same then return .ok ()
  return .error s!"the type: `{fty}` is not an instance of `{gty}`"

/-- Why the binding of extern `f` of the program to the `@[export]`
definition `g` of its C symbol fails, or `.ok ()` if it holds. The binding
holds when two tests pass (a rule shared with another Lean translator built
on the same runtime):
1. One type: `f`'s type is an instance of `g`'s (`typeInstance`): `g`'s with
   its universe parameters instantiated is `f`'s, definitionally
   (transparency `all`), the borrow marks aside; `g`'s result type (only)
   may be identified as `toMono` does: a trivial structure is its single
   relevant field (`Nat → Nat` binds to an `@[export]` returning a
   `{m : Nat // m > 0}`), `Decidable p` is `Bool` (`resultInstance`).
2. One compiled signature, the condition under which native Lean's linked
   call is defined: the arguments `f`'s C call passes (not the IO world,
   not erased ones) are the parameters `g`'s C function takes (all but the
   IO world, erased ones included; `compiledSig?`), with equal types, and
   the two results have one type. Borrow marks must be equal too, except
   that an argument `f` passes owned may meet a parameter `g` borrows
   (natively a leak, no other effect); an `@&` on `f` where `g` takes the
   argument owned fails (natively `g` releases a reference the caller
   still holds). -/
def bindingFailure? (f g : Name) : CoreM (Except String Unit) := do
  let env ← getEnv
  let (some fi, some gi) := (env.find? f, env.find? g) | return .error s!"{g} is not a declaration"
  if let .error why ← (typeInstance fi.type gi.type gi.levelParams).run' {} {} then return .error why
  let some (fps, fr) ← compiledSig? f false | return .error s!"the compiled signature: Lean compiled no signature for {f}"
  let some (gps, gr) ← compiledSig? g true | return .error s!"the compiled signature: Lean compiled no signature for {g}"
  if fps.size != gps.size || fr != gr || (fps.zip gps).any (fun ((a, _), (b, _)) => a != b) then
    return .error s!"the compiled signature: {g}'s C function is `{renderCompiledSig gps gr}`, its call `{renderCompiledSig fps fr}`"
  for h : i in [:fps.size] do
    if fps[i].2 && !gps[i]!.2 then
      return .error s!"borrowed on the extern, owned on the target: it borrows (@&) argument {i + 1}, which {g} takes owned"
  return .ok ()

/-- `toDecl` for the Lean definition of extern `declName` (which `toDecl`
turns into an extern declaration): its definition, or its `_unsafe_rec`
version (recursive and `partial` definitions), as Lean's compiler compiles
it without the attribute (`ToDecl.toDecl`: `_unsafe_rec` names and
`@[csimp]` replacements, `macro_inline`, matchers). It is `noinline`: Lean's
passes in Stage 2 would otherwise evaluate calls of it on literals, which
natively, a C call, they never are (`Nat.shiftLeft 1 (2^64)` stopped
lean2rr, RV8E-11). An `opaque` declaration has no Lean definition (its
value only shows that its type is inhabited), nor has an axiom. -/
def externBodyDecl (declName : Name) : CompilerM (Decl .pure) := do
  let some info ← getDeclInfo? declName | throwError "it is not a declaration"
  match info with
  | .defnInfo _ => pure ()
  | .opaqueInfo _ =>
    throwError "it has no Lean definition (an `opaque` declaration, whose value only shows that its type is inhabited)"
  | .axiomInfo _ => throwError "it has no Lean definition (an axiom)"
  | _ => throwError "it has no Lean definition"
  let safe ← declIsNotUnsafe declName
  let some value := info.value? (allowOpaque := true) | throwError "it has no Lean definition"
  let (type, value) ← Meta.MetaM.run' do
    let type ← toLCNFType info.type
    let value ← Meta.lambdaTelescope value fun xs body => do Meta.mkLambdaFVars xs (← Meta.etaExpand body)
    -- `f._unsafe_rec` calls itself: calls of `f`; `@[csimp]` replacements.
    let value ← Core.transform value fun e => match e with
      | .const c us => return .done (← CSimp.replaceConstant (← getEnv) (.const ((isUnsafeRecName? c).getD c) us))
      | _ => return .continue
    let value ← macroInline value
    let value ← inlineMatchers value
    let value ← macroInline value
    return (type, value)
  let code ← toLCNF value type
  let decl ← if let .fun decl (.return _) := code then
      eraseFunDecl decl (recursive := false)
      pure ({ name := declName, params := decl.params, type, value := .code decl.value,
              levelParams := info.levelParams, safe, inlineAttr? := some .noinline } : Decl .pure)
    else
      pure { name := declName, params := #[], type, value := .code code, levelParams := info.levelParams,
             safe, inlineAttr? := some .noinline }
  decl.etaExpand

/-- How an extern names its C code, for messages: its symbol, or the kind
of its entry (`@[extern c inline "…"]`, `@[extern]`). -/
def externLabel (env : Environment) (n : Name) : String :=
  match getExternNameFor env `c n with
  | some sym => sym
  | none => match getExternAttrData? env n with
    | some d => if d.entries.any (· matches .inline ..) then "inline C" else "adhoc C"
    | none => "C"

/-- Compile extern `n`'s Lean definition (`externBodyDecl`) with
`recompilePasses`, as `recompile` does. `none` on success, otherwise why
not. -/
def compileExternBody (n : Name) : MonoM (Option String) := do
  if (← get).extraBase.contains n then return none
  let passes ← recompilePasses
  try
    let decls ← (do
        let d ← externBodyDecl n
        runPasses passes (markRecDecls #[d]) false : CompilerM _).run (phase := .base)
    let sym := externLabel (← getEnv) n
    modify fun s => { s with
      extraBase := decls.foldl (fun m d => m.insert d.name d) s.extraBase
      externBodies := s.externBodies.push (sym, n) }
    return none
  catch e =>
    let why ← e.toMessageData.toString
    -- `externBodyDecl`'s own reasons are complete sentences; Lean's
    -- compilation errors are not.
    return some (if why.startsWith "it " then why else s!"its Lean definition could not be compiled: {why}")

/-- The forwarding declaration of extern `f` of the program bound to the
`@[export]` definition `g` (`ExternRoute.export`): `f`'s parameters (from its
LCNF type, as `toDecl` takes an extern's), a call of `g` on them, and
`noinline`, as an extern's Lean definition (`externBodyDecl`). Calls of `f`
are not renamed to `g` in Stage 1: Stage 2's passes would then inline and
fold `g` on literal arguments, which natively, a C call, they never are
(review REB-01, the export form of RV8E-11). Test 1 leaves `g` no type
parameters, and test 2 none of `f`'s parameters erased. -/
def exportForwardDecl (f g : Name) : CompilerM (Decl .pure) := do
  let some info := (← getEnv).find? f | throwError "{f} is not a declaration"
  let some gi := (← getEnv).find? g | throwError "{g} is not a declaration"
  let type ← Meta.MetaM.run' (toLCNFType info.type)
  let mut params := #[]
  let mut ty := type
  repeat
    match ty with
    | .forallE n d b _ =>
      params := params.push (← mkParam n d false)
      ty := b
    | _ => break
  let args : Array (Arg .pure) := params.map fun p => if p.type.isErased then .erased else .fvar p.fvarId
  let r ← mkLetDecl `_r ty (.const g (gi.levelParams.map fun _ => Level.zero) args)
  return { name := f, levelParams := info.levelParams, type, params, value := .code (.let r (.return r.fvarId)),
           safe := true, inlineAttr? := some .noinline }

/-- Compile the forwarding declaration of extern `f` bound to `@[export]`
definition `g` (`exportForwardDecl`) with `recompilePasses`. `none` on
success, otherwise why not. -/
def compileExportForward (f g : Name) : MonoM (Option String) := do
  if (← get).extraBase.contains f then return none
  let passes ← recompilePasses
  try
    let decls ← (do runPasses passes #[← exportForwardDecl f g] false : CompilerM _).run (phase := .base)
    modify fun s => { s with extraBase := decls.foldl (fun m d => m.insert d.name d) s.extraBase }
    return none
  catch e => return some (← e.toMessageData.toString)

/-- How a refusal describes declaration `g` of Lean's library that the
refused extern's C symbol names (`what`: "that of" an extern, "the
`@[export]` of" a definition): a public one is to be called instead; a
private one (module system) is named by its user-facing name, with how a
program can call it (reviews REB-10, REB-12, REB-18). -/
def libraryDeclAdvice (g : Name) (what : String) : CoreM String := do
  let env ← getEnv
  if isPrivateName g then
    let m := match env.getModuleIdxFor? g with
      | some i => toString env.header.moduleNames[i.toNat]!
      | none => "?"
    return s!"{what} {(privateToUserName? g).getD g}, a private declaration of module {m} of \
      Lean's library, which a program can call only from a `module` file that imports it with \
      `import all {m}`, and to which lean2rr does not bind an extern of the program"
  return s!"{what} {g} of Lean's library, to which lean2rr does not bind an extern of the program: \
    call {g} instead"

/-- What native Lean runs for C symbol `sym` when it is a function of Lean's
library, for the note on an extern of the program that runs its Lean
definition instead: "Lean's library function" for the `@[export]` of a Lean
definition of Lean's library (`lean_string_drop`, `String.Internal.dropImpl`),
"Lean's runtime function" for the symbol of an extern of Lean's library,
imported or not (the source scan, `librarySourceExternSyms`, only for a
symbol the prelude defines: it is cached but reads Lean's whole source, so
it does not run for the program's own symbols; reviews REB-08, REB-13). -/
def nativeLibraryFunction? (sym : String) : MonoM (Option String) := do
  if let some g := (← exportMap).get? sym then
    if ← isToolchainDecl g then return some "Lean's library function"
  if (← toolchainExternSyms).contains sym then return some "Lean's runtime function"
  if (← get).config.preludeFns.contains sym then
    if (← librarySourceExternSyms).contains sym then return some "Lean's runtime function"
  return none

/-- The route of extern `n`, which is not of Lean's library (see the
section's introduction); its Lean definition, or its forwarding declaration
to an `@[export]` definition, is compiled here when that is the route.
Cached by `externRoute`. Where the route is its Lean definition although
its C symbol is another declaration's `@[export]` whose binding fails, the
failed tests are recorded for lean2rr's warning
(`MonoState.externBindingWarnings`; review REB-02). A refused extern whose
symbol is that of an extern of Lean's library gets the declaration to call
instead; when no imported module declares one but the runtime implements
the symbol, the module of Lean's library that does, to import
(`librarySourceExternSyms`; reviews REB-03, REB-07). -/
def computeExternRoute (n : Name) : MonoM ExternRoute := do
  let env ← getEnv
  if let some g := Compiler.getImplementedBy? env n then return .implementedBy g
  let sym? := getExternNameFor env `c n
  let mut failed : Array String := #[]
  if let some sym := sym? then
    -- Another declaration's `@[export]`, of the program's own (not of Lean's
    -- library, whose `@[export]`s an extern of the program is not bound to,
    -- as to Lean's runtime; review REB-14).
    if let some g := (← exportMap).get? sym then
      if g != n && !(← isToolchainDecl g) then
        match ← bindingFailure? n g with
        | .ok () =>
          match ← compileExportForward n g with
          | none => return .export g
          | some why => failed := failed.push s!"its C symbol {sym} is the @[export] of {g}, but the call of {g} could not be compiled: {why}"
        | .error why => failed := failed.push s!"its C symbol {sym} is the @[export] of {g}, but the binding fails {why}"
  match ← compileExternBody n with
  | none =>
    unless failed.isEmpty do
      modify fun s => { s with externBindingWarnings := s.externBindingWarnings.push (n, failed) }
    if let some sym := sym? then
      if let some what ← nativeLibraryFunction? sym then
        modify fun s => { s with externBodiesOfRuntime := s.externBodiesOfRuntime.insert n what }
    return .body
  | some why =>
    let some sym := sym? | return .refused ("; ".intercalate (why :: failed.toList))
    -- The symbol of an extern of Lean's library: lean2rr does not bind the
    -- program's extern to it, but says what to call.
    let lib := (← toolchainExternSyms).getD sym #[]
    if !lib.isEmpty then
      -- A private declaration (module system) is named by its user-facing
      -- name, with how a program can call it (`libraryDeclAdvice`).
      let (priv, pub) := lib.partition isPrivateName
      let mut parts := #[]
      unless pub.isEmpty do
        let names := " or ".intercalate (pub.toList.map toString)
        parts := parts.push s!"that of {names} of Lean's library, to which lean2rr does not bind an \
          extern of the program: call {names} instead"
      for g in priv do
        parts := parts.push (← libraryDeclAdvice g "that of")
      failed := failed.push s!"its C symbol {sym} is {" and ".intercalate parts.toList}"
    -- The `@[export]` of a Lean definition of Lean's library (natively the
    -- call runs it; an extern of the program is not bound to it, review
    -- REB-14).
    else if let some g ← (do
        match (← exportMap).get? sym with
        | some g => if ← isToolchainDecl g then pure (some g) else pure none
        | none => pure none : MonoM (Option Name)) then
      failed := failed.push s!"its C symbol {sym} is {← libraryDeclAdvice g "the @[export] of"}"
    -- A function of lean2rr's runtime whose declaration in Lean's library
    -- the program does not import (not a helper of lean2rr's prelude, such
    -- as `l2r_nat_repr` or `lean_natarr_push`, which no Lean module
    -- declares; review REB-07). `do` runs every `(← …)` of a condition
    -- before it, without `&&`'s short circuit, so the scan of Lean's source
    -- (`librarySourceExternSyms`) is nested: it runs only for such a
    -- refused extern (review REB-08).
    else if failed.isEmpty && (← get).config.preludeFns.contains sym && !(← exportMap).contains sym then
      if let some m := (← librarySourceExternSyms).get? sym then
        failed := failed.push s!"its C symbol {sym} is that of an extern of Lean's library declared in \
          module {m}, which the program does not import; if that declaration is public, import {m} \
          and call it instead"
    return .refused ("; ".intercalate (why :: failed.toList))

/-- `computeExternRoute`, once per extern. -/
def externRoute (n : Name) : MonoM ExternRoute := do
  if let some r := (← get).externRoutes.find? n then return r
  let r ← computeExternRoute n
  modify fun s => { s with externRoutes := s.externRoutes.insert n r }
  return r

/-- The base declaration to instantiate for `n`: one compiled by lean2rr,
or Lean's persisted one — unless that one is tainted by type-unsafe code, in
which case `n` is recompiled from source, or is an extern that is not of
Lean's library and runs its Lean definition (`externRoute`). -/
def baseDeclFor? (n : Name) : MonoM (Option (Decl .pure)) := do
  if let some d := (← get).extraBase.find? n then return some d
  let some d ← getBaseDecl? n | do
    -- A safe declaration with an `implemented_by` has no persisted body.
    if (← unsafeImplMap).toList.any (·.2 == n) then
      if ← recompile n then return (← get).extraBase.find? n
    return none
  if let .extern _ := d.value then
    unless ← isToolchainDecl n do
      match ← externRoute n with
      | .body | .export _ => return (← get).extraBase.find? n
      | .implementedBy _ | .refused _ => pure ()
    return some d
  if (← get).config.safeSources && (specOrigin? n).isNone then
    if ← isTainted d then
      if ← recompile n then return (← get).extraBase.find? n
  return some d

/-- The `IO.Error` builders of Lean's C runtime (exported Lean definitions),
numbered by the error kind the runtime's fallible primitives report (the
order of `decode_io_error`; see runtime/README.md). -/
def ioErrorBuilderSyms : Array String := #[
  "lean_mk_io_error_other_error", "lean_mk_io_error_interrupted",
  "lean_mk_io_error_invalid_argument", "lean_mk_io_error_invalid_argument_file",
  "lean_mk_io_error_no_file_or_directory", "lean_mk_io_error_permission_denied",
  "lean_mk_io_error_permission_denied_file", "lean_mk_io_error_resource_exhausted",
  "lean_mk_io_error_resource_exhausted_file", "lean_mk_io_error_inappropriate_type",
  "lean_mk_io_error_inappropriate_type_file", "lean_mk_io_error_no_such_thing",
  "lean_mk_io_error_no_such_thing_file", "lean_mk_io_error_already_exists",
  "lean_mk_io_error_already_exists_file", "lean_mk_io_error_hardware_fault",
  "lean_mk_io_error_unsatisfied_constraints", "lean_mk_io_error_illegal_operation",
  "lean_mk_io_error_resource_vanished", "lean_mk_io_error_protocol_error",
  "lean_mk_io_error_time_expired", "lean_mk_io_error_resource_busy",
  "lean_mk_io_error_unsupported_operation", "lean_mk_io_user_error"]

/-- Is `sym` a fallible IO primitive whose errors the runtime reports
through its last-error protocol? -/
def isFallibleIOSym (sym : String) : Bool :=
  (sym.startsWith "lean_io_prim_handle_" &&
    sym ∉ ["lean_io_prim_handle_is_tty", "lean_io_prim_handle_is_eof"]) ||
  sym ∈ ["lean_io_remove_file", "lean_io_create_dir", "lean_io_remove_dir", "lean_io_rename",
         "lean_io_hard_link", "lean_io_realpath", "lean_io_read_dir", "lean_io_metadata",
         "lean_io_symlink_metadata", "lean_chmod", "lean_io_create_tempfile",
         "lean_io_create_tempdir", "lean_io_current_dir", "lean_io_app_path",
         "lean_io_process_get_current_dir", "lean_io_process_set_current_dir",
         "lean_io_get_random_bytes"] ||
  -- The standard streams' operations (their glue is generated with the
  -- `IO.FS.Stream` values) report errors the same way.
  sym ∈ ["lean_get_stdout", "lean_get_stderr", "lean_get_stdin"]

/-- The child-process externs that can fail. Their glue (Lower's "Child
processes") reports errors through the runtime's last-error protocol too. -/
def processIOSyms : Array String :=
  #["lean_io_process_spawn", "lean_io_process_child_wait", "lean_io_process_child_try_wait",
    "lean_io_process_child_kill"]

/-- A fallible IO extern needs the `IO.Error` builders: instantiate them. -/
def ensureIOErrorBuilders (f : Name) : MonoM Unit := do
  let some sym := getExternNameFor (← getEnv) `c f | return
  unless isFallibleIOSym sym || processIOSyms.contains sym do return
  for b in ioErrorBuilderSyms do
    if let some d := (← exportMap).get? b then
      discard <| instanceName { decl := d, typeArgs := #[] }

/-- Redirect a call target: an extern implemented by an exported Lean
definition becomes that definition, as does a definition lean2rr's shim
replaces; with `safeSources`, a type-unsafe
implementation becomes the safe declaration it implements. -/
def redirectTarget (f : Name) : MonoM Name := do
  -- A definition the shim replaces (`L2RShim`, exported as
  -- `l2r_override_<f mangled>`) is that definition.
  if let some d := (← exportMap).get? (f.mangle "l2r_override_") then
    if d != f then return d
  -- An extern of Lean's library whose C symbol is provided by an
  -- `@[export]` Lean definition is that definition (Lean's runtime calls
  -- it; we compile it). An extern of the program follows its route: its
  -- `@[implemented_by]` target, or the `@[export]` definition its C symbol
  -- binds to (`externRoute`).
  if isExtern (← getEnv) f then
    if ← isToolchainDecl f then
      if let some sym := getExternNameFor (← getEnv) `c f then
        if let some d := (← exportMap).get? sym then
          if d != f then return d
    else match ← externRoute f with
      | .implementedBy g => return g
      | _ => pure ()
  if !(← get).config.safeSources then return f
  if ← isTypeUnsafeImpl f then
    if let some safe := (← unsafeImplMap).find? f then
      if ← recompile safe then return safe
  return f

/-- Positions of type-former parameters. -/
def typeParamPositions (decl : Decl .pure) : Array Nat := Id.run do
  let mut out := #[]
  for h : i in [:decl.params.size] do
    if isTypeFormerType decl.params[i].type then out := out.push i
  return out

/-- Is parameter `i` of `decl` a type (not a type former or a proposition)
that shows in no later parameter's type and not in the result type (its
LCNF type)? Then
every instance of `decl` has one type whatever the argument: `len {α}
(b : Bool) (v : if b then List α else Unit) : Nat` is
`Bool → lcAny → Nat` at every `α`. -/
def typeParamHidden (decl : Decl .pure) (i : Nat) : Bool := Id.run do
  -- A type: of kind `Sort u`, but not `Prop` (a proposition is erased).
  let isType (p : Param .pure) : Bool := match p.type with
    | .sort u => !u.isZero
    | _ => false
  unless decl.params[i]?.any isType do return false
  let mut t := decl.type
  for _ in [:i] do
    let .forallE _ _ b _ := t | return false
    t := b
  let .forallE _ _ b _ := t | return false
  return !b.hasLooseBVar 0

/-! ## Static dictionaries

A type-class dictionary is *static* when it is built from instance constants
and types only. Like Lean's specializer, lean2rr specializes a callee on the
static dictionaries passed to it: the callee's instance binds the parameter
to the dictionary itself, so Lean's `simp` folds its projections into direct
calls (`inlineProjInst?` folds let-bound dictionaries only). A static
dictionary is encoded as an `Expr`: `c a₁ … aₙ` for an instance application,
where a type argument `t` is `L2R.tyArg t` and an erased one is `◾`, or
`.proj S i d` for a projection. -/

def tyArgMarker : Expr := .const `L2R.tyArg []

/-- Does evaluating the constant `c` (a declaration without parameters) do
more than build a dictionary of functions? That is: call a function
(`instance : Inhabited Grid := ⟨mkGrid 300⟩`), or allocate data: a
constructor of a type that is not a class, with a relevant field (a list
or a record literal, a `Thunk.mk`), a string literal, a number past the
small ones. A class's own constructor (the dictionary and its parent
dictionaries), a closure, a constructor without relevant fields (`[]`,
`none`) and a small number are values. Natively such a constant is
evaluated once, at startup, and a callee that receives it reads its
fields; in a callee specialized on it, `simp` copies the body to the
projections (`inlineProjInst?`), to run at every call: a call runs again, a
literal is rebuilt, a thunk is made and forced again (round 7 RV7F-02,
RV7F-04). Only a dictionary of functions gains from being copied: its
methods become direct calls. `fuel` bounds the constants followed. -/
partial def constComputes (c : Name) (fuel : Nat := 8) : MonoM Bool := do
  if fuel == 0 then return true
  let some decl ← baseDeclFor? c | return false
  unless decl.params.isEmpty do return false
  let .code code := decl.value | return false
  go code fuel
where
  go (code : Code .pure) (fuel : Nat) : MonoM Bool := do
    match code with
    | .let d k =>
      let computes ← match d.value with
        | .erased | .proj .. => pure false
        | .lit (.str _) => pure true
        | .lit (.nat n) => pure (n ≥ 2 ^ 63)
        | .lit _ => pure false
        | .fvar _ args => pure !args.isEmpty
        | .const f _ args _ =>
          if let some (.ctorInfo ci) := (← getEnv).find? f then
            pure (!isClass (← getEnv) ci.induct &&
              args[ci.numParams:].any (· matches .fvar _))
          else if args.isEmpty then constComputes f (fuel - 1)
          else match ← baseDeclFor? f with
            -- A partial application: a closure.
            | some kd => pure (args.size ≥ kd.params.size)
            | none => pure true
      if computes then return true
      go k fuel
    -- A local function is a value: its body runs when it is called.
    | .fun _ k _ => go k fuel
    | .return _ => return false
    | _ => return true

/-- The static dictionary a `let` value denotes, given the static
dictionaries of variables in scope. A constant that is more than a
dictionary of functions (`constComputes`) is not part of a static
dictionary: the callee reads it at run time, as natively. -/
def staticDict? (statics : Std.HashMap FVarId Expr) (v : LetValue .pure) (ty : Expr) : MonoM (Option Expr) := do
  unless (← isClass? ty).isSome do return none
  match v with
  | .const c _ args _ =>
    if args.isEmpty then
      if ← constComputes c then return none
    let mut out := #[]
    for a in args do
      match a with
      | .type t _ =>
        let t ← normTypeArg t
        if t == anyExpr then return none
        out := out.push (mkApp tyArgMarker t)
      | .erased => out := out.push erasedExpr
      | .fvar x =>
        match statics[x]? with
        | some e => out := out.push e
        | none => return none
    let e := mkAppN (.const c []) out
    -- Bounded like type arguments (polymorphic recursion builds ever
    -- larger dictionaries).
    if e.approxDepth.toNat > (← get).config.maxTypeArgSize then return none
    return some e
  | .proj sn i x _ =>
    match statics[x]? with
    | some e => return some (.proj sn i e)
    | none => return none
  | _ => return none

/-- Rebuild a static dictionary as a chain of `let`s (registered in the local
context); returns the variable holding it. -/
partial def dictLets (e : Expr) : StateT (Array (LetDecl .pure)) CompilerM FVarId := do
  let value ← match e with
    | .proj sn i b => pure (LetValue.proj sn i (← dictLets b))
    | _ =>
      let .const c _ := e.getAppFn | throwError "lean2rr: malformed static dictionary"
      let args ← e.getAppArgs.mapM fun a => do
        if a.isAppOf `L2R.tyArg then return Arg.type a.appArg!
        else if a.isErased then return Arg.erased
        else return Arg.fvar (← dictLets a)
      pure (LetValue.const c [] args)
  let ty ← value.inferType
  let fvarId ← mkFreshFVarId
  let d : LetDecl .pure := { fvarId, binderName := `_dict, type := ty, value }
  modifyLCtx (·.addLetDecl d)
  modify (·.push d)
  return fvarId

/-- Positions of class-typed (instance) parameters. -/
def classParamPositions (decl : Decl .pure) : MonoM (Array Nat) := do
  let mut out := #[]
  for h : i in [:decl.params.size] do
    if (← isClass? decl.params[i].type).isSome then out := out.push i
  return out

/-- Redirect a constant application to the instance of its callee. Returns
`none` when the constant is not a declaration we instantiate (constructors,
monomorphic externs). -/
def renameApp (statics : Std.HashMap FVarId Expr) (f : Name) (args : Array (Arg .pure)) :
    MonoM (Option (Name × Array (Arg .pure))) := do
  -- A constant defined by `initialize c : T ← act` has no code: its value
  -- is the result of `act`, run at startup (Stage 4 reads it from a
  -- once-cell). `act` becomes a root.
  if let some initFn := getInitFnNameFor? (← getEnv) f then
    unless (← get).initConsts.any (·.1 == f) do
      discard <| instanceName { decl := initFn, typeArgs := #[] }
      modify fun s => { s with initConsts := s.initConsts.push (f, initFn) }
    return none
  -- Declarations that Lean's mono passes recognise by name keep it:
  -- `toMono` replaces `Decidable.decide` by its argument, which folds the
  -- `if` on it and so the closed terms (an instance under a new name
  -- survives as a call).
  if f == ``Decidable.decide then return none
  let f0 := f
  let f ← redirectTarget f
  if isExtern (← getEnv) f then ensureIOErrorBuilders f
  let some callee ← baseDeclFor? f | return none
  let positions := typeParamPositions callee
  if let .extern _ := callee.value then
    if positions.isEmpty then
      modify fun s => { s with monoExterns := s.monoExterns.insert f }
      -- A redirected call (an extern of the program whose
      -- `@[implemented_by]` target is an extern) calls that extern under
      -- its own name.
      return if f != f0 then some (f, args) else none
  let mut typeArgs := #[]
  let isExternCallee := callee.value matches .extern _
  for i in positions do
    -- A type that shows nowhere in the callee's type: `lcAny`, so that every
    -- call of it, at any type, calls one instance, as natively one function
    -- whose calls and closed terms Lean merges by value and type.
    if !isExternCallee && typeParamHidden callee i then
      if (← IO.getEnv "L2R_DEBUG_HIDDEN").isSome then IO.eprintln s!"lean2rr: hidden type parameter {i} of {f}"
      typeArgs := typeArgs.push anyExpr
      continue
    match args[i]? with
    | some (.type e _) =>
      let t ← normTypeArg e
      -- A type whose values are types (`Type`, `Type → Type`, `Prop`):
      -- natively a parameter whose type is the type parameter stays data
      -- (`x : α` is `lcAny`, given `box(0)`), but at `t` it would be a type
      -- parameter, erased, and Lean's `cse` would merge `f x` and `f y`. The
      -- uniform instance keeps it data.
      typeArgs := typeArgs.push (if !isExternCallee && isTypeFormerType t then anyExpr else t)
    -- A type that is a variable here (taken out of an existential package,
    -- or a type parameter Lean's specializer turned into a value) is not
    -- statically known: the uniform instance.
    | some _ => typeArgs := typeArgs.push anyExpr
    -- A partial application that stops before a type parameter: that
    -- parameter is kept (see `instantiate`), so it has no argument here.
    | none => typeArgs := typeArgs.push anyExpr
  let mut found : Array (Option Expr) := #[]
  for i in ← classParamPositions callee do
    found := found.push <| match args[i]? with
      | some (.fvar x) => statics[x]?
      | _ => none
  let dicts := if found.any Option.isSome then found else #[]
  let n ← instanceName { decl := f, typeArgs, dicts }
  -- Type arguments stay (as erased arguments): instances keep Lean's arity.
  let args := args.zipIdx.map fun (a, i) => if positions.contains i then .erased else a
  return some (n, args)

partial def renameCode (statics : Std.HashMap FVarId Expr) : Code .pure → MonoM (Code .pure)
  | .let d k => do
    let statics := match ← staticDict? statics d.value d.type with
      | some e => statics.insert d.fvarId e
      | none => statics
    let d ← match d.value with
      | .const f us args _ =>
        match ← renameApp statics f args with
        | some (n, args') =>
          -- A monomorphic extern keeps its own name, and so its universes.
          let us := if (← get).monoExterns.contains n then us else []
          pure { d with value := .const n us args' }
        | none => pure d
      | _ => pure d
    return .let d (← renameCode statics k)
  | .fun d k _ => do
    let value ← renameCode statics d.value
    return .fun (FunDecl.mk d.fvarId d.binderName d.params d.type value) (← renameCode statics k)
  | .jp d k => do
    let value ← renameCode statics d.value
    return .jp (FunDecl.mk d.fvarId d.binderName d.params d.type value) (← renameCode statics k)
  | .cases c => do
    let alts ← c.alts.mapM fun alt => do
      match alt with
      | .alt ctor ps code _ => return .alt ctor ps (← renameCode statics code)
      | .default code => return .default (← renameCode statics code)
      | other => return other
    return .cases ⟨c.typeName, c.resultType, c.discr, alts⟩
  | code => return code

/-- Build the instance of `decl` at `typeArgs` like Lean's `mkSpecDecl`:
instantiate universe levels (at `0`) and type parameters, and internalize.
Type parameters are kept as erased parameters, so arities are Lean's. -/
def instantiate (decl : Decl .pure) (name : Name) (typeArgs : Array Expr) (keepMissing : Bool)
    (classPositions : Array Nat := #[]) (dicts : Array (Option Expr) := #[]) :
    CompilerM (Decl .pure) := do
  let us := decl.levelParams.map fun _ => Level.zero
  let positions := typeParamPositions decl
  -- Static dictionaries are rebuilt as `let`s; their parameters stay (unused).
  let mut dictSubst : FVarSubst .pure := {}
  let mut dictDecls : Array (LetDecl .pure) := #[]
  for h : j in [:dicts.size] do
    if let some e := dicts[j] then
      if let some i := classPositions[j]? then
        let (fv, ds) ← (dictLets e).run dictDecls
        dictDecls := ds
        dictSubst := dictSubst.insert decl.params[i]!.fvarId (.fvar fv)
  -- Returns the kept (internalized) parameters and, per original parameter,
  -- the expression it is instantiated with (for the result type).
  let go : Internalize.InternalizeM .pure (Array (Param .pure) × Array Expr) := do
    let mut kept := #[]
    let mut instArgs := #[]
    for h : i in [:decl.params.size] do
      let p := decl.params[i]
      let p := { p with type := eraseLevels (p.type.instantiateLevelParamsNoCache decl.levelParams us) }
      match positions.idxOf? i with
      | some j =>
        -- The parameter is substituted in the body but kept, with an
        -- erased type, so that the instance has exactly Lean's arity (a
        -- polymorphic function must not become a constant, which Lean
        -- would evaluate at startup; cf. ReduceArity).
        let t := typeArgs[j]!
        let p' ← Internalize.internalizeParam { p with type := erasedExpr }
        kept := kept.push p'
        modify fun s => s.insert p.fvarId (if t.isErased then .erased else .type t)
        instArgs := instArgs.push t
      | none =>
        let p' ← Internalize.internalizeParam p
        kept := kept.push p'
        instArgs := instArgs.push (.fvar p'.fvarId)
        -- A parameter fixed to a static dictionary: the body uses the
        -- dictionary's `let` instead (the parameter remains, unused).
        if let some d := dictSubst[p.fvarId]? then
          modify fun s => s.insert p.fvarId d
    return (kept, instArgs)
  let code := match decl.value with
    | .code c => c.instantiateValueLevelParams decl.levelParams us
    | .extern _ => .return default
  let ((params, args), value) ← (do
      let r ← go
      let v ← match decl.value with
        | .code _ =>
          let c ← Internalize.internalizeCode code
          pure (DeclValue.code (dictDecls.foldr (fun d c => .let d c) c))
        | .extern e => pure (DeclValue.extern e)
      return (r, v) : Internalize.InternalizeM .pure _).run' {}
  let declType := eraseLevels (decl.type.instantiateLevelParamsNoCache decl.levelParams us)
  let retType ← Core.betaReduce (← instantiateForall declType args)
  let type ← mkForallParams params retType
  return { decl with name, levelParams := [], params, type, value, inlineAttr? := decl.inlineAttr? }

/-- Build an extern instance. Extern declarations have no body, and their
parameter list is not in internalized form, so the instance signature is
built from the declaration's type instead: type-former binders are
instantiated, the others become fresh parameters (borrow annotations are
dropped: Reussir's ownership analysis decides borrowing). -/
def instantiateExtern (decl : Decl .pure) (name : Name) (typeArgs : Array Expr) :
    CompilerM (Decl .pure) := do
  let us := decl.levelParams.map fun _ => Level.zero
  let positions := typeParamPositions decl
  let mut ty := eraseLevels (decl.type.instantiateLevelParamsNoCache decl.levelParams us)
  let mut params : Array (Param .pure) := #[]
  for h : i in [:decl.params.size] do
    let .forallE n d b _ := ty.headBeta
      | throwError "lean2rr: extern {decl.name} has fewer binders than parameters"
    let d := d.consumeMData
    match positions.idxOf? i with
    | some j =>
      -- kept as an erased parameter (Lean's arity); not passed to C
      let t := typeArgs[j]!
      let p ← mkParam n erasedExpr false
      params := params.push p
      ty := b.instantiate1 t
    | none =>
      let p ← mkParam n (← Core.betaReduce d) false
      params := params.push p
      ty := b.instantiate1 (.fvar p.fvarId)
  let retType ← Core.betaReduce ty
  let type ← mkForallParams params retType
  return { decl with name, levelParams := [], params, type }

/-! ## Uniform-representation code

A few library functions rely on Lean's uniform object representation:
`Array.mapMUnsafe` reinterprets an `Array α` as an `Array NonScalar`,
replaces its elements one by one with values of another type, and casts the
result to `Array β`. Such code is inlined and specialized into user code, so
it is part of the persisted LCNF. lean2rr gives it the uniform
representation it assumes: `NonScalar` and `PNonScalar` (types that stand
for "any object") become `lcAny`, i.e. `Box`; the casts become the
representation conversions of Stage 4 (element-wise for arrays), and
`NonScalar.mk`/`PNonScalar.mk` (only used to build the `box(0)`
placeholder) become `◾`. -/

def isUniformConst (n : Name) : Bool := n == ``NonScalar || n == ``PNonScalar

def uniformTy (e : Expr) : Expr :=
  if e.find? (fun e => e.isConst && isUniformConst e.constName!) |>.isNone then e
  else e.replace fun e => if e.isConst && isUniformConst e.constName! then some anyExpr else none

def uniformParamTy (p : Param .pure) : Param .pure := { p with type := uniformTy p.type }

partial def uniformCode : Code .pure → Code .pure
  | .let d k =>
    let value : LetValue .pure := match d.value with
      | .const c _ _ _ =>
        if c == ``NonScalar.mk || c == ``PNonScalar.mk then .erased else d.value
      | v => v
    let value : LetValue .pure := match value with
      | .const c us args h => .const c us (args.map fun (a : Arg .pure) => match a with
          | .type t _ => .type (uniformTy t)
          | a => a) h
      | v => v
    .let { d with type := uniformTy d.type, value } (uniformCode k)
  | .fun d k _ => .fun (uniformFun d) (uniformCode k)
  | .jp d k => .jp (uniformFun d) (uniformCode k)
  | .cases c =>
    let alts := c.alts.map fun
      | .alt ctor ps code _ => .alt ctor (ps.map uniformParamTy) (uniformCode code)
      | .default code => .default (uniformCode code)
      | other => other
    .cases ⟨c.typeName, uniformTy c.resultType, c.discr, alts⟩
  | code => code
where
  uniformFun (d : FunDecl .pure) : FunDecl .pure :=
    FunDecl.mk d.fvarId d.binderName (d.params.map uniformParamTy) (uniformTy d.type) (uniformCode d.value)

def uniformDecl (d : Decl .pure) : Decl .pure :=
  let value := match d.value with
    | .code c => .code (uniformCode c)
    | v => v
  { d with type := uniformTy d.type, params := d.params.map uniformParamTy, value }

/-! ## Calls that Lean's CSE merges after erasure

Lean's mono-phase `cse` (`Code.cse`) keys a `let` on its mono value, in
which type arguments are erased, so a call of a declaration is merged into
an earlier call of it whose value arguments agree, even at other type
arguments (`gp xs none` used as an `Option String` and later as an
`Option (Nat → Nat)`): the call runs once, and the merged variable keeps the
first call's type. Stage 1 gives the two calls instances at different types,
under different names, so both would run, and a panic or trace in them
would come out twice. So Stage 1 gives the calls of such a group one
instance and the same arguments, and Stage 2's `cse` (Lean's) merges them
as natively. A use of the merged value at another type converts it (§5.1:
a box, an unbox, or a wrapper of a function value).

An instance at concrete types reads its inputs at those types: `fst@Nat`
unboxes a list element as a `Nat`. A value that exists at two types holds
nothing where the types differ (`none`, `[]`; nothing is both a `String`
and a function), except a function: one closure at two function types
natively (`id` as `Nat → Nat` and as `String → String`). The instance's
closure, used at the other type, gets inputs of that type. So the instance
is chosen as follows (`erasedMerges`):
1. The earlier call's, when its value serves every later use (`serves`):
   each function value in it has the same domain at both types, and no
   `lcAny` hides a difference of the type arguments. The later calls get
   the earlier call's type and value arguments, and the merged value keeps
   its type, as natively.
2. Else the instance at `lcAny` for each type argument that differs, for
   every call of the group, the earlier one too (`uniformArgs`). This is
   the uniform code that native Lean runs: its closures take boxes, so
   they serve both uses through wrappers. The calls get the earlier call's
   value arguments; one that replaces another variable must serve at that
   variable's type, since the uniform code can return it, unless both are
   calls of one group at `lcAny`. A type-former argument that differs
   prevents this. So does a closed group (a closed term, which Lean's
   closed-term cache shares with the same call at the same type in other
   functions), unless the earlier call keeps its instance or the base test
   aligned it (`erasedMerges`).
3. Else only the later calls of 1 are aligned. The others are left as they
   are and run apart (plan §10, "Merging after erasure").

A type parameter that shows nowhere in a declaration's type
(`typeParamHidden`) gets `lcAny` at every call (`renameApp`): every
instance would have the same type, and natively one closed term serves the
calls at every type. -/

/-- Runtime objects whose contents are not fields that `serves` follows
(a task, a thunk, a reference, a promise): two instantiations of one of them
do not serve each other. -/
def opaqueTypes : List Name := [``Task, ``Thunk, ``ST.Ref, ``IO.Promise]

/-- The field types of the constructors of inductive `iv` at arguments
`args`, as in base LCNF (dependent fields at `lcAny`). -/
def ctorFieldTypesAt (iv : InductiveVal) (args : Array Expr) : CoreM (Array (Array Expr)) := do
  iv.ctors.toArray.mapM fun ctor => do
    let mut ty ← instantiateForall (← getOtherDeclBaseType ctor []) args[:iv.numParams].toArray
    let mut out := #[]
    repeat
      match ty.headBeta with
      | .forallE _ d b _ => out := out.push d; ty := b.instantiate1 anyExpr
      | _ => break
    return out

/-- Is the head of `t` (after `monoHead`) an inductive type? -/
def inductiveHead (t : Expr) : CoreM Bool := do
  let .const n _ := t.getAppFn | return false
  return (← getEnv).find? n matches some (.inductInfo _)

/-- Does type `t` mention `lcAny` (or `NonScalar`)? Behind it, a type
argument of the call can hide (`if b then List α else Unit` is `lcAny`). -/
def mentionsAny (t : Expr) : Bool :=
  (t.find? fun e => e.isConstOf ``lcAny || (e.isConst && isUniformConst e.constName!)).isSome

/-- Builtin types without parameters whose representation is a scalar or
plain data, although a field is opaque to Lean (`Float`'s
`floatSpec.float`). -/
def atomicDataTypes : List Name := [``Float, ``Float32]

/-- Can a value of type `t` hold only data: no function (also behind a
trivial structure), no runtime object, nothing unclassified? Inductives are
followed into their fields (`seen` stops at types already followed); `lcAny`
is taken to hold data. Only the base test (`serves` with `strict := false`)
uses it. -/
partial def firstOrderData (t : Expr) : StateT (Std.HashSet (Expr × Expr)) CoreM Bool := do
  let some t ← monoHead t | return false
  if t == anyExpr || t.isErased then return true
  if (← get).contains (t, t) then return true
  modify (·.insert (t, t))
  let .const n _ := t.getAppFn | return false
  let args := t.getAppArgs
  if opaqueTypes.contains n then return false
  if atomicDataTypes.contains n then return true
  match (← getEnv).find? n with
  | some (.inductInfo iv) =>
    if args.any (·.isLambda) then return false
    for fs in ← ctorFieldTypesAt iv args do
      for f in fs do
        unless ← firstOrderData f do return false
    return true
  | _ => return false

/-- Does a value of type `a`, made by the instance at the earlier call's
type arguments, serve a use at type `b`, the type of a later call or
argument? The types are compared as `toMono` sees them (`monoHead` at every
level) and walked in parallel:
- equal types serve, unless they mention `lcAny` (`mentionsAny`);
- an erased type serves: it holds no data;
- `lcAny` and another type do not: the box can hold a function;
- two function types serve when their domains are equal and do not mention
  `lcAny` (the instance reads its inputs at its own types) and their
  codomains serve as codomains (`cod`, below);
- a function type and an inductive type, or two different inductive types,
  serve: no value has both types (the values were found equal on
  constructor names); but not as codomains (`cod`): a closure exists at both
  function types, and it is converted when it is used, which needs a
  conversion of its results;
- two instantiations of one inductive serve when only parameters differ, no
  differing parameter is a type former or shows in no field, the inductive
  is not a runtime object (`opaqueTypes`), and their fields serve (one
  layout per inductive: fields are not converted; `seen` stops at pairs
  already compared);
- anything else does not.

With `strict := false`, the test that Stage 1 made before the review of the
dependent-type work (*the base test*): `lcAny` is taken to hide nothing
(equal types serve; `lcAny` and a type that holds only data serve,
`firstOrderData`), and two function types that differ do not serve. It
decides only whether a closed group may take the instance at `lcAny`
(`erasedMerges`). -/
partial def serves (a b : Expr) (cod : Bool := false) (strict : Bool := true) :
    StateT (Std.HashSet (Expr × Expr)) CoreM Bool := do
  let some a ← monoHead a | return false
  let some b ← monoHead b | return false
  if a == b then return !strict || !mentionsAny a
  if a.isErased || b.isErased then return true
  if a == anyExpr || b == anyExpr then
    return !strict && (← firstOrderData (if a == anyExpr then b else a))
  unless cod do
    if (← get).contains (a, b) then return true
    modify (·.insert (a, b))
  match a, b with
  | .forallE _ da ca _, .forallE _ db cb _ =>
    if !strict || ca.hasLooseBVars || cb.hasLooseBVars then return false
    let some da ← monoHead da | return false
    let some db ← monoHead db | return false
    if da != db || mentionsAny da then return false
    serves ca cb (cod := true)
  -- Nothing is both a closure and a value of an inductive type.
  | .forallE .., _ => return !cod && (← inductiveHead b)
  | _, .forallE .. => return !cod && (← inductiveHead a)
  | _, _ =>
    let (.const n _, .const m _) := (a.getAppFn, b.getAppFn) | return false
    let some (.inductInfo iv) := (← getEnv).find? n | return false
    unless ← inductiveHead b do return false
    -- Values of two different inductive types: nothing has both types.
    if n != m then return !cod
    let as := a.getAppArgs
    let bs := b.getAppArgs
    if as.size != bs.size || opaqueTypes.contains n then return false
    for i in [:as.size] do
      if as[i]! != bs[i]! && (i ≥ iv.numParams || as[i]!.isLambda || bs[i]!.isLambda) then
        return false
    let fas ← ctorFieldTypesAt iv as
    let fbs ← ctorFieldTypesAt iv bs
    for (fa, fb) in fas.zip fbs do
      for (x, y) in fa.zip fb do
        unless ← serves x y (strict := strict) do return false
    -- A parameter that differs but shows in no field classifies contents the
    -- fields do not hold: unclassified.
    for i in [:iv.numParams] do
      if as[i]! != bs[i]! then
        let fis ← ctorFieldTypesAt iv (as.set! i bs[i]!)
        if fis == fas then return false
    return true

/-- The arguments of the calls of `f` in one group (`args₀`, the earlier
call's, and `others`, the later calls') at the instance at `lcAny` for every
type argument in which they differ, with the earlier call's value arguments.
`none` when a type argument that differs is not a type (a type former, by
the kind of `f`'s parameter), or when a value argument of the earlier call
replaces another variable that it does not serve at that variable's type
(`serves`). Two calls of one group that took the instance at `lcAny`
(`uniformOf`: each call's earlier call) serve each other: the uniform value
serves at the type of each call of its group. -/
def uniformArgs (f : Name) (args₀ : Array (Arg .pure)) (others : Array (Array (Arg .pure)))
    (uniformOf : Std.HashMap FVarId FVarId) : CompilerM (Option (Array (Arg .pure))) := do
  -- The binder kinds of `f`: its base declaration's parameters (a
  -- specialization Lean made has no kernel constant), else its type.
  let kinds : Array Expr ← do
    if let some d ← getBaseDecl? f then pure (d.params.map (·.type))
    else if (← getEnv).contains f then pure (getParamTypes (← getOtherDeclBaseType f []))
    else pure #[]
  let mut out := #[]
  for h : i in [:args₀.size] do
    let a₀ := args₀[i]
    let kind? := kinds[i]?
    let as := others.map (·[i]!)
    if as.all (· == a₀) then
      out := out.push a₀
      continue
    match a₀ with
    | .type _ _ =>
      unless kind? matches some (.sort _) && as.all (· matches .type ..) do return none
      out := out.push (.type anyExpr)
    | .fvar x =>
      for a in as do
        let .fvar y := a | return none
        if x != y then
          let together := match uniformOf[x]?, uniformOf[y]? with
            | some g, some g' => g == g'
            | _, _ => false
          unless together || (← (serves (← getType x) (← getType y)).run' {}) do return none
      out := out.push a₀
    | _ => return none
  return some out

/-- Does the earlier call keep its instance with arguments `args` instead of
`args₀`: does every type argument they change show nowhere in `f`'s type
(`typeParamHidden`), so that `renameApp` gives both the instance at `lcAny`? -/
def keepsInstance (f : Name) (args₀ args : Array (Arg .pure)) : CoreM Bool := do
  let some d ← getBaseDecl? f | return false
  for h : i in [:args₀.size] do
    if args₀[i] != args[i]! && !typeParamHidden d i then return false
  return true

/-- What `erasedMerges` collects in one instance's code. -/
structure MergeScan where
  /-- The variable each merged variable stands for. -/
  reps : Std.HashMap FVarId FVarId := {}
  /-- The variables merged into each representative. -/
  groups : Std.HashMap FVarId (Array FVarId) := {}
  /-- The calls of definitions, with their binder types. -/
  calls : Std.HashMap FVarId (Name × List Level × Array (Arg .pure) × Expr) := {}
  /-- The binders of `calls`, in program order. -/
  order : Array FVarId := #[]
  /-- The `let`s whose values use no variable but such `let`s: closed terms,
  which Lean's closed-term extraction may share with other functions. -/
  closed : Std.HashSet FVarId := {}

/-- The calls of `code` that Lean's mono-phase `cse` merges into an earlier
call of the same declaration at other type arguments, each with the
universe levels and arguments it gets: the earlier call's, or the ones of
the instance at `lcAny` (`uniformArgs`), which the earlier call then gets
too (see the section's comment). A closed group (the earlier call is a
closed term) takes the instance at `lcAny` only when the earlier call keeps
its instance (`keepsInstance`) or when the base test (`serves` with
`strict := false`) serves every later call: Lean's closed-term cache
compares values and types, so natively the merged call shares the closed
term of the same call at the earlier call's types in other functions, which
the base kept by aligning to the earlier call's instance or by running the
calls apart; the instance at `lcAny` would be a closed term of its own.
Groups are decided in program order, so that an argument's group is decided
before the group of its call. The grouping follows `Code.cse` on mono code:
values are compared with type arguments erased, variables replaced by the
variable they were merged into, and a trivial structure (`Subtype`, `Fin`)
taken for its field and `Decidable` for `Bool`, as `toMono` does; a `let` is
merged into one in scope (`cases` alternatives start a nested scope, join
points see the enclosing scope, and a local function's body only its own:
Lean's `cse` runs after lambda lifting), and `@[never_extract]` calls are
not merged. Only calls of definitions count: Stage 1 does not rename
constructors (Stage 2's `cse` merges them as natively), and extern instances
and instances (dictionary builders) compute nothing observable. -/
partial def erasedMerges (code : Code .pure) :
    CompilerM (Std.HashMap FVarId (List Level × Array (Arg .pure))) := do
  let ((), scan) ← (go code {}).run {}
  let typeArgs (as : Array (Arg .pure)) := as.filterMap fun
    | .type t _ => some t
    | _ => none
  let debug := (← IO.getEnv "L2R_DEBUG").isSome
  let mut out := {}
  -- The calls that took the instance at `lcAny`, each with its group's
  -- earlier call.
  let mut uniformOf : Std.HashMap FVarId FVarId := {}
  for r in scan.order do
    let some members := scan.groups[r]? | continue
    let some (f, us, args₀, ty₀) := scan.calls[r]? | continue
    -- The calls of `f` merged into `r`, with their arguments and types.
    let group := members.filterMap fun m => match scan.calls[m]? with
      | some (g, _, args, ty) => if g == f && args.size == args₀.size then some (m, args, ty) else none
      | none => none
    let later := group.filter fun (_, args, _) => typeArgs args != typeArgs args₀
    if later.isEmpty then continue
    let served ← later.filterM fun (_, _, ty) => (serves ty₀ ty).run' {}
    if served.size < later.size then
      if let some args ← uniformArgs f args₀ (group.map (·.2.1)) uniformOf then
        let allowed ← do
          if !scan.closed.contains r then pure true
          else if ← keepsInstance f args₀ args then pure true
          else later.allM fun (_, _, ty) => (serves ty₀ ty (strict := false)).run' {}
        if allowed then
          if debug then IO.eprintln s!"lean2rr: merged calls of {f}: {group.size + 1} at lcAny"
          out := out.insert r (us, args)
          uniformOf := uniformOf.insert r r
          for (m, _, _) in group do
            out := out.insert m (us, args)
            uniformOf := uniformOf.insert m r
          continue
    if debug then
      IO.eprintln s!"lean2rr: merged calls of {f}: {served.size} at the earlier call's types, {later.size - served.size} apart"
    for (m, _, _) in served do
      out := out.insert m (us, args₀)
  return out
where
  go (code : Code .pure) (map : Std.HashMap Expr FVarId) : StateT MergeScan CoreM Unit := do
    match code with
    | .let d k =>
      let env ← getEnv
      let s ← get
      let rep (x : FVarId) : FVarId := s.reps.getD x x
      let closedArg (a : Arg .pure) : Bool := match a with
        | .fvar x => s.closed.contains x
        | _ => true
      let isClosed := match d.value with
        | .lit _ | .erased => true
        | .const _ _ args _ => args.all closedArg
        | .proj _ _ x => s.closed.contains x
        | .fvar .. => false
      if isClosed then modify fun s => { s with closed := s.closed.insert d.fvarId }
      -- A value that is another variable in mono: a trivial structure's
      -- constructor or projection, `Decidable.decide`.
      let alias? : Option FVarId ← match d.value with
        | .const c _ args _ =>
          if c == ``Decidable.decide then
            pure (match (args[1]? : Option (Arg .pure)) with | some (.fvar x) => some x | _ => none)
          else match env.find? c with
            | some (.ctorInfo ci) =>
              match ← hasTrivialStructure? ci.induct with
              | some info => pure (match (args[info.numParams + info.fieldIdx]? : Option (Arg .pure)) with
                  | some (.fvar x) => some x
                  | _ => none)
              | none => pure none
            | _ => pure none
        | .proj s i x =>
          match ← hasTrivialStructure? s with
          | some info => pure (if info.fieldIdx == i then some x else none)
          | none => pure none
        | _ => pure none
      if let some x := alias? then
        modify fun s => { s with reps := s.reps.insert d.fvarId (rep x) }
        return ← go k map
      let arg (a : Arg .pure) : Expr := match a with
        | .fvar x => .fvar (rep x)
        | _ => erasedExpr
      let key : Expr := match d.value with
        | .const ``Decidable.isTrue .. => .const ``Bool.true []
        | .const ``Decidable.isFalse .. => .const ``Bool.false []
        | .const f _ args _ => mkAppN (.const f []) (args.map arg)
        | .fvar g args => mkAppN (.fvar (rep g)) (args.map arg)
        | .proj s i x => .proj s i (.fvar (rep x))
        | .lit l => l.toExpr
        | .erased => erasedExpr
      if let .const f us args _ := d.value then
        unless env.isConstructor f || isExtern env f || (← isInstanceReducible f) do
          modify fun s => { s with calls := s.calls.insert d.fvarId (f, us, args, d.type),
                                   order := s.order.push d.fvarId }
      let neverExtract := match d.value with
        | .const f .. => hasNeverExtractAttribute env f
        | _ => false
      if neverExtract then go k map
      else match map[key]? with
        | some r =>
          modify fun s => { s with reps := s.reps.insert d.fvarId r,
                                   groups := s.groups.insert r ((s.groups.getD r #[]).push d.fvarId) }
          go k map
        | none => go k (map.insert key d.fvarId)
    | .fun d k _ => go d.value {}; go k map
    | .jp d k => go d.value map; go k map
    | .cases cs => for alt in cs.alts do go alt.getCode map
    | _ => pure ()

/-- Make the calls `erasedMerges` finds with the arguments it gives them;
their binders get the type of the new call. -/
partial def alignErasedMerges (code : Code .pure) : CompilerM (Code .pure) := do
  let marked ← erasedMerges code
  if marked.isEmpty then return code
  go marked code
where
  go (marked : Std.HashMap FVarId (List Level × Array (Arg .pure))) (code : Code .pure) :
      CompilerM (Code .pure) := do
    match code with
    | .let d k =>
      let d ← match marked[d.fvarId]?, d.value with
        | some (us, args₀), .const f _ _ _ =>
          let value : LetValue .pure := .const f us args₀
          d.update (← value.inferType) value
        | _, _ => pure d
      return code.updateLet! d (← go marked k)
    | .fun d k _ =>
      let d ← d.update d.type d.params (← go marked d.value)
      return code.updateFun! d (← go marked k)
    | .jp d k =>
      let d ← d.update d.type d.params (← go marked d.value)
      return code.updateFun! d (← go marked k)
    | .cases cs =>
      let alts ← cs.alts.mapM fun alt => return alt.updateCode (← go marked alt.getCode)
      return code.updateAlts! alts
    | c => return c

/-- Process one instance: instantiate, simplify, rename, record. -/
def monoInstance (key : InstKey) (name : Name) : MonoM Unit := do
  modify fun s => { s with current := some key, currentInst := some name }
  let some decl ← baseDeclFor? key.decl
    | throwError "lean2rr: no base declaration for {key.decl} (internal error)"
  let keepMissing := true
  match decl.value with
  | .extern _ =>
    let inst ← (instantiateExtern decl name key.typeArgs).run (phase := .base)
    modify fun s => { s with externs := s.externs.push (uniformDecl inst) }
  | .code _ =>
    let doSimp := (← get).config.simp
    let classPositions ← classParamPositions decl
    let inst ← (do
        let inst ← instantiate decl name key.typeArgs keepMissing classPositions key.dicts
        -- No inlining of definitions here: persisted bodies may contain
        -- type-unsafe code. Dictionary projections are still folded
        -- (`inlineProjInst?` is not gated by `inlineDefs`); general
        -- inlining happens in Stage 2 over lean2rr's own instances.
        let inst ← if doSimp then inst.simp { inlineDefs := false } else pure inst
        -- Calls that Lean's CSE merges after erasure call one instance.
        inst.value.mapCodeM alignErasedMerges >>= fun value => pure { inst with value }
        : CompilerM _).run (phase := .base)
    let inst := uniformDecl inst
    let .code code := inst.value | unreachable!
    let code ← renameCode {} code
    modify fun s => { s with decls := s.decls.push { inst with value := .code code } }

/-- Run Stage 1 from monomorphic `roots`; returns their instance names. -/
def monomorphize (roots : Array Name) (config : MonoConfig := {}) : CoreM (Array Name × MonoState) := do
  let act : MonoM (Array Name) := do
    let rootNames ← roots.mapM fun r => instanceName { decl := r, typeArgs := #[] }
    repeat
      let s ← get
      if h : s.work.size > 0 then
        let (key, name) := s.work[s.work.size - 1]
        modify fun s => { s with work := s.work.pop }
        monoInstance key name
      else break
    return rootNames
  act.run { config }

end LeanToReussir
