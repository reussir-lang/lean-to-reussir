import Lean
import LeanToReussir.Collect
import LeanToReussir.Relevance
import LeanToReussir.Passes

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
  /-- Base declarations compiled by lean2rr itself (safe reference
  definitions of unsafe implementations, and their auxiliary declarations). -/
  extraBase : NameMap (Decl .pure) := {}
  /-- Safe definitions that could not be compiled (the unsafe version stays). -/
  uncompilable : NameSet := {}

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
  -- would create a new instance per level; use the uniform one at once.
  let key ← match (← get).current with
    | some cur =>
      if cur.decl == key.decl && cur.typeArgs.size == key.typeArgs.size &&
         (cur.typeArgs.zip key.typeArgs).any (fun (a, b) => a != b && a != anyExpr && (b.find? (· == a)).isSome) then
        modify fun s => { s with uniformArgs := s.uniformArgs + key.typeArgs.size }
        pure { key with typeArgs := key.typeArgs.map fun _ => anyExpr, dicts := #[] }
      else pure key
    | none => pure key
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
    keys := s.keys.insert n key }
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

/-- The origin of a specialization name `X._at_.Y.spec_N`: `X`. -/
def specOrigin? (n : Name) : Option Name :=
  let comps := n.components
  match comps.idxOf? `_at_ with
  | some i => some ((comps.take i).foldl (· ++ ·) .anonymous)
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

/-- The base declaration to instantiate for `n`: one compiled by lean2rr,
or Lean's persisted one — unless that one is tainted by type-unsafe code, in
which case `n` is recompiled from source. -/
def baseDeclFor? (n : Name) : MonoM (Option (Decl .pure)) := do
  if let some d := (← get).extraBase.find? n then return some d
  let some d ← getBaseDecl? n | do
    -- A safe declaration with an `implemented_by` has no persisted body.
    if (← unsafeImplMap).toList.any (·.2 == n) then
      if ← recompile n then return (← get).extraBase.find? n
    return none
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
  "lean_mk_io_error_unsupported_operation"]

/-- Is `sym` a fallible IO primitive whose errors the runtime reports
through its last-error protocol? -/
def isFallibleIOSym (sym : String) : Bool :=
  sym.startsWith "lean_io_prim_handle_" ||
  sym ∈ ["lean_io_remove_file", "lean_io_create_dir", "lean_io_remove_dir", "lean_io_rename",
         "lean_io_hard_link", "lean_io_realpath", "lean_io_read_dir", "lean_io_metadata",
         "lean_io_symlink_metadata"]

/-- A fallible IO extern needs the `IO.Error` builders: instantiate them. -/
def ensureIOErrorBuilders (f : Name) : MonoM Unit := do
  let some sym := getExternNameFor (← getEnv) `c f | return
  unless isFallibleIOSym sym do return
  for b in ioErrorBuilderSyms do
    if let some d := (← exportMap).get? b then
      discard <| instanceName { decl := d, typeArgs := #[] }

/-- Redirect a call target: an extern implemented by an exported Lean
definition becomes that definition; with `safeSources`, a type-unsafe
implementation becomes the safe declaration it implements. -/
def redirectTarget (f : Name) : MonoM Name := do
  -- An extern whose C symbol is provided by an `@[export]` Lean definition
  -- is that definition (Lean's runtime calls it; we compile it).
  if isExtern (← getEnv) f then
    if let some sym := getExternNameFor (← getEnv) `c f then
      if let some d := (← exportMap).get? sym then
        if d != f then return d
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

/-- The static dictionary a `let` value denotes, given the static
dictionaries of variables in scope. -/
def staticDict? (statics : Std.HashMap FVarId Expr) (v : LetValue .pure) (ty : Expr) : MonoM (Option Expr) := do
  unless (← isClass? ty).isSome do return none
  match v with
  | .const c _ args _ =>
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
  let f ← redirectTarget f
  if isExtern (← getEnv) f then ensureIOErrorBuilders f
  let some callee ← baseDeclFor? f | return none
  let positions := typeParamPositions callee
  if let .extern _ := callee.value then
    if positions.isEmpty then
      modify fun s => { s with monoExterns := s.monoExterns.insert f }
      return none
  let mut typeArgs := #[]
  for i in positions do
    match args[i]? with
    | some (.type e _) => typeArgs := typeArgs.push (← normTypeArg e)
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
      | .const f _ args _ =>
        match ← renameApp statics f args with
        | some (n, args') => pure { d with value := .const n [] args' }
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

/-- Process one instance: instantiate, simplify, rename, record. -/
def monoInstance (key : InstKey) (name : Name) : MonoM Unit := do
  modify fun s => { s with current := some key }
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
        if doSimp then inst.simp { inlineDefs := false } else pure inst : CompilerM _).run (phase := .base)
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
