import LeanToReussir.Lower.Conv

/-! # Declarations and signatures -/

namespace LeanToReussir
open Lean Compiler LCNF

/-- Parameter types and result type of a function type with `n` parameters. -/
def splitFnType (ty : Expr) (n : Nat) : Array Expr × Expr := Id.run do
  let mut ty := ty
  let mut ps := #[]
  for _ in [:n] do
    match ty.consumeMData with
    | .forallE _ d b _ => ps := ps.push d; ty := b.instantiate1 anyExpr
    | _ => break
  return (ps, ty)

/-- What a constant application targets. -/
inductive Callee where
  /-- A declaration with code in the translated program. -/
  | code (fn : String) (params : Array RR.Ty) (ret : RR.Ty)
  /-- An extern: Lean name (original, for the extern table), key type
  arguments (for polymorphic externs), mono parameter types, result type. -/
  | extern (orig : Name) (typeArgs : Array Expr) (params : Array Expr) (ret : Expr)
  /-- A constructor. -/
  | ctor (info : ConstructorVal)
  /-- A constant defined by `initialize`: read from its once-cell. -/
  | initConst (slot : Nat) (type : Expr)

/-- Record a call of extern `orig` if lean2rr refuses it (an extern of the
program without a Lean definition or binding, `LowerCtx.externRefusals`):
`lowerProgram` rejects the program, naming it. Every call of an extern,
direct, partial or as a function value, gets its target here. -/
def noteRefusedExtern (orig : Name) : LowerM Unit := do
  unless (← read).externRefusals.contains orig do return
  unless (← get).missingExterns.any (·.2 == orig) do
    let sym := (getExternNameFor (← getEnv) `c orig).getD ""
    modify fun s => { s with missingExterns := s.missingExterns.push (sym, orig) }

def calleeOf (f : Name) : LowerM Callee := do
  if let some slot := (← get).initSlots.find? f then
    return .initConst slot (← toMonoTypeKeep (← getOtherDeclBaseType f []))
  if let some (.ctorInfo c) := (← getEnv).find? f then
    -- Constructors of builtin types implemented by the runtime
    -- (`Int.ofNat` is `lean_nat_to_int`, …) are calls, as in Lean's IR.
    unless isExtern (← getEnv) f do return .ctor c
  if let some d := (← read).decls.find? f then
    let (ps, r) := splitFnType d.type d.params.size
    match d.value with
    | .code _ => return .code (fnName f) (← ps.mapM lowerType) (← lowerType r)
    | .extern _ =>
      let key := (← read).keys.find? f
      let orig := key.map (·.decl) |>.getD f
      noteRefusedExtern orig
      return .extern orig (key.map (·.typeArgs) |>.getD #[]) ps r
  -- A monomorphic extern kept under its own name: take Lean's persisted mono signature.
  if let some d ← getMonoDecl? f then
    noteRefusedExtern f
    let (ps, r) := splitFnType d.type d.params.size
    return .extern f #[] ps r
  if let some (.ctorInfo c) := (← getEnv).find? f then
    let ty ← toMonoTypeKeep (← getOtherDeclBaseType f [])
    let (ps, r) := splitFnType ty (c.numParams + c.numFields)
    return .extern f #[] ps r
  throwError "lean2rr: unknown callee {f} (internal error)"

/-- Argument lowering with conversion to the expected type. -/
def lowerArg (ctx : CodeCtx) (a : Arg .pure) (expected : RR.Ty) : LowerM RR.Expr := do
  match a with
  | .fvar x =>
    match ctx.vars[x]? with
    | some (n, t) => coerce (.var n) t expected
    | none => throwError "lean2rr: unbound variable {x.name} (internal error)"
  -- `◾` (type arguments, proofs, or `box(0)` at a relevant type)
  | _ => zeroValue expected

/-- A partial application of target `tg` to `supplied` (at its parameter
types) as a value of type `expected`, the type of the binder. That may be
another representation (a lifted lambda whose result Lean typed `lcAny`,
a closure stored at a uniform type, `Box`): the value is then converted
(`tryCoerce`). The target runs only when its last argument arrives. -/
def partialApp (tg : FnTarget) (supplied : Array RR.Expr) (expected : RR.Ty) : LowerM RR.Expr := do
  let (v, t) ← partValue tg supplied
  coerce v t expected

/-- Apply `f : t` to `args` (each with its type): up to a chain's length at
a time (`applyCall`); a function value of statically unknown type (`Box`)
is unboxed to `Box → Box`. The result and its type. -/
def applyExprs (f : RR.Expr) (t : RR.Ty) (args : Array (RR.Expr × RR.Ty)) :
    LowerM (RR.Expr × RR.Ty) := do
  let mut e := f
  let mut t := t
  let mut i := 0
  while i < args.size do
    if t == RR.Ty.box then
      let canon := RR.Ty.fn RR.Ty.box RR.Ty.box
      e ← coerce e RR.Ty.box canon
      t := canon
    let (doms, _) := fnChain t
    if doms.isEmpty then throwError "lean2rr: application of a non-function value of type {t.render}"
    let j := min doms.size (args.size - i)
    let mut as := #[]
    for k in [:j] do
      let (a, aty) := args[i + k]!
      as := as.push (← coerce a aty doms[k]!)
    e ← applyCall e t as
    t := fnResult t j
    i := i + j
  return (e, t)

/-- Apply a function value `f : fty` to further (Lean) arguments. -/
def applyChain (f : RR.Expr) (fty : RR.Ty) (ctx : CodeCtx) (args : Array (Arg .pure)) :
    LowerM (RR.Expr × RR.Ty) := do
  let mut e := f
  let mut t := fty
  let mut i := 0
  while i < args.size do
    if t == RR.Ty.box then
      let canon := RR.Ty.fn RR.Ty.box RR.Ty.box
      e ← coerce e RR.Ty.box canon
      t := canon
    let (doms, _) := fnChain t
    if doms.isEmpty then throwError "lean2rr: application of a non-function value of type {t.render}"
    let j := min doms.size (args.size - i)
    let mut as := #[]
    for k in [:j] do
      as := as.push (← lowerArg ctx args[i + k]! doms[k]!)
    e ← applyCall e t as
    t := fnResult t j
    i := i + j
  return (e, t)

end LeanToReussir
