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

/-- The function type with parameter types `ps` (closed: as `splitFnType`
gives them) and result `r`. -/
def mkFnType (ps : Array Expr) (r : Expr) : Expr :=
  ps.foldr (fun p b => .forallE `a p b .default) r

/-- What a constant application targets. -/
inductive Callee where
  /-- A declaration with code in the translated program: Reussir parameter
  types (one per Lean parameter), result type, and which parameters its
  Reussir function takes (rule 4a, `keepMask`). -/
  | code (fn : String) (params : Array RR.Ty) (ret : RR.Ty) (keep : Array Bool)
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
    | .code _ => return .code (fnName f) (← ps.mapM lowerType) (← lowerType r) (keepMask (d.params.map (·.type)))
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

/-- A partial application of target `tg` to its first `j` Lean arguments,
of which it captures `supplied` (those it takes, at its parameter types),
as a value of type `expected`, the type of the binder. That may be
another representation (a lifted lambda whose result Lean typed `lcAny`,
a closure stored at a uniform type, `Box`): the value is then converted
(`tryCoerce`). The target runs only when its last argument arrives. -/
def partialApp (tg : FnTarget) (j : Nat) (supplied : Array RR.Expr) (expected : RR.Ty) : LowerM RR.Expr := do
  let (v, t) ← partValue tg j supplied
  coerce v t expected

/-- An argument of a Lean application: a value with its Reussir type, or
`◾`. -/
inductive LArg where
  | val (e : RR.Expr) (t : RR.Ty)
  | erased
  deriving Inhabited

/-- Apply `f : t` to Lean arguments `args`, along `t`'s Lean positions
(rule 4): a phantom domain takes its argument away; any other domain gets
its argument at its type (`◾` gives the domain's placeholder: `()` at a
unit domain, Lean's `box(0)` at a relevant one). The domains in a row are
applied at once (`applyCall`, up to the chain's length), so that a target
whose arity they reach is called directly. A function value of statically
unknown type (`Box`) is unboxed to `Box → Box`, which has a domain for
every Lean argument (`◾` included: uniform code applies `box(0)` there).
The result and its type (by Lean positions). -/
def applyLean (f : RR.Expr) (t : RR.Ty) (args : Array LArg) : LowerM (RR.Expr × RR.Ty) := do
  let mut e := f
  let mut t := t
  let mut i := 0
  while i < args.size do
    if t == RR.Ty.box then
      let canon := RR.Ty.fn RR.Ty.box RR.Ty.box
      e ← coerce e RR.Ty.box canon
      t := canon
    unless t matches .fn .. do
      throwError "lean2rr: application of a non-function value of type {t.render}"
    let start := t
    let mut as := #[]
    while i < args.size do
      let .fn d c := t | break
      if d != RR.Ty.phantom then
        let a : LArg := args[i]!
        as := as.push (← match a with
          | .val a aty => coerce a aty d
          | .erased => zeroValue d)
      t := c
      i := i + 1
    unless as.isEmpty do e ← applyCall e start as
  return (e, t)

/-- Apply `f : t` to `args` (each with its type, one per Lean position of
`t`; see `applyLean`). The result and its type. -/
def applyExprs (f : RR.Expr) (t : RR.Ty) (args : Array (RR.Expr × RR.Ty)) :
    LowerM (RR.Expr × RR.Ty) :=
  applyLean f t (args.map fun (a, aty) => .val a aty)

/-- Apply a function value `f : fty` to further (Lean) arguments. -/
def applyChain (f : RR.Expr) (fty : RR.Ty) (ctx : CodeCtx) (args : Array (Arg .pure)) :
    LowerM (RR.Expr × RR.Ty) := do
  let largs ← args.mapM fun a => do
    match a with
    | .fvar x =>
      match ctx.vars[x]? with
      | some (n, t) => pure (LArg.val (.var n) t)
      | none => throwError "lean2rr: unbound variable {x.name} (internal error)"
    | _ => pure .erased
  applyLean f fty largs

end LeanToReussir
