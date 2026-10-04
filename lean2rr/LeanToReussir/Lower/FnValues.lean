import LeanToReussir.Lower.Ctx

/-! # Function values

A Lean function value of (lowered, curried) type `T = A₁ → … → Aₙ → R` is
a value of a generated shared enum `L2RFn_…` (translation plan §5.3), not
a Reussir closure: applying a shared Reussir closure copies it, and
curried application allocates a closure per argument. The variants:
- `z`: the `box(0)` placeholder, a function that is never applied (an
  application returns the zero of its result type);
- `raw(A₁ -> …)`: a Reussir closure (built by glue code);
- `p<m>_<id>(c₁, …, cₘ)`: target `id` (a declaration, extern, constructor
  or stream primitive) with its first `m` arguments captured;
- `w<S>(g)`: a function value `g` of another representation `S` of the same
  Lean type, converted at each application.
Applying `j` arguments calls a generated `l2r_ap<j>_…` that matches the
variant. A target whose remaining arity is `j` is called directly and
nothing is allocated, as with `lean_apply_n` at exact arity; with fewer
arguments a new `p` value is built (a partial application); with more, the
result is applied to the rest. The application functions and the enums are
generated at the end (`finishFnValues`), when all variants are known. -/

namespace LeanToReussir
open Lean Compiler LCNF

/-- Parameter types of a function type's curried chain, and its result. -/
partial def fnChain (t : RR.Ty) : Array RR.Ty × RR.Ty :=
  go t #[]
where
  go : RR.Ty → Array RR.Ty → Array RR.Ty × RR.Ty
    | .fn d c, acc => go c (acc.push d)
    | t, acc => (acc, t)

/-- The type of a value of function type `t` applied to `j` arguments. -/
def fnResult : RR.Ty → Nat → RR.Ty
  | t, 0 => t
  | .fn _ c, j + 1 => fnResult c j
  | t, _ => t

def fnVariantName : FnVariant → String
  | .part id m => s!"p{m}_{id}"
  | .wrap src => s!"w{src.enc}"

def applyFnName (t : RR.Ty) (j : Nat) : String := s!"l2r_ap{j}_{t.enc}"

def addFnVariant (t : RR.Ty) (v : FnVariant) : LowerM Unit := do
  let vs ← getPart (·.fnVariants.getD t #[])
  unless vs.contains v do
    modify fun s => { s with fnVariants := s.fnVariants.insert t (vs.push v), fnVariantCount := s.fnVariantCount + 1 }

/-- `f`, of function type `t`, applied to `args` (at `t`'s parameter types;
at most the chain length). -/
def applyCall (f : RR.Expr) (t : RR.Ty) (args : Array RR.Expr) : LowerM RR.Expr := do
  let j := args.size
  unless ← getPart (·.fnApplySet.contains (t, j)) do
    modify fun s => { s with fnApplies := s.fnApplies.push (t, j), fnApplySet := s.fnApplySet.insert (t, j) }
  return .call (applyFnName t j) #[] (#[f] ++ args)

/-- A function value of type `t = A → B` from a Reussir lambda
`|x : A| body`, where `body : B`. -/
def rawFnValue (t : RR.Ty) (x : String) (body : RR.Block) : RR.Expr :=
  match t with
  | .fn d _ => .ctor (RR.fnTypeName t) (some "raw") #[.lam x d body]
  | _ => .lam x t body

/-- The type of target `tg` with its first `m` arguments captured. -/
def partTy (tg : FnTarget) (m : Nat) : RR.Ty :=
  tg.params[m:].toArray.foldr (fun a b => RR.Ty.fn a b) tg.ret

/-- Target `tg` with its first arguments `captured` (at `tg`'s parameter
types; fewer than all of them), and the value's type. -/
def partValue (tg : FnTarget) (captured : Array RR.Expr) : LowerM (RR.Expr × RR.Ty) := do
  unless (← get).fnTargets.contains tg.id do
    modify fun s => { s with fnTargets := s.fnTargets.insert tg.id tg }
  let t := partTy tg captured.size
  let v := FnVariant.part tg.id captured.size
  addFnVariant t v
  return (.ctor (RR.fnTypeName t) (some (fnVariantName v)) captured, t)

/-- `l2r_fconv_S_T(f)`: function value `f : S` at representation `T`. A
value that is itself a wrapped value of another representation `R`
(`w<R>(g)`) is converted from `R` directly (`g` itself when `R` is `T`), so
that a value converted back and forth (a structure field crossing uniform
code in a loop) is not wrapped again each time; otherwise it is wrapped
(`w<S>`). The body is generated at the end (`genFnConv`). -/
def fnConvFn (src dst : RR.Ty) : LowerM String := do
  unless ← getPart (·.fnConvSet.contains (src, dst)) do
    modify fun s => { s with fnConvs := s.fnConvs.push (src, dst), fnConvSet := s.fnConvSet.insert (src, dst) }
  return s!"l2r_fconv_{src.enc}_{dst.enc}"

/-- The generated function unboxing a `Box` to function type `t` (its body
is generated at the end, with the other unboxing functions). -/
def unboxFnFn (t : RR.Ty) : LowerM String := do
  unless ← getPart (·.fnUnboxTargetSet.contains t) do
    modify fun s => { s with fnUnboxTargets := s.fnUnboxTargets.push t, fnUnboxTargetSet := s.fnUnboxTargetSet.insert t }
  return s!"l2r_unbox_fn_{t.enc}"

end LeanToReussir
