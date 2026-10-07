import LeanToReussir.Lower.Ctx

/-! # Function values

A Lean function value of (lowered, curried) type `T = A₁ → … → Aₙ → R` is
a value of a generated shared enum `L2RFn_…` (translation plan §5.3), not
a Reussir closure: applying a shared Reussir closure copies it, and
curried application allocates a closure per argument. The variants:
- `z`: the `box(0)` placeholder, a function that is never applied (an
  application returns the zero of its result type);
- `raw(A₁ -> …)`: a Reussir closure (built by glue code);
- `p<j>_<id>(c₁, …)`: target `id` (a declaration, extern, constructor
  or stream primitive) applied to its first `j` Lean arguments, of which it
  captures those it takes (rule 4: not the erased ones);
- `w<S>(g)`: a function value `g` of another representation `S` of the same
  Lean type, converted at each application.
Applying `j` arguments calls a generated `l2r_ap<j>_…` that matches the
variant. A target whose remaining arity is `j` is called directly and
nothing is allocated, as with `lean_apply_n` at exact arity; with fewer
arguments a new `p` value is built (a partial application); with more, the
result is applied to the rest. The application functions and the enums are
generated at the end (`finishFnValues`), when all variants are known.

A function type can have phantom domains (`RR.Ty.phantom`: an erased Lean
domain without a parameter at run time, rule 4). The enum, its variants and
its application functions are those of the run-time type (`RR.Ty.rt`);
the Lean positions matter where Lean arguments are applied (`applyLean`),
where a target's parameters are matched with a type's domains (`genApply`)
and where a value is wrapped at another type (`w<S>` records both). -/

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
  | .part id j => s!"p{j}_{id}"
  -- The target type is named only when it has phantom domains (otherwise
  -- it is the enum's own type).
  | .wrap src dst => if dst.rt == dst then s!"w{src.enc}" else s!"w{src.enc}_{dst.enc}"

def applyFnName (t : RR.Ty) (j : Nat) : String := s!"l2r_ap{j}_{t.enc}"

/-- Register variant `v` of the enum of function type `t` (its run-time
type). -/
def addFnVariant (t : RR.Ty) (v : FnVariant) : LowerM Unit := do
  let t := t.rt
  let vs ← getPart (·.fnVariants.getD t #[])
  unless vs.contains v do
    modify fun s => { s with fnVariants := s.fnVariants.insert t (vs.push v) }

/-- `f`, of function type `t`, applied to `args` (at the parameter types of
`t`'s run-time type, `RR.Ty.rt`; at most its chain length). -/
def applyCall (f : RR.Expr) (t : RR.Ty) (args : Array RR.Expr) : LowerM RR.Expr := do
  let t := t.rt
  let j := args.size
  unless ← getPart (·.fnApplySet.contains (t, j)) do
    modify fun s => { s with fnApplies := s.fnApplies.push (t, j), fnApplySet := s.fnApplySet.insert (t, j) }
  return .call (applyFnName t j) #[] (#[f] ++ args)

/-- A function value of type `t = A → B` (at run time, `RR.Ty.rt`) from a
Reussir lambda `|x : A| body`, where `body : B`. -/
def rawFnValue (t : RR.Ty) (x : String) (body : RR.Block) : RR.Expr :=
  match t.rt with
  | tr@(.fn d _) => .ctor (RR.fnTypeName tr) (some "raw") #[.lam x d body]
  | _ => .lam x t body

/-- Whether target `tg` takes its Lean parameter `i` (rule 4a). -/
def FnTarget.takes (tg : FnTarget) (i : Nat) : Bool := tg.keep[i]?.getD true

/-- The number of arguments target `tg` captures from its first `j` Lean
arguments. -/
def FnTarget.captures (tg : FnTarget) (j : Nat) : Nat :=
  ((List.range j).filter tg.takes).length

/-- The fields of variant `v` of a function-value enum, besides `z`/`raw`:
a wrapped value, or the arguments a partial application captures. -/
def fnVariantFields (v : FnVariant) : LowerM (Array RR.Ty) := do
  match v with
  | .wrap src _ => return #[src]
  | .part id j =>
    let some tg := (← get).fnTargets[id]? | throwError "lean2rr: unknown function target {id}"
    return (tg.params.extract 0 j).zipIdx.filterMap fun (p, i) => if tg.takes i then some p else none

/-- The parameter types of target `tg` that its call takes. -/
def FnTarget.callParams (tg : FnTarget) : Array RR.Ty :=
  (tg.params.zipIdx.filter fun (_, i) => tg.takes i).map (·.1)

/-- The function type of target `tg`, by Lean positions (phantom domains
included). -/
def FnTarget.fnTy (tg : FnTarget) : RR.Ty :=
  tg.ty.getD (tg.params.foldr (fun a b => RR.Ty.fn a b) tg.ret)

/-- The type of target `tg` applied to its first `j` Lean arguments. -/
def partTy (tg : FnTarget) (j : Nat) : RR.Ty :=
  fnResult tg.fnTy j

/-- Target `tg` applied to its first `j` Lean arguments, which are fewer
than all of them, capturing `captured` (the arguments it takes, at its
parameter types), and the value's type. -/
def partValue (tg : FnTarget) (j : Nat) (captured : Array RR.Expr) : LowerM (RR.Expr × RR.Ty) := do
  unless (← get).fnTargets.contains tg.id do
    modify fun s => { s with fnTargets := s.fnTargets.insert tg.id tg }
  let t := partTy tg j
  let v := FnVariant.part tg.id j
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
