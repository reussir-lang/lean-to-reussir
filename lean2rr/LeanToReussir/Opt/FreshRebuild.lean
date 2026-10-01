import Lean
import LeanToReussir.PassConfig

/-!
# Returned matched values rebuilt (optimization `fresh-rebuild`)

Lean's `simp` replaces a constructor rebuilt from a match's fields by the
matched value itself: `match r with | .error e => .error e | .ok a => …`
becomes `| .error _ => r`. That is the error arm of every `ExceptT`,
`Option` and `EStateM` bind. lean2rr returns the value itself, as native
Lean does (translation plan §5.5): a copy would be another object for
`ptrAddrUnsafe`, and a shared value rebuilt is a copy (allocated, and a
DAG kept by returning existing nodes would become a tree). But the matched
value then stays live across the match, so Reussir cannot reuse its cell
for what the other arms build: each bind's success path allocates the new
result and frees the old one (the classic MonadicInterp: 12% of its time).

Where neither matters, the arm returns the constructor rebuilt from its
fields, so every arm consumes the matched cell and Reussir reuses it (for
the rebuilt one too: the same cell comes back when it was unique). Only:
- in a program that never asks for an object's identity
  (`LowerCtx.observesIdentity`: no `ptrAddrUnsafe`, nothing that inlines
  to it such as `ptrEq`, no `ST.Ref.ptrEq`), where a value and an equal
  copy cannot be told apart;
- when the matched value is the result of a call or a constructor
  application in the same function (`CodeCtx.fresh`): a bind's result,
  normally built just before and unique. A parameter or a field (a node of
  a persistent structure that a lookup returns) is returned itself;
- when the arm binds every field and uses the matched value only by
  returning it (`onlyReturned`), in an enum matched at its own type.

Without the pass every such arm returns the matched value itself.
-/

namespace LeanToReussir
open Lean Compiler LCNF

/-- Whether `x` occurs in `c` only as a returned value (`return x`). -/
partial def Opt.FreshRebuild.onlyReturned (x : FVarId) (c : Code .pure) : Bool :=
  let inArg : Arg .pure → Bool := fun | .fvar y => y == x | _ => false
  let inValue : LetValue .pure → Bool := fun
    | .fvar f args => f == x || args.any inArg
    | .const _ _ args _ => args.any inArg
    | .proj _ _ y _ => y == x
    | _ => false
  match c with
  | .let d k => !inValue d.value && onlyReturned x k
  | .fun d k _ | .jp d k => onlyReturned x d.value && onlyReturned x k
  | .jmp _ args => !args.any inArg
  | .cases cs => cs.discr != x && cs.alts.all (onlyReturned x ·.getCode)
  | .return _ | .unreach _ => true

/-- The fields of an enum alternative (`LowerHooks.enumFields`): when the
alternative only returns the fresh matched value, every field stays bound
and the value is returned rebuilt from them (`CodeCtx.rebuild`). -/
def Opt.FreshRebuild.enumFields (prev : CodeCtx → CasesArm → Array (Option String) →
      LowerM (Array (Option String) × CodeCtx))
    (ctx : CodeCtx) (arm : CasesArm) (binders : Array (Option String)) :
    LowerM (Array (Option String) × CodeCtx) := do
  if !(← read).observesIdentity && !arm.view && arm.shared && ctx.fresh.contains arm.discr &&
      !binders.isEmpty && binders.all Option.isSome && onlyReturned arm.discr arm.code then
    let e := RR.Expr.ctor arm.ty (some arm.layout.variant) (binders.map fun b => .var b.get!)
    return (binders, { ctx with rebuild := ctx.rebuild.insert arm.discr (e, .named arm.ty) })
  prev ctx arm binders

/-- Registry entry point. -/
def Opt.FreshRebuild.install (c : PassConfig) : PassConfig :=
  { c with lower := { c.lower with enumFields := enumFields c.lower.enumFields } }

end LeanToReussir
