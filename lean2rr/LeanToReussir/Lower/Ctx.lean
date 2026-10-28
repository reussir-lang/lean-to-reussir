import Lean
import LeanToReussir.MonoTypesKeep
import LeanToReussir.LowerBase
import LeanToReussir.Lower.IntMatch

/-!
# Stage 4: the context of code lowering

How jumps to join points are lowered (J1–J4, translation plan §5.6), the
state machine of a declaration lowered as one function (J4), and the
context `lowerCode` threads through a declaration's code, with a slot for
the state of optional passes.
-/

namespace LeanToReussir
open Lean Compiler LCNF

/-- How a jump to a join point is lowered. -/
inductive JumpAction where
  /-- J1: the join point has a single jump; its body is inlined there. -/
  | inline (params : Array (Param .pure)) (body : Code .pure)
  /-- J2: jumps produce the join point's arguments (of types `tys`) as the
  value of the enclosing structured `let`: with two or more, a tuple
  (`tupleType tys`, its members in `memberOrder`). -/
  | yield (tys : Array RR.Ty)
  /-- J3: jumps call the outlined function with the captured variables
  followed by the arguments. -/
  | call (fn : String) (captured : Array String)
  /-- J4: jumps re-enter the declaration's state machine at the join point's
  variant (see `StateMachine`). -/
  | enter (variant : String) (captured : Array String)

/-- Another declaration of a state machine that runs a cycle of
declarations calling each other in tail position (`tailCallGroups`): its
entry variant, whose fields are its parameters, its arity, and the function
that enters the state machine at that variant. A tail call of it from the
state machine re-enters the state machine at that variant; a tail call of
it from another declaration's own function calls `entryFn`. -/
structure SmMember where
  name : Name
  variant : String
  arity : Nat
  /-- Its parameters (the variant's fields): names and types. -/
  params : Array (String × RR.Ty)
  /-- The function, with its parameters, that enters the state machine at
  `variant` (`fnName name ++ "_cyc"`, `_lit` for the light state machine;
  the declaration's own function is `fnName name`). -/
  entryFn : String
  deriving Inhabited

/-- A self-recursive declaration whose outlined join points call it back in
tail position is lowered as one function over an enum of entry points (J4,
translation plan §5.6): the declaration's own entry and one variant per
outlined join point. Jumps to those join points and self tail calls become
self tail calls of that function, which LLVM turns into a loop; separate
functions would make the loop mutually recursive, using stack per
iteration. Declarations that call each other in tail position (a cycle,
`tailCallGroups`) also run in one state machine, with an entry variant per
declaration (`members`): a tail call between them re-enters it, where a
call between separate functions uses stack per call unless LLVM makes it a
sibling call. That state machine is named apart from the first
declaration's own (`entryFn`): each declaration keeps its own function,
and only its tail calls of the others enter the cycle's state machine
(`CodeCtx.cycles`), or its light state machine, of its light
declarations, when it has one (`lowerGroup`). Planned and emitted by the lowering hook
`LowerHooks.stateMachine`; `lowerCode` re-enters it when the context has
one. -/
structure StateMachine where
  /-- The dispatching function. -/
  fn : String
  /-- The name of the entry-point enum, whose variants are `e` for the
  declaration itself and one per outlined join point. The lowering marks
  each call and jump that enters the state machine with its variant
  (`mode::v`). The core form emits this enum. Opt/StateMachines emits it
  only when a variant keeps a field; when every variant is nullary, the
  entry point is an integer, each mark becomes the variant's literal, and
  no enum is emitted. -/
  mode : String
  /-- The declaration, whose tail calls re-enter at `entry`. -/
  self : Name
  arity : Nat
  /-- Names of the declaration's parameters. -/
  params : Array String
  entry : String := "e"
  /-- The function, with the declaration's parameters, that enters the
  state machine at `entry`: the declaration's own function (`fnName self`),
  or for a state machine of a cycle of tail calls `fnName self ++ "_cyc"`
  (`_lit` for its light state machine). -/
  entryFn : String
  /-- The other declarations of its cycle of tail calls (`SmMember`), in
  the order of their entry variants; none for a single declaration. -/
  members : Array SmMember := #[]
  /-- Which form of state machine this is: `.anonymous` for the core's
  (`Lower/StateMachine`); an optional pass that plans another form tags it
  with its name, and its hooks handle that form only. -/
  form : Name := .anonymous

structure CodeCtx where
  vars : Std.HashMap FVarId (String × RR.Ty) := {}
  jumps : Std.HashMap FVarId JumpAction := {}
  /-- Types of join-point parameters, for lowering jump arguments (of the
parameters the join point takes: rule 4 removes the erased ones). -/
  jpParams : Std.HashMap FVarId (Array RR.Ty) := {}
  /-- Which parameters of each join point it takes (not the erased ones,
  rule 4); a jump passes the arguments of these. -/
  jpKeep : Std.HashMap FVarId (Array Bool) := {}
  sm : Option StateMachine := none
  /-- Bodies of the join points in scope. -/
  jpBodies : Std.HashMap FVarId (Code .pure) := {}
  /-- The join points in scope jumped to once (J1, inlined at their jump). -/
  jpSingle : FVarIdSet := {}
  /-- The declarations of the call cycle of the declaration being lowered
  (`JpScope.loop`). -/
  loop : NameSet := {}
  /-- The declaration whose code is being lowered (its own function, or its
  arm of a cycle's state machine): a tail call of another declaration is
  no tail call natively when the caller keeps an argument until it returns
  (`borrowKeeps`), and stays a call. -/
  decl : Name := .anonymous
  /-- The state machines of the cycle of tail calls of the declaration
  being lowered that its tail calls enter (`lowerGroup`), in order of
  preference: while its own function is lowered, the cycle's light state
  machine, if any, then the cycle's state machine; while its arm of the
  light state machine is lowered, the cycle's state machine. A tail call of
  another declaration of the cycle enters the first of them that has it
  (calls that declaration's entry function of that state machine,
  `StateMachine.entryFn`, `SmMember.entryFn`). -/
  cycles : Array StateMachine := #[]
  /-- Variables that a hook bound again, in the current alternative, to a
  value of its own equal to theirs (Opt/NullaryScrutinee): other hooks must
  not bind them again there. -/
  pinned : FVarIdSet := {}
  /-- Variables bound in the function being lowered to an application of a
  constant (a declaration or a constructor) to at least one argument: the
  constant and the number of arguments. -/
  letCalls : Std.HashMap FVarId (Name × Nat) := {}
  /-- Matched values that the current alternative returns as an expression
  of their type instead of themselves (Opt/FreshRebuild: the constructor
  rebuilt from the alternative's fields). Plain: none. -/
  rebuild : Std.HashMap FVarId (RR.Expr × RR.Ty) := {}
  /-- The matched values of the enclosing alternatives, with the
  alternatives' field parameters: a `reset` of Lean's in a nested branch
  releases the fields the branch does not read (`armResetNames`). -/
  altParams : Std.HashMap FVarId (Array FVarId) := {}
  /-- The variables that the outlined join points in scope (J3, J4) capture,
  with their types. A jump to one passes them by these names, also where
  `vars` names the same LCNF variable differently (a hook or a `cases` bound
  it again in an alternative: Opt/NullaryScrutinee, a converted scrutinee,
  Opt/LazyFields); the names stay in scope, so a join point outlined there
  that jumps to one captures them too. Also the binders that a rebuilt
  matched value reads (`rebuild`, Opt/FreshRebuild), which `vars` no longer
  names when a field is converted: a join point outlined there that
  returns the value captures them. -/
  captured : Std.HashMap String RR.Ty := {}
  /-- The variables the declaration being lowered uses (`codeUses` of its
  body): a field parameter that is not used is not converted to its own
  type (`bindField`). -/
  used : Std.HashSet FVarId := {}
  /-- The variables of the declaration being lowered whose every use puts
  the value into a box (`boxedOnlyVars`): a field parameter among them
  keeps the field's `Box` (`bindField`), and a `let` among them is bound as
  a `Box` (`lowerCode`). -/
  boxedOnly : Std.HashSet FVarId := {}
  /-- The field parameters that `bindField` converted to their own types,
  with the name of the conversion's `let`: a binding drops such a `let`
  when its code does not use it (`dropUnusedConvs`), and `lazy-fields`'
  consuming re-match keeps it instead of converting the field again. -/
  fieldConv : Std.HashMap FVarId String := {}
  /-- With `LowerCtx.intMatch`: the declaration's `let`s of `Nat` literals
  and how many times its code names each variable (`intMatchInfo`), for
  the matches on `Nat` and `Int` (Lower/IntMatch). -/
  intInfo : IntMatchInfo := {}
  /-- The loop-carried increments of the declaration being lowered
  (`loopCarriedAdds`): each `let z := Nat.add y l` (`l` a literal) whose
  `y` is the declaration's parameter at the position where a self tail
  call passes `z`, with `y`. Such an increment reads the parameter itself,
  not the rebinding after a proved access (`rebindIndex`'s exception). -/
  loopAdds : Std.HashMap FVarId FVarId := {}
  /-- The `Nat` variables that `rebindIndex` bound again after a proved
  access (to `l2r_nat_of_index` of the access's word), with the Reussir
  name each had before its first rebinding, which is in scope wherever the
  rebinding is. Empty in an outlined join point's body and in a local
  function, where that name is not captured. -/
  indexOrig : Std.HashMap FVarId String := {}
  /-- The state optional passes keep in the context, by the pass's name
  (`CodeCtx.getExt?`, `CodeCtx.setExt`). -/
  ext : NameMap Dynamic := {}

/-- The state optional pass `key` keeps in the context, if any. -/
def CodeCtx.getExt? (ctx : CodeCtx) (α : Type) [TypeName α] (key : Name) : Option α :=
  (ctx.ext.find? key).bind (·.get? α)

/-- The context with optional pass `key`'s state set to `v`. -/
def CodeCtx.setExt {α : Type} [TypeName α] (ctx : CodeCtx) (key : Name) (v : α) : CodeCtx :=
  { ctx with ext := ctx.ext.insert key (.mk v) }

end LeanToReussir
