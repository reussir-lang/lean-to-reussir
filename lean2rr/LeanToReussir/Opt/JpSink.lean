import Lean
import LeanToReussir.PassConfig

/-!
# Join points sunk before the strategy is chosen (optimization `jp-sink`)

Before the join-point strategy is chosen (translation plan §5.6), every
join point is moved down to the smallest part of its scope that contains
all its jumps: past `let`s, into the single `cases` branch that jumps to it,
into the continuation or body of another join point. Free variables stay in
scope (binders are unique), and no code is duplicated. A join point declared
before a `cases` of which only one branch uses it often satisfies J2 once
sunk into that branch, instead of being outlined (J3), which would make a
loop through it mutually recursive. Without this pass join points stay
where Lean put them.
-/

namespace LeanToReussir
open Lean Compiler LCNF

/-- Does `c` jump to `j`? -/
partial def hasJumpTo (j : FVarId) : Code .pure → Bool
  | .jmp j' _ => j == j'
  | .let _ k => hasJumpTo j k
  | .fun d k _ | .jp d k => hasJumpTo j d.value || hasJumpTo j k
  | .cases c => c.alts.any (hasJumpTo j ·.getCode)
  | _ => false

/-- Place join point `d` (whose scope is `k`) as deep as possible: into the
single branch, join-point body or continuation containing all its jumps.
Free variables of `d` stay in scope (binders are unique), and code does not
grow. Sunk into the subtree its jumps come from, a join point is more often
structured (J2) instead of outlined: an outlined join point that calls the
enclosing function back makes a loop mutually recursive, which LLVM does not
turn into a loop. -/
partial def sinkInto (d : FunDecl .pure) (k : Code .pure) : Code .pure :=
  let j := d.fvarId
  match k with
  | .let x k' => .let x (sinkInto d k')
  | .fun f k' _ => if hasJumpTo j f.value then .jp d k else .fun f (sinkInto d k')
  | .jp d2 k2 =>
    match hasJumpTo j d2.value, hasJumpTo j k2 with
    | true, true => .jp d k
    | true, false => .jp (FunDecl.mk d2.fvarId d2.binderName d2.params d2.type (sinkInto d d2.value)) k2
    | false, true => .jp d2 (sinkInto d k2)
    | false, false => k
  | .cases c =>
    if (c.alts.filter (hasJumpTo j ·.getCode)).size == 1 then
      .cases ⟨c.typeName, c.resultType, c.discr, c.alts.map fun alt =>
        if hasJumpTo j alt.getCode then
          match alt with
          | .alt ctor ps code _ => .alt ctor ps (sinkInto d code)
          | .default code => .default (sinkInto d code)
          | other => other
        else alt⟩
    else .jp d k
  | _ => .jp d k

/-- Sink every join point of `c` (innermost first). -/
partial def sinkJoinPoints : Code .pure → Code .pure
  | .let x k => .let x (sinkJoinPoints k)
  | .fun d k _ =>
    .fun (FunDecl.mk d.fvarId d.binderName d.params d.type (sinkJoinPoints d.value)) (sinkJoinPoints k)
  | .jp d k =>
    sinkInto (FunDecl.mk d.fvarId d.binderName d.params d.type (sinkJoinPoints d.value)) (sinkJoinPoints k)
  | .cases c =>
    .cases ⟨c.typeName, c.resultType, c.discr, c.alts.map fun
      | .alt ctor ps code _ => .alt ctor ps (sinkJoinPoints code)
      | .default code => .default (sinkJoinPoints code)
      | other => other⟩
  | c => c

/-- Registry entry point: sinking runs on every declaration's body before it
is lowered. -/
def Opt.JpSink.install (c : PassConfig) : PassConfig :=
  let prev := c.lower.prepareBody
  { c with lower := { c.lower with prepareBody := fun b => sinkJoinPoints (prev b) } }

end LeanToReussir
