import Lean
import LeanToReussir.PassConfig

/-!
# Small join points duplicated (optimization `jp-small`)

J1′ of the join-point strategy (translation plan §5.6): a join point whose
copy is small (at most 40 bindings, alternatives and exits, nested join
points included, and the bodies of the small join points it jumps to) and
that is not J2 is inlined at each of its jumps, like J1, instead of
outlined (J3). Without this pass such join points are outlined.
-/

namespace LeanToReussir
open Lean Compiler LCNF

/-- Size of a code block (bindings, alternatives and exits), counted up to
`cap`. -/
partial def codeSize (c : Code .pure) (cap : Nat) : Nat :=
  go c 0
where
  go (c : Code .pure) (acc : Nat) : Nat :=
    if acc ≥ cap then acc else
    match c with
    | .let _ k => go k (acc + 1)
    | .fun d k _ | .jp d k => go k (go d.value (acc + 1))
    | .cases cs => cs.alts.foldl (fun acc alt => go alt.getCode (acc + 1)) (acc + 1)
    | _ => acc + 1

/-- Size of what a copy of the join-point body `c` contains, counted up to
`cap`: its own nodes as `codeSize` counts them (join points nested in it
once), and at each jump to another join point of `bodies` (those in scope)
whose own body is small, that body, counted the same way: such a join point
is duplicated there too. Without them, the bound would not cover a chain of
sibling join points each jumping to two others (a sequence of `match`es
that pass a constructor on: each jump goes to an alternative of the next
`match`): every one of them small, the first one's copies would hold 2^n
copies of the last. -/
partial def copySize (bodies : Std.HashMap FVarId (Code .pure)) (c : Code .pure) (cap : Nat) : Nat :=
  go c {} 0
where
  /-- `inner`: the join points declared in the block being counted, whose
  bodies are counted with their declarations. -/
  go (c : Code .pure) (inner : FVarIdSet) (acc : Nat) : Nat :=
    if acc ≥ cap then acc else
    match c with
    | .let _ k => go k inner (acc + 1)
    | .fun d k _ => go k inner (go d.value inner (acc + 1))
    | .jp d k => go k (inner.insert d.fvarId) (go d.value inner (acc + 1))
    | .cases cs => cs.alts.foldl (fun acc alt => go alt.getCode inner (acc + 1)) (acc + 1)
    | .jmp j _ =>
      match bodies[j]? with
      | some b => if !inner.contains j && codeSize b 41 ≤ 40 then go b {} (acc + 1) else acc + 1
      | none => acc + 1
    | _ => acc + 1

/-- Small join points (nested join points included, since sinking nests
them, and the small join points they jump to, duplicated with them) are
duplicated at their jumps (like J1) rather than outlined: outlining one on
a loop's path makes the loop a state machine (J4) or mutually recursive
(J3), and keeps the reuse of cells matched before the jump from reaching
constructions after it. -/
def isSmallJp (bodies : Std.HashMap FVarId (Code .pure)) (d : FunDecl .pure) : Bool :=
  copySize bodies d.value 41 ≤ 40

/-- Registry entry point. -/
def Opt.JpSmall.install (c : PassConfig) : PassConfig :=
  let prev := c.lower.duplicateJp
  { c with lower := { c.lower with duplicateJp := fun bodies d => prev bodies d || isSmallJp bodies d } }

end LeanToReussir
