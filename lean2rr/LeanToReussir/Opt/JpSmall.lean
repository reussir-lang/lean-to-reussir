import Lean
import LeanToReussir.PassConfig

/-!
# Small join points duplicated (optimization `jp-small`)

J1′ of the join-point strategy (translation plan §5.6): a join point whose
body is small (at most 40 bindings, alternatives and exits, nested join
points included) and that is not J2 is inlined at each of its jumps, like
J1, instead of outlined (J3). Without this pass such join points are
outlined.
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

/-- Small join points (nested join points included, since sinking nests
them) are duplicated at their jumps (like J1) rather than
outlined: outlining one on a loop's path makes the loop a state machine
(J4) or mutually recursive (J3), and keeps the reuse of cells matched
before the jump from reaching constructions after it. -/
def isSmallJp (d : FunDecl .pure) : Bool := codeSize d.value 41 ≤ 40

/-- Registry entry point. -/
def Opt.JpSmall.install (c : PassConfig) : PassConfig :=
  let prev := c.lower.duplicateJp
  { c with lower := { c.lower with duplicateJp := fun d => prev d || isSmallJp d } }

end LeanToReussir
