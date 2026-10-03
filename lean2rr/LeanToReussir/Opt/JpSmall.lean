import Lean
import LeanToReussir.PassConfig

/-!
# Small join points duplicated (optimization `jp-small`)

J1′ of the join-point strategy (translation plan §5.6): a join point whose
body is small (at most 40 bindings, alternatives and exits, nested join
points included), whose copy, with the join points inlined into it,
expands to at most 480, whose copies beyond the first add at most 2000
(4000 for a loop's continuation), and that is not J2, is inlined at each of
its jumps, like J1, instead of outlined (J3). Without this pass such join
points are outlined.
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

/-- Size of the code a copy of the join-point body `c` can expand to,
counted up to `cap`, and whether the copy makes a tail call of a
declaration of `scope.loop` (the declaration's call cycle), that is,
whether it is a loop's continuation (exact when the size is below `cap`).

The size counts the bindings, alternatives and exits, and at each jump the
body of the join point jumped to when it may be inlined there (J1, J1′):
one declared in `c` (counted at each jump to it, not where it is
declared), or another join point in `scope` that is jumped to once (J1
inlines it whatever its size) or whose own body is small. Those bodies are
counted the same way. It is an upper bound (a J2 or outlined target costs
only its jump), and bounding it bounds what duplication produces: with the
bound on the own body alone, a chain of sibling join points each jumping to
two others (a sequence of `match`es that pass a constructor on: each jump
goes to an alternative of the next `match`) gave the first one's copies
2^n copies of the last; and without the join points jumped to once, a
large one whose jump is in a small duplicated join point was copied with
it (jp-sink, which puts it inside its jumper, off). -/
partial def copyInfo (scope : JpScope) (c : Code .pure) (cap : Nat) : Nat × Bool :=
  go c {} (0, false)
where
  /-- `inner`: the join points declared in the block being counted. -/
  go (c : Code .pure) (inner : Std.HashMap FVarId (Code .pure)) (st : Nat × Bool) : Nat × Bool :=
    let (acc, loops) := st
    if acc ≥ cap then st else
    match c with
    | .let d k =>
      let loops := loops || match d.value, k with
        | .const f _ _ _, .return x => x == d.fvarId && scope.loop.contains f
        | _, _ => false
      go k inner (acc + 1, loops)
    | .fun d k _ => go k inner (go d.value inner (acc + 1, loops))
    | .jp d k => go k (inner.insert d.fvarId d.value) (acc + 1, loops)
    | .cases cs => cs.alts.foldl (fun st alt => go alt.getCode inner (st.1 + 1, st.2)) (acc + 1, loops)
    | .jmp j _ =>
      match inner[j]? with
      | some b => go b inner (acc + 1, loops)
      | none =>
        match scope.bodies[j]? with
        | some b =>
          if scope.single.contains j || codeSize b 41 ≤ 40 then go b {} (acc + 1, loops)
          else (acc + 1, loops)
        | none => (acc + 1, loops)
    | _ => (acc + 1, loops)

/-- The most code a copy of a duplicated join point may expand to
(`copyInfo`): twelve times the bound on its own body. Loops whose
conditions are a few `&&`/`||` tests (each test a join point jumping to the
shared continuation) expand to 300-350 and stay plain loops. -/
def copyBudget : Nat := 480

/-- The most code the copies of a duplicated join point may add, beyond the
one copy that inlining a single jump makes: (jumps - 1) × its size. A join
point jumped to from the many alternatives of a wide `match` (a `match`
with 800 arms, each going on to an alternative of the next `match`: 260
jumps to copies of about 150 nodes) is outlined instead of copied into
every arm. -/
def copiesBudget : Nat := 2000

/-- The same for a loop's continuation (a copy that tail-calls a
declaration of the declaration's call cycle): after a `match` of up to
about 100 arms, a continuation of 30-40 nodes is still copied into each
arm. Outlined, it would make the loop a state machine, or, in mutual
recursion, use a stack frame more per iteration. -/
def loopCopiesBudget : Nat := 4000

/-- Small join points (nested join points included, since sinking nests
them) are duplicated at their jumps (like J1) rather than outlined:
outlining one on a loop's path makes the loop a state machine (J4) or
mutually recursive (J3), and keeps the reuse of cells matched before the
jump from reaching constructions after it. A copy, with the join points
inlined into it, must also stay within `copyBudget`, so that duplication
cannot multiply along a chain of join points, and all the copies within
`copiesBudget` (`loopCopiesBudget` for a loop's continuation), so that a
join point with many jumps is not copied to each. `jumps` is the number of
jumps to the join point. -/
def isSmallJp (scope : JpScope) (d : FunDecl .pure) (jumps : Nat) : Bool :=
  codeSize d.value 41 ≤ 40 &&
    let (size, loops) := copyInfo scope d.value (copyBudget + 1)
    size ≤ copyBudget && (jumps - 1) * size ≤ (if loops then loopCopiesBudget else copiesBudget)

/-- Registry entry point. -/
def Opt.JpSmall.install (c : PassConfig) : PassConfig :=
  let prev := c.lower.duplicateJp
  { c with lower := { c.lower with duplicateJp := fun scope d n => prev scope d n || isSmallJp scope d n } }

end LeanToReussir
