import Lean
import LeanToReussir.Emit.Program
import Lean.Util.SCC

/-!
# Functions whose inlined copies would make one function too large

Part of the required practice `inline-anchors` (with `anchoredFns`).
rrc's MLIR inliner (Reussir's default inliner) inlines a callee of at most
256 operations at every call, however many calls there are, bottom-up:
a callee's own callees are inlined into it first. When one function calls
such callees from many places, every call gets a copy, and LLVM's passes
over the result are superlinear in the function's size. Example:
`RtJpWide`. Its 800-arm `match` on a `Nat` is
one function (`int-match`). The arms call three outlined join points (J3)
of about 160 operations, each one about 266 times. The copies made one LLVM
function of about a million blocks. LLVM's CorrelatedValuePropagation
builds the dominator tree again for each `switch` that it changes, and the
build took 740 s and 3.5 GB; with the three join points kept out of the
inliner, 5 s and 0.5 GB. lean2rr outlined those join points because their
copies would have been too much code (`jp-small`'s bound); the inliner then
copied them in again.

The rule. After `Outline` and the passes over the generated functions,
`copyAnchors` visits the generated functions callees first (one cycle of
the call graph at a time). At each function `g` it takes the functions
that `g` calls and that rrc can inline into it: not anchored, not refused
by the inliner (in `g`'s cycle of the call graph: `g` itself, a callee
that calls `g` back or calls itself), with a lower bound of their size at
most `copyAnchorInlineLimit` (256), and not small (size over
`copyAnchorSmallSize`, 32). Their copies beyond the first add

  Σ (calls of `f` in `g` - 1) × size of `f`

to `g`. While that is over `copyAnchorBudget` (4000), the callee that adds
the most is kept out of rrc's inliner (`#[transform_anchor]`).
- Two sizes, in lean2rr's count of the operations that rrc makes of a
  function's code (`fnSize`, `exprSize`). The size of a copy (`cost`) is
  the own size plus a copy of each function that rrc may inline into it
  first (the inliner works bottom-up), at most 256 a copy: so a wrapper of
  a few operations that calls a mid-size function once counts as mid-size
  (`RtCopyAnchors`' `wrap`). The size that decides whether rrc can inline
  a function at all (`low`) leaves out the callees that rrc may not inline
  into it (recursive ones): so a function that is mid-size on its own and
  calls a recursive function once is still inlinable, and its copies count
  (`RtCopyAnchors`' `mid`, whose `cost` is over 256, shown as 256). Both
  leave out the functions anchored so far. A function that a later caller
  anchors can still count in a size computed before: `cost` is then too
  large (more anchoring: the safe side); for `low`, the pass is repeated,
  with every function anchored so far anchored from the start, until it
  anchors nothing new, so the last pass's `low` counts no anchored
  function. `RtJpWide`'s join points: 160 (rrc: about 180). `fnSize`
  counts fewer operations than rrc makes (no reference counting), so a
  function whose `low` is over 256 is taken to be over the inliner's
  limit, and its calls add no copies.
- A small function is never anchored: a copy is about as small as the
  call, and LLVM would inline it again anyway. (`RtJpAnchors`' `tiny`: a
  join point of size 23 called from 300 arms, 299 × 23 = 6877, over the
  budget, stays inlinable.)
- A function that calls itself is anchored like any other. MLIR's inliner
  does not inline a self-recursive function, but under `-O aggressive`
  Reussir's unique-carrying specialization (which runs before the inliner)
  can redirect its self calls to a specialized copy, after which the
  function is no longer recursive and is inlined (`RtCopyAnchors`'
  `build`).
- The copies are summed per caller, because the superlinear cost is in the
  size of one function: copies spread over many functions add code
  linearly (lean-zip's hash updates, `updateHashesMergedFast`, 226 calls
  in 61 functions, at most 20 in one). Several callees that each stay
  under the budget can be over it together (`RtCopyAnchors`' `sum3`: of
  three functions of size 175 called about 21 times each, two are kept
  out).
- The budget is `jp-small`'s bound for a loop's continuation
  (`loopCopiesBudget`, 4000 nodes): the most code that lean2rr's own copies
  of a join point may add. `RtJpWide`'s `match` gets about 127000; the same
  shape with 100 arms (33 calls a join point) about 15000 (rrc 18 s
  inlined, 0.4 s anchored).
- In a cycle of the call graph, MLIR's inliner refuses only a callee that
  calls itself or calls its caller back directly, and Reussir's declines
  only the calls that an inlining copied in: in a cycle of three or more
  functions, a function can be inlined into another one. Such calls count,
  with the callee's sizes before the cycle's decisions (its own size and
  the callees outside the cycle) (`RtCopyAnchors`' `fc`, in the cycle
  `fa` → `fb` → `fc` → `fa`, called from every arm of `fb`).

Out of line, a function costs a call at each call site. LLVM, which runs
after Reussir's passes, can still inline it (the anchor's `no_inline`
does not reach LLVM).

What: a translation-cost guard, not an optimization (it cannot be turned
off; `L2R_NO_INLINE_ANCHORS` turns it off with the other anchors, for
measurements; `L2R_DEBUG` prints its decisions). Remove only if: rrc's
inliner bounds the code that its copies add to one function (it counts no
calls on Reussir 00906e38).
-/

namespace LeanToReussir
open RR

/-- A function of at most this size (`fnSize`) is never kept out of rrc's
inliner for its copies. -/
def copyAnchorSmallSize : Nat := 32

/-- The most code (in `fnSize` units) that the copies beyond the first of
the callees that can be anchored may add to one function, together, before
the callee that adds the most is kept out of rrc's inliner (`jp-small`'s
`loopCopiesBudget`). -/
def copyAnchorBudget : Nat := 4000

mutual
  /-- About the number of operations rrc makes of `e` before inlining: one
  for each call, application, construction, projection, cast, literal or
  other atom, `if`, `match` and lambda, one per `match` arm and each value
  it binds, one per branch of an `if`; a variable is none. -/
  partial def exprSize (e : Expr) (acc : Nat) : Nat :=
    match e with
    | .var _ => acc
    | .atom _ => acc + 1
    | .call _ _ args | .ctor _ _ args => args.foldl (fun a x => exprSize x a) (acc + 1)
    | .apply f a => exprSize a (exprSize f (acc + 1))
    | .field x _ | .cast x _ => exprSize x (acc + 1)
    | .lam _ _ b => blockSize b (acc + 1)
    | .ite c t f => blockSize f (blockSize t (exprSize c (acc + 3)))
    | .mtch s arms =>
      arms.foldl (init := exprSize s (acc + 1)) fun a arm =>
        blockSize arm.body (a + 1 + arm.wrap.size + (arm.binders.filter (·.isSome)).size)
    | .block b => blockSize b acc
  partial def blockSize (b : Block) (acc : Nat) : Nat :=
    exprSize b.result (b.lets.foldl (fun a (_, _, e) => exprSize e a) acc)
end

/-- The size of a function's own code (`exprSize`). -/
def fnSize (body : Block) : Nat := blockSize body 0

/-- A function whose size (`CopyAnchor.size`: `fnSize` with what rrc
inlines into it) is over this bound is taken to be over the 256 operations
up to which rrc's inliner inlines a callee (`fnSize` counts fewer
operations than rrc makes: no reference counting), so it is not inlined,
and its calls add no copies. -/
def copyAnchorInlineLimit : Nat := 256

/-- The generated functions (`names`) that `body` calls, each with its
number of calls, in the order of their first call. -/
def calleeCounts (names : Std.HashSet String) (body : Block) : Array (String × Nat) := Id.run do
  let mut order : Array String := #[]
  let mut counts : Std.HashMap String Nat := {}
  for f in Outline.blockCalls body #[] do
    if !names.contains f then continue
    match counts[f]? with
    | some n => counts := counts.insert f (n + 1)
    | none =>
      order := order.push f
      counts := counts.insert f 1
  return order.map fun f => (f, counts.getD f 0)

/-- A function kept out of rrc's inliner for its copies (`copyAnchors`), or
a small one left to it although its copies are over the budget (`small`):
its size with what rrc inlines into it (`size`), its own size (`own`), and
its number of calls (`calls`) in the function `caller` that decided it. -/
structure CopyAnchor where
  fn : String
  size : Nat
  own : Nat
  calls : Nat
  caller : String

/-- The decisions of `copyAnchors`: the functions anchored, in the order
decided, and, for `L2R_DEBUG`, the small functions left inlinable whose
copies in one caller are over the budget, and the most code that the
copies of the callees that can be anchored add to one function before
anchoring, with that function (`largest`). -/
structure CopyAnchors where
  anchored : Array CopyAnchor := #[]
  small : Array CopyAnchor := #[]
  largest : Nat × String := (0, "")

/-- The generated functions and their calls (`calleeCounts`): each
function's own size (`fnSize`), the functions it calls (with the number of
calls, and as a set), the cycles of the call graph callees first
(`Lean.SCC.scc`, Tarjan's algorithm), and the functions that are recursive
(in a cycle of two or more, or calling themselves). -/
structure CallGraph where
  own : Std.HashMap String Nat := {}
  callees : Std.HashMap String (Array (String × Nat)) := {}
  calls : Std.HashMap String (Std.HashSet String) := {}
  comps : List (List String) := []
  recursive : Std.HashSet String := {}

/-- The `CallGraph` of the generated functions `fns`. -/
def callGraph (fns : Array Item) : CallGraph := Id.run do
  let nameSet : Std.HashSet String := fns.foldl (init := {}) fun s it => match it with
    | .fn n .. => s.insert n
    | _ => s
  let mut names : Array String := #[]
  let mut g : CallGraph := {}
  for it in fns do
    let .fn n _ _ body := it | continue
    if g.own.contains n then continue
    names := names.push n
    let cs := calleeCounts nameSet body
    g := { g with own := g.own.insert n (fnSize body), callees := g.callees.insert n cs,
                  calls := g.calls.insert n (cs.foldl (fun s (f, _) => s.insert f) {}) }
  let comps := Lean.SCC.scc names.toList fun f => ((g.callees.getD f #[]).map (·.1)).toList
  let mut recursive : Std.HashSet String := {}
  for comp in comps do
    match comp with
    | [f] => if (g.calls.getD f {}).contains f then recursive := recursive.insert f
    | _ => for f in comp do recursive := recursive.insert f
  return { g with comps, recursive }

/-- Whether rrc's inliner refuses to inline `h` into `g`, both in one cycle
of the call graph: `h` is `g`, calls `g` back, or calls itself (MLIR's
`Inliner::Impl::shouldInline`). -/
def CallGraph.refused (cg : CallGraph) (g h : String) : Bool :=
  h == g || (cg.calls.getD h {}).contains g || (cg.calls.getD h {}).contains h

/-- One pass of `copyAnchors`, with the functions of `pre` anchored from the
start: the decisions (the functions anchored in this pass, the small ones
left over the budget, the largest sum) and all the anchored functions.
Two sizes per function (`fnSize` units, a copy counting at most
`copyAnchorInlineLimit`):
- `cost`, what a copy of it costs: its own size plus a copy of each
  function that rrc may inline into it (not anchored, `low` at most the
  limit; in its cycle, one that the inliner does not refuse, `refused`);
- `low`, a lower bound for the test whether rrc can inline it: its own size
  plus a copy of each callee that rrc surely inlines into it (not anchored,
  not recursive, `low` at most the limit).
A function whose `low` is over the limit is not inlined; its calls add no
copies. In a cycle, the sizes of its functions before the cycle's
decisions (own size and the callees outside it) are those of the copies
inside it. -/
def copyAnchorPass (cg : CallGraph) (pre : Std.HashSet String) : CopyAnchors × Std.HashSet String := Id.run do
  let lim := copyAnchorInlineLimit
  let mut anchored := pre
  let mut cost : Std.HashMap String Nat := {}
  let mut low : Std.HashMap String Nat := {}
  let mut out : CopyAnchors := {}
  for comp in cg.comps do
    let inComp : Std.HashSet String := comp.foldl (·.insert ·) {}
    -- Sizes before the cycle's decisions: own size and the callees outside it.
    for g in comp do
      let mut c := cg.own.getD g 0
      let mut l := c
      for (h, n) in cg.callees.getD g #[] do
        if inComp.contains h || anchored.contains h || low.getD h 0 > lim then continue
        c := c + n * min (cost.getD h 0) lim
        if !cg.recursive.contains h then l := l + n * low.getD h 0
      cost := cost.insert g c
      low := low.insert g l
    for g in comp do
      let mut cands : Array (String × Nat × Nat) := #[]
      let mut total := 0
      for (h, n) in cg.callees.getD g #[] do
        if n ≤ 1 || anchored.contains h || low.getD h 0 > lim then continue
        if inComp.contains h && cg.refused g h then continue
        let e := min (cost.getD h 0) lim
        if e ≤ copyAnchorSmallSize then
          if (n - 1) * e > copyAnchorBudget then
            out := { out with small := out.small.push { fn := h, size := e, own := cg.own.getD h 0, calls := n, caller := g } }
          continue
        cands := cands.push (h, e, n)
        total := total + (n - 1) * e
      if total > out.largest.1 then out := { out with largest := (total, g) }
      if total ≤ copyAnchorBudget then continue
      let adds (c : String × Nat × Nat) : Nat := (c.2.2 - 1) * c.2.1
      let sorted := cands.qsort fun a b => adds a > adds b || (adds a == adds b && a.1 < b.1)
      for c@(h, e, n) in sorted do
        if total ≤ copyAnchorBudget then break
        anchored := anchored.insert h
        out := { out with anchored := out.anchored.push { fn := h, size := e, own := cg.own.getD h 0, calls := n, caller := g } }
        total := total - adds c
    -- The cost of the cycle's functions with the copies the inliner makes
    -- inside the cycle (their `low` stays: recursive callees are left out).
    if comp.length > 1 then
      let before := cost
      for g in comp do
        let mut c := before.getD g 0
        for (h, n) in cg.callees.getD g #[] do
          if !inComp.contains h || anchored.contains h || cg.refused g h || low.getD h 0 > lim then continue
          c := c + n * min (before.getD h 0) lim
        cost := cost.insert g c
  return (out, anchored)

/-- The generated functions of `p` that `inline-anchors` keeps out of rrc's
inliner for their copies (see the module comment), not anchored already:
`copyAnchorPass` again, with all the functions anchored so far anchored
from the start, until a pass anchors nothing new. Then the last pass's
`low` counts no function that ends up anchored (a later caller's decision
in the same pass); the decisions of the earlier passes stay. The small
functions over the budget and the largest sum are those of the first
pass. Linear in the program's size per pass (but for sorting
each function's callees); a pass beyond the first only follows a pass
that anchored something. -/
def LoweredProgram.copyAnchors (p : LoweredProgram) : CopyAnchors := Id.run do
  let cg := callGraph p.fns
  let (first, a) := copyAnchorPass cg p.anchored
  let mut out := first
  let mut anchored := a
  let mut fresh := first.anchored.size
  for _ in [0:cg.own.size] do
    if fresh == 0 then break
    let (d, a) := copyAnchorPass cg anchored
    out := { out with anchored := out.anchored ++ d.anchored }
    anchored := a
    fresh := d.anchored.size
  return out

/-- `p` with `copyAnchors` anchored too, and the decisions. -/
def LoweredProgram.anchorCopies (p : LoweredProgram) : LoweredProgram × CopyAnchors :=
  let d := p.copyAnchors
  ({ p with anchored := d.anchored.foldl (fun s a => s.insert a.fn) p.anchored }, d)

end LeanToReussir
