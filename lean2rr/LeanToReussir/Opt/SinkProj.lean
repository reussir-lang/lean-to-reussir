import Std.Data.HashSet
import LeanToReussir.RR
import LeanToReussir.PassConfig

/-!
# Field projections sunk into the branches that use them (optimization `sink-proj`)

A `cases` on a structure binds the fields the alternative uses at its top
(`let f = s.0;`, Lower's `lowerCases`). When the alternative then branches,
and a field is used only in some branches while another branch keeps the
structure whole (`if k == k' then (k', t.bump rest) :: more else (k', t) ::
go k rest more`: the pair `s` is stored again as it is), Reussir retains the
field before the branch and releases it in the branch that keeps `s`. That
release never frees anything (`s` still holds the field), but Reussir's
token reuse offers the field's cells as reuse tokens there, and they can
win over the cell the branch really frees: the branch then allocates a new
cell, and frees the matched one after its recursive call, which is no
longer a tail call (adv4 PF4-10; Reussir bug 7 is the same phantom-donor
class for match binders).

This pass moves such a projection into the branches that use it. A
projection `let x = s.j` of a block that ends in an `if` or `match` moves
when no later binding of the block and not the condition (scrutinee) uses
`x`, some branches use `x` and others do not, and one of those others uses
`s` whole. Values are immutable and a projection has no effect, so the
value is the same, and the field is only retained where it is used.
-/

namespace LeanToReussir.RR

/-- `bound` extended with the names arm `a` binds. -/
def Arm.bound (a : Arm) (bound : Std.HashSet String) : Std.HashSet String :=
  a.binders.foldl (fun b x => match x with | some x => b.insert x | none => b) bound

mutual
  /-- Free variables of `e` (names bound in `bound` excluded). -/
  partial def Expr.freeVars (e : Expr) (bound : Std.HashSet String) (acc : Std.HashSet String) :
      Std.HashSet String :=
    match e with
    | .var n => if bound.contains n then acc else acc.insert n
    | .atom _ => acc
    | .call _ _ args | .ctor _ _ args => args.foldl (fun acc a => a.freeVars bound acc) acc
    | .apply f a => a.freeVars bound (f.freeVars bound acc)
    | .field e _ | .cast e _ => e.freeVars bound acc
    | .lam x _ b => b.freeVars (bound.insert x) acc
    | .ite c t f => f.freeVars bound (t.freeVars bound (c.freeVars bound acc))
    | .mtch s arms => arms.foldl (fun acc arm => arm.body.freeVars (arm.bound bound) acc) (s.freeVars bound acc)
    | .block b => b.freeVars bound acc

  partial def Block.freeVars (b : Block) (bound : Std.HashSet String) (acc : Std.HashSet String) :
      Std.HashSet String :=
    let (bound, acc) := b.lets.foldl (fun (bound, acc) (x, _, e) => (bound.insert x, e.freeVars bound acc)) (bound, acc)
    b.result.freeVars bound acc
end

/-- The names an arm binds. -/
def Arm.binderSet (a : Arm) : Std.HashSet String :=
  a.binders.foldl (fun b x => match x with | some x => b.insert x | none => b) {}

/-- Sink the projections of block `b` into its final `if`/`match` (see
above). -/
def sinkHere (b : Block) : Block := Id.run do
  let (head, branches, binders) : Expr × Array Block × Array (Std.HashSet String) := match b.result with
    | .ite c t e => (c, #[t, e], #[{}, {}])
    | .mtch s arms => (s, arms.map (·.body), arms.map (·.binderSet))
    | _ => (.atom "", #[], #[])
  if branches.size < 2 then return b
  let mut fvs := (branches.zip binders).map fun (br, bs) => br.freeVars bs {}
  let headFv := head.freeVars {} {}
  let mut branches := branches
  let mut usedLater : Std.HashSet String := headFv
  let mut boundLater : Std.HashSet String := {}
  let mut kept : Array (String × Option Ty × Expr) := #[]
  for i in [:b.lets.size] do
    let (x, ty, e) := b.lets[b.lets.size - 1 - i]!
    let mut moved := false
    if let .field (.var s) _ := e then
      if !usedLater.contains x && !boundLater.contains s && !boundLater.contains x then
        let users := (List.range branches.size).filter fun k => fvs[k]!.contains x
        let keepsWhole := (List.range branches.size).any fun k => fvs[k]!.contains s && !fvs[k]!.contains x
        let clash := users.any fun k => binders[k]!.contains s || binders[k]!.contains x
        if !users.isEmpty && users.length < branches.size && keepsWhole && !clash then
          for k in users do
            branches := branches.set! k { branches[k]! with lets := #[(x, ty, e)] ++ branches[k]!.lets }
            fvs := fvs.set! k ((fvs[k]!.erase x).insert s)
          moved := true
    if !moved then
      kept := kept.push (x, ty, e)
      usedLater := e.freeVars {} usedLater
      boundLater := boundLater.insert x
  let result := match b.result with
    | .ite c _ _ => Expr.ite c branches[0]! branches[1]!
    | .mtch s arms => .mtch s ((arms.zip branches).map fun (a, br) => { a with body := br })
    | r => r
  return { lets := kept.reverse, result }

mutual
  partial def Expr.sinkProj (e : Expr) : Expr :=
    match e with
    | .call f ts args => .call f ts (args.map (·.sinkProj))
    | .apply f a => .apply f.sinkProj a.sinkProj
    | .ctor t v args => .ctor t v (args.map (·.sinkProj))
    | .field e i => .field e.sinkProj i
    | .cast e t => .cast e.sinkProj t
    | .lam x t b => .lam x t b.sinkProj
    | .ite c t f => .ite c.sinkProj t.sinkProj f.sinkProj
    | .mtch s arms => .mtch s.sinkProj (arms.map fun a => { a with body := a.body.sinkProj })
    | .block b => .block b.sinkProj
    | e => e

  /-- Sink projections in `b` and, below, in every nested block (outer
  blocks first, so a projection can move down several levels). -/
  partial def Block.sinkProj (b : Block) : Block :=
    let b := sinkHere b
    { lets := b.lets.map (fun (x, t, e) => (x, t, e.sinkProj)), result := b.result.sinkProj }
end

def Item.sinkProj : Item → Item
  | .fn n ps r body => .fn n ps r body.sinkProj
  | it => it

end LeanToReussir.RR

/-- Registry entry point: runs on every generated function. -/
def LeanToReussir.Opt.SinkProj.install (c : LeanToReussir.PassConfig) : LeanToReussir.PassConfig :=
  { c with rrPasses := c.rrPasses.push fun _ fns => fns.map (·.sinkProj) }
