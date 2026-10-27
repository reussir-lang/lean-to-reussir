import Std.Data.HashMap
import Std.Data.HashSet
import LeanToReussir.RR
import LeanToReussir.Emit.Program

/-!
# Values that die at the start of a branch are released in native Lean's order

When several values die at the start of a branch (the arm of a `match`,
a branch of an `if`: values that another branch uses and this one does
not), native Lean releases them there, newest first: its
`ExplicitRC.addPrologForAlt` sorts them by their index, which counts the
variables in binding order, and prepends a `dec` for each. A `cases` with
two or more alternatives gives its scrutinee a new index in the
alternative of a constructor (`withCtorAlt`), the newest so far: there, a
scrutinee whose fields the alternative does not read is released first,
and in branches nested in that alternative it counts as bound at the
`cases`. In the default alternative (`_`) it keeps its index. A scrutinee
whose fields the alternative reads (a scalar field too) stays live there
until its last projection, so it is released after the alternative's other
releases. (A `cases` with one alternative left, a structure's, is no
`cases` natively, `simpCase`: no new index.)

Reussir releases the values that die at an arm's start oldest first (in
the order of its variables), and a matched value that dies in the match
before all of them, after the fields the arm reads are retained. Only
resources can tell (plan §5.8, "Release order at the start of a branch"):
a handle closes and flushes its buffer when released, and the last
reference to an unresolved promise resolves its `result?` task with
`none`, which runs its `sync` dependents. Two handles that die at a
branch's start wrote `12` to their file, natively `21`; a matched value
holding a handle `S` in a field the arm does not read, with two other
handles that die there, `S12`, natively `21S`.

So, in a program that makes resources, lean2rr releases such values
itself where the order shows, with `l2r_release_after` (an effectful FFI
call that consumes the value: Reussir takes it as the value's last use and
adds no release of its own), as it emulates Lean's borrowed parameters
(Lower/Borrow). This step of the core runs over the generated functions
right after `Outline`, before the optional passes over them, and computes
Reussir's liveness on them (free variables; the rules of Reussir's
`ownership.rs` for `If`, `Match` and argument lists): the values that die
at an arm's start are those that the other arms use and this one does
not, and that the code after the `if` or `match` does not use. Of these it
takes the recorded ones (`LoweredProgram.armNames`: every name the
lowering gave a variable of `armReleaseVars`, Lower/Borrow, one that may
hold a resource by the rule of the borrow emulation, `mayHoldAt`: the flow
analysis, which follows closures, thunks and tasks, or in a program that
casts the type, where every closure, thunk and task may; and that the code
owns), and releases them at the arm's start, newest first, when there are
at least two. Order: each name has its Lean variable's
binding order (its place in the declaration's code, the order of native
Lean's indices), also a name lean2rr gives the variable later (a field
converted to its own type, a field `lazy-fields` binds where it is used, a
join point's parameter at an inlined jump), in a function and in the
functions cut out of it (`Outline`, the join points J3 and the state
machines J4); a matched value counts as bound at the `match` in a
constructor's arm and below it.

The scrutinee `s` of a `match`, when it is recorded and dies in the match:
- in an arm that reads none of its fields, it is released with the
  others: first in a constructor's arm, by its binding order in the
  default arm. While no arm of the match releases `s` itself (and no arm
  uses it), Reussir consumes it in the match and releases it first in each
  arm (before the arm's own releases), which is native's order in a
  constructor's arm;
- in an arm that reads a field, it is released after the others, when a
  field the arm does not read may hold a resource
  (`LoweredProgram.armFields`; otherwise its release frees nothing that
  shows).
Once an arm releases `s` itself, Reussir borrows it for the whole `match`
and releases it with the other values that die in each arm that does not
use it, oldest first: so then `s` is ordered in every arm where it dies with
another recorded value. The values that are not recorded hold no resource
(or someone else holds them), so their order does not show, but for a pure
task, whose release time is lean2rr's (plan §10, "Release time of pure
tasks"; it is recorded only in a program that casts, by type).

The optional passes after it keep the order: `sink-proj` moves a
structure's projection into the branches that use the projected value, and
a release counts as such a use (its projection comes first, then the
releases in their order); `merge-fns` merges only functions whose code,
releases included, is the same up to names. Programs that make no
resources come out unchanged, and so do arms where fewer than two such
values die. Arms that only reach `l2r_unreachable` are left alone. Not
emulated (plan §10, "Release order at the start of a branch"): natively
Lean's `pushProj` moves the projections at an alternative's start into the
branches of a `cases` that follows at once, so the scrutinee dies in the
branches that read no field (at their start) and after the projection in
the others, where lean2rr releases it at the arm's start; a `cases` whose
alternatives `simpCase` folds into a default alternative only after
`toImpure` keeps its scrutinee's index there; a join point's body that
lean2rr places under a `match` (J1, J1′) counts the scrutinee as bound
there. (A structure that `flatten-structs` splits into its fields holds
nothing whose release shows: the flow analysis follows closures, thunks and
tasks, and so does the type rule of a program that casts.)
-/

namespace LeanToReussir.ArmRelease
open RR

abbrev Names := Std.HashSet String

/-- What the lowering recorded (`LoweredProgram.armNames`, `armFields`). -/
structure Info where
  /-- Name ↦ (type, the binding order of its Lean variable). -/
  names : Std.HashMap String (Ty × Nat)
  fields : Std.HashMap (String × String) (Array Bool)

/-- The free names of a `.var` operand: the name, or the identifiers of a
verbatim operand (`L2RUnit::u{}`; `atomIdents`), as `Outline.exprFvs` reads them. -/
def varNames (n : String) : Names :=
  if n.all (fun c => c.isAlphanum || c == '_') then ({} : Names).insert n
  else (atomIdents n).foldl (·.insert ·) {}

/-- `a` with the names of `b` added. -/
@[inline] def union (a b : Names) : Names :=
  if a.size < b.size then a.fold (·.insert ·) b else b.fold (·.insert ·) a

/-- Whether `v` is in one of the layers of the live set `L` (the
continuation's free names, a layer per enclosing level). -/
@[inline] def live (L : List Names) (v : String) : Bool := L.any (·.contains v)

/-- A block that only reaches `l2r_unreachable`. -/
def unreachableBlock (b : Block) : Bool :=
  b.lets.isEmpty && b.result matches .call "l2r_unreachable" _ _

/-- Where the code being visited is: the names live after it (`L`), the
largest binding order of a recorded name bound on the way to it (`top`: the
recorded names in scope come up to it), and the order keys of the matched
values that a `match` it is in renumbered (`moved`: name ↦ order key). -/
structure Pos where
  L : List Names
  top : Nat
  moved : Std.HashMap String Nat := {}

/-- The binding order of recorded name `v`. -/
def Info.order (I : Info) (v : String) : Nat := ((I.names.get? v).map (·.2)).getD 0

/-- The order key of name `v` at `p`: twice its binding order, or the key a
`match` gave it (odd: between the names bound before the `match` and
those bound in its arm). Newest is largest. -/
def Info.key (I : Info) (p : Pos) (v : String) : Nat := p.moved.getD v (2 * I.order v)

/-- `p` with names `xs` bound. -/
def Info.bind (I : Info) (p : Pos) (xs : Array String) : Pos :=
  { p with top := xs.foldl (fun m x => if I.names.contains x then max m (I.order x) else m) p.top }

abbrev M := StateM Nat

/-- `b` with `vs` released at its start, in that order, when there are at
least two. -/
def releaseAt (I : Info) (vs : Array String) (b : Block) : M Block := do
  if vs.size < 2 then return b
  let mut lets := #[]
  for v in vs do
    let k ← get
    set (k + 1)
    lets := lets.push (s!"l2rrel{k}", some (Ty.named "u64"),
      Expr.call "l2r_release_after" #[((I.names.get? v).map (·.1)).getD .unit] #[.var v])
  return { b with lets := lets ++ b.lets }

/-- Names with their order keys, newest first. -/
def newestFirst (vs : Array (String × Nat)) : Array String :=
  (vs.qsort fun a b => a.2 > b.2 || (a.2 == b.2 && a.1 < b.1)).map (·.1)

mutual
  /-- `e` with the releases added in its branches, and its free names. -/
  partial def goExpr (I : Info) (e : Expr) (p : Pos) : M (Expr × Names) := do
    match e with
    | .var n => return (e, varNames n)
    | .atom t => return (e, (atomIdents t).foldl (·.insert ·) {})
    | .call f tys args =>
      let (args, fv) ← goArgs I args p
      return (.call f tys args, fv)
    | .ctor t v args =>
      let (args, fv) ← goArgs I args p
      return (.ctor t v args, fv)
    | .apply f a =>
      let (args, fv) ← goArgs I #[f, a] p
      return (.apply args[0]! args[1]!, fv)
    | .field x i =>
      let (x, fv) ← goExpr I x p
      return (.field x i, fv)
    | .cast x t =>
      let (x, fv) ← goExpr I x p
      return (.cast x t, fv)
    | .lam x t b =>
      -- A closure's body is a scope of its own: its captures and its
      -- parameter are owned on entry.
      let (b, fv) ← goBlock I b (I.bind { p with L := [] } #[x])
      return (.lam x t b, fv.erase x)
    | .block b =>
      let (b, fv) ← goBlock I b p
      return (.block b, fv)
    | .ite c t f =>
      let (t, ft) ← goBlock I t p
      let (f, ff) ← goBlock I f p
      let (c, fc) ← goExpr I c { p with L := ft :: ff :: p.L }
      -- Reussir's [If-Reconcile]: a branch releases what the other uses,
      -- it does not, and the code after the `if` does not.
      let dying (other own : Names) : Array String :=
        newestFirst <| other.fold (init := #[]) fun acc v =>
          if I.names.contains v && !own.contains v && !live p.L v then acc.push (v, I.key p v) else acc
      let t ← if unreachableBlock t then pure t else releaseAt I (dying ff ft) t
      let f ← if unreachableBlock f then pure f else releaseAt I (dying ft ff) f
      return (.ite c t f, union fc (union ft ff))
    | .mtch s arms => goMatch I s arms p

  /-- Call arguments, evaluated in order: the later arguments are live
  after each one (Reussir's [Args]). -/
  partial def goArgs (I : Info) (args : Array Expr) (p : Pos) : M (Array Expr × Names) := do
    let mut acc : Names := {}
    let mut out := args
    for h : k in [:args.size] do
      let i := args.size - 1 - k
      let (a, fa) ← goExpr I args[i]! { p with L := acc :: p.L }
      out := out.set! i a
      acc := union acc fa
    return (out, acc)

  /-- A block: each `let`'s value with the rest of the block live after it,
  and the names bound before it in scope. -/
  partial def goBlock (I : Info) (b : Block) (p : Pos) : M (Block × Names) := do
    -- The largest binding order of a recorded name bound before each `let`
    -- (and before the result).
    let tops := b.lets.foldl (init := #[p.top]) fun ts (x, _, _) =>
      ts.push (if I.names.contains x then max ts.back! (I.order x) else ts.back!)
    let (r, fr) ← goExpr I b.result { p with top := tops.back! }
    let mut acc := fr
    let mut lets := b.lets
    for h : k in [:b.lets.size] do
      let i := b.lets.size - 1 - k
      let (x, t, e) := b.lets[i]!
      acc := acc.erase x
      let (e, fe) ← goExpr I e { p with L := acc :: p.L, top := tops[i]! }
      lets := lets.set! i (x, t, e)
      acc := union acc fe
    return (⟨lets, r⟩, acc)

  /-- A `match`: Reussir's reconciliation per arm (`place_leaf`), with the
  scrutinee's rules of the module comment. -/
  partial def goMatch (I : Info) (s : Expr) (arms : Array Arm) (p : Pos) : M (Expr × Names) := do
    let sv? : Option String := match s with
      | .var n => if I.names.contains n then some n else none
      | _ => none
    -- A `cases` natively when two or more arms can run: in a
    -- constructor's arm the scrutinee counts as bound here.
    let real := (arms.filter fun a => !unreachableBlock a.body).size
    let posOf (arm : Arm) : Pos :=
      let q := I.bind p (arm.binders.filterMap id)
      match sv?, arm.ctor with
      | some sv, some _ => if real ≥ 2 then { q with moved := q.moved.insert sv (2 * p.top + 1) } else q
      | _, _ => q
    let mut bodies : Array Block := #[]
    -- Each arm's body's free names (binders included), and the arm's own.
    let mut fbs : Array Names := #[]
    let mut fas : Array Names := #[]
    let mut treeFree : Names := {}
    for arm in arms do
      let (b, fb) ← goBlock I arm.body (posOf arm)
      let fa := arm.binders.foldl (fun acc x => match x with | some x => acc.erase x | none => acc) fb
      bodies := bodies.push b
      fbs := fbs.push fb
      fas := fas.push fa
      treeFree := union treeFree fa
    let (s', fs) ← goExpr I s { p with L := treeFree :: p.L }
    -- The values that may hold a resource and die in the match.
    let cands : Array String := treeFree.fold (init := #[]) fun acc v =>
      if I.names.contains v && !live p.L v then acc.push v else acc
    -- The scrutinee, when it may hold a resource and dies in the match.
    let sd? := sv?.filter (!live p.L ·)
    -- Per arm: the other values that die at its start, and the
    -- scrutinee's place there (`pre`: with them, `post`: after them).
    let mut dyings : Array (Array String) := #[]
    let mut pres : Array Bool := #[]
    let mut posts : Array Bool := #[]
    for h : i in [:arms.size] do
      let arm := arms[i]
      let fa := fas[i]!
      let fb := fbs[i]!
      dyings := dyings.push (cands.filter fun v => !fa.contains v && some v != sd?)
      match sd? with
      | some sv =>
        let reads := arm.binders.any fun x => match x with | some x => fb.contains x | none => false
        let flags? := arm.ctor.bind fun c => I.fields[(sv, c)]?
        let anyMay := match flags? with
          | some fl => fl.any id
          | none => true
        let unreadMay := match flags? with
          | some fl => (List.range fl.size).any fun j => fl[j]! &&
              match arm.binders[j]? with
              | some (some x) => !fb.contains x
              | _ => true
          | none => true
        let dies := !fa.contains sv
        pres := pres.push (dies && !reads && anyMay)
        posts := posts.push (dies && reads && unreadMay)
      | none =>
        pres := pres.push false
        posts := posts.push false
    -- The scrutinee's order key in each arm.
    let keys : Array Nat := arms.map fun arm => match sd? with
      | some sv => I.key (posOf arm) sv
      | none => 0
    -- Whether the pass releases the scrutinee in some arm (then Reussir
    -- borrows it for the match), or an arm uses it already.
    let explicit := match sd? with
      | some _ => (List.range arms.size).any fun i =>
          !unreachableBlock bodies[i]! &&
          ((posts[i]! && !dyings[i]!.isEmpty) ||
           (pres[i]! && dyings[i]!.any fun v => I.key p v > keys[i]!))
      | none => false
    let borrowed := match sd? with
      | some sv => explicit || treeFree.contains sv
      | none => false
    let mut out := #[]
    for h : i in [:arms.size] do
      let arm := arms[i]
      let body := bodies[i]!
      if unreachableBlock body then
        out := out.push { arm with body }
        continue
      let others := dyings[i]!.map fun v => (v, I.key p v)
      let vs : Array String := match sd?, borrowed with
        | some sv, true =>
          newestFirst (if pres[i]! then others.push (sv, keys[i]!) else others) ++
            (if posts[i]! then #[sv] else #[])
        | _, _ => newestFirst others
      out := out.push { arm with body := ← releaseAt I vs body }
    return (.mtch s' out, union fs treeFree)
end

/-- Every generated function, with releases at the start of its branches:
its body, with its parameters in scope and nothing live after it. -/
def armReleaseFns (I : Info) (fns : Array Item) : Array Item :=
  let go : M (Array Item) := fns.mapM fun it => match it with
    | .fn n ps r body => do
      let start : Pos := I.bind { L := [], top := 0 } (ps.map (·.1))
      return .fn n ps r (← goBlock I body start).1
    | it => pure it
  go.run' 0

end ArmRelease

/-- The release order at the start of a branch (see above): in a program
that makes resources (`armNames` not empty), every generated function. -/
def LoweredProgram.armRelease (p : LoweredProgram) : LoweredProgram :=
  if p.armNames.isEmpty then p else
  { p with fns := ArmRelease.armReleaseFns { names := p.armNames, fields := p.armFields } p.fns }

end LeanToReussir
