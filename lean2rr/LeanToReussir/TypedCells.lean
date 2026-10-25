import Lean
import LeanToReussir.CellKinds
import LeanToReussir.CompactArrays
import LeanToReussir.Collect

/-!
# The whole-program check of typed references (optimization `typed-cells`)

With optimization `typed-cells` (clean step B2), the cell of a reference
of element type `X` holds `X`'s own Reussir type `T` when `X`'s cell kind
(`CellKinds.lean`) is on: the reference is the record `L2RRef…(Cell<T>)`,
one record type per `T`, and `set`, `get`, `take` and `swap` move values of
type `T` with no box. Every other reference keeps the cell of `Box`es
(`refType`, rule 1).

Lean's mono phase types every reference `lcAny`, so a reference travels in
a `Box`, and each operation unboxes it at its own record type: the box's
payload number tells the record types apart, so a reference unboxed at
another record type stops the program (`l2r_unreachable`), never reads a
cell of another type. This check makes that impossible.

A reference is made by one primitive (`ST.Prim.mkRef`) and used by five
(`get`, `set`, `swap`, `take`, `ptrEq`), each an extern instance whose type
arguments are known (`InstKey`). A reference made at element type `M`
reaches an operation at element type `O` only if `M` and `O` can be one
type up to `lcAny` (`cellTypesMeet`, on mono types; and `cellBaseApart`,
on the type arguments before mono, where a reference, a promise or a
handle still has its own head instead of `lcAny`): the program is typed,
and Stage 1 replaces a type variable by a type or by `lcAny` (an
existential's type, a uniform instance, polymorphic recursion), never by an
unrelated type. A
cast is the exception (`programCasts`): then every kind is off. So for
every pair of a make and an operation whose types can meet, both must have
one representation (both cells typed at one kind, or both of `Box`es);
otherwise both kinds are turned off, until no pair differs. An operation
at `lcAny` (an existential package's reference) thus turns off every kind
whose references it can meet, which is every kind.

A kind is also turned off when its element type can hold a value whose
release the program can observe (`releaseUnsafe?`, the rule of typed
arrays): a typed cell's value is released by Reussir's own drop when the
reference dies, in Reussir's field order, where a box's release follows
Lean's order.
-/

namespace LeanToReussir
open Lean Compiler LCNF

/-- The primitive that makes a reference. -/
def refMakePrim : Name := ``ST.Prim.mkRef

/-- The primitives that operate on a reference. -/
def refOpPrims : List Name :=
  [``ST.Prim.Ref.get, ``ST.Prim.Ref.set, ``ST.Prim.Ref.swap, ``ST.Prim.Ref.take, ``ST.Prim.Ref.ptrEq]

/-- What the check decided: the cell kinds of references whose cells are
typed, and why each other kind seen is off. -/
structure TCResult where
  refOn : Array String := #[]
  refOff : Array (String × String) := #[]

/-- Whether a reference of element type `a` and one of element type `b`,
the instances' type arguments as Stage 1 gives them (before mono), can
never be one reference: at some position that both reach through one
inductive head, they have two different *rigid* heads (an inductive or an
opaque type; not `lcAny`, `◾`, a cast target `NonScalar`/`PNonScalar`, a
definition or a variable), one of which mono represents by `lcAny` or by
another type that `Box` stands for (`mayBeBox`): a reference, a promise, a
handle. Mono's types cannot tell such a type from any
other (`cellTypesMeet` takes `lcAny` to meet everything), but two types
with different rigid heads are never one type, so no reference has both
(a cast aside: `programCasts`). Says `false` when unsure. -/
partial def cellBaseApart (a b : Expr) (fuel : Nat := 32) : CoreM Bool := do
  let a := a.consumeMData.headBeta
  let b := b.consumeMData.headBeta
  if a == b then return false
  let fuel' + 1 := fuel | return false
  let env ← getEnv
  let rigid (n : Name) : Bool :=
    !(n == ``lcAny || n == ``lcErased || n == ``lcVoid || isUniformConst n) &&
      (match env.find? n with
       | some (.inductInfo _) | some (.opaqueInfo _) => true
       | _ => false)
  let .const m _ := a.getAppFn | return false
  let .const n _ := b.getAppFn | return false
  unless rigid m && rigid n do return false
  if !sameInductive m n then
    -- Apart when mono loses one of the two types.
    let lost (t : Expr) : CoreM Bool := do
      let mt := keyTy (← toMonoTypeKeep t)
      return mt == anyExpr || (!mt.isForall && !mt.isErased && mayBeBox env mt)
    return (← lost a) || (← lost b)
  if a.getAppNumArgs != b.getAppNumArgs then return false
  for (x, y) in a.getAppArgs.zip b.getAppArgs do
    if ← cellBaseApart x y fuel' then return true
  return false

/-- The whole-program check (see the module comment) over the program's
declarations `decls` (extern instances included) with their instance keys,
given whether the program can cast (`casts`) and the array decisions (the
compact storage kinds `compactOn` and the typed pointer kinds `typedOn`,
which give an array's cell kind). -/
def typedRefKinds (decls : Array (Decl .pure)) (keys : NameMap InstKey) (casts : Option Name)
    (compactOn : Array String) (typedOn : Std.HashSet String) : CoreM TCResult := do
  let env ← getEnv
  -- The element types of the references made and of the operations, as
  -- the instances' type arguments give them (`lcAny` where unknown), each
  -- with an instance for the report.
  let mut makes : Std.HashMap Expr Name := {}
  let mut ops : Std.HashMap Expr Name := {}
  for d in decls do
    match d.value with
    | .extern _ =>
      let k := keys.find? d.name
      let orig := (k.map (·.decl)).getD d.name
      let isMake := orig == refMakePrim
      unless isMake || refOpPrims.contains orig do continue
      let t := ((k.bind (·.typeArgs[1]?)).map (·.consumeMData)).getD anyExpr
      if isMake then
        unless makes.contains t do makes := makes.insert t d.name
      else
        unless ops.contains t do ops := ops.insert t d.name
    | .code c =>
      -- A primitive called by its own name (no instance): its element
      -- type is unknown.
      for f in codeConsts c #[] do
        if f == refMakePrim then
          unless makes.contains anyExpr do makes := makes.insert anyExpr d.name
        else if refOpPrims.contains f then
          unless ops.contains anyExpr do ops := ops.insert anyExpr d.name
  if makes.isEmpty && ops.isEmpty then return {}
  let cache ← IO.mkRef {}
  -- Each type argument with its mono type, which gives the kind.
  let withMono (m : Std.HashMap Expr Name) : CoreM (Array (Expr × Expr × Name)) := do
    let sorted := m.toArray.qsort fun a b => toString a.1 < toString b.1
    sorted.mapM fun (t, w) => return (t, keyTy (← toMonoTypeKeep t), w)
  let makesL ← withMono makes
  let opsL ← withMono ops
  let mut kinds : Std.HashMap Expr (Option String) := {}
  let mut seen : Array String := #[]
  let mut off : Std.HashMap String String := {}
  for (_, t, _) in makesL ++ opsL do
    if kinds.contains t then continue
    let k ← cellKind? cache compactOn typedOn t
    kinds := kinds.insert t k
    let some k := k | continue
    unless seen.contains k do seen := seen.push k
    if off.contains k then continue
    if let some n := casts then
      off := off.insert k s!"the program can cast ({n})"
    else if let some u ← releaseUnsafe? t then
      off := off.insert k s!"its contents ({t}) may hold a value of type {u}, whose release the program can observe"
  -- Which makes and operations can meet: their mono types can be one type
  -- up to `lcAny` (`cellTypesMeet`), and their type arguments are not
  -- apart (`cellBaseApart`).
  let mut meets : Array (Expr × Name × Expr × Name) := #[]
  for (mb, m, mw) in makesL do
    for (ob, o, ow) in opsL do
      if cellTypesMeet env m o && !(← cellBaseApart mb ob) then
        meets := meets.push (m, mw, o, ow)
  -- A make and an operation that can meet have one representation.
  repeat
    let mut changed := false
    for (m, mw, o, ow) in meets do
      let rep (t : Expr) : Option String := (kinds.getD t none).filter (!off.contains ·)
      let (rm, ro) := (rep m, rep o)
      if rm == ro then continue
      let why := s!"a reference made at {m} ({mw}) can reach an operation at {o} ({ow})"
      for r in [rm, ro] do
        if let some k := r then
          unless off.contains k do off := off.insert k why
      changed := true
    unless changed do break
  let sorted := seen.qsort (· < ·)
  return { refOn := sorted.filter (!off.contains ·),
           refOff := sorted.filterMap fun k => (off[k]?).map (k, ·) }

end LeanToReussir
