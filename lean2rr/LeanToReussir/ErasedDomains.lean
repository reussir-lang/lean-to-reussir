import Lean
import LeanToReussir.MonoTypesKeep

/-!
# Rule 4: erased parameters and erased domains (Stage 4)

`◾` (`lcErased`: a type, a type argument or a proof) carries no
information. Stage 4 removes it from functions, calls and function types,
without moving the point where a function body runs: Lean runs a body when
its function's last parameter is applied, which `dbg_trace`, panics,
non-termination and the number of times work runs make observable.
Stages 1 to 3 keep Lean's arities (Lean's own passes, closed terms and
startup constants decide on them).

- **Declarations** (`keepMask`): an erased parameter stays only if it is
  the last parameter; it is then one `L2RUnit` parameter, which stands for
  the whole trailing group of erased parameters. Every other erased
  parameter is removed. So `f x` stays a partial application when Lean's
  `f` takes a type or a proof after `x`, and a function whose parameters
  are all erased stays a function. (Join points remove all of them.)
- **Function types** (`keptErasedHead`, used by `lowerType`): an erased
  domain stays as a unit domain when some function value that can have the
  type completes right after that domain; otherwise it is a phantom domain
  (`RR.Ty.phantom`), which has no parameter at run time.

The decision for an erased domain depends on the type from that domain on:
a function type's representation is built from its codomain's, so the
decision at a position cannot depend on the domains before it. It stays
(`keptErasedHead`) when it is the last domain of its type (a function type
stays a function), or when some value of the program completes right after
it at a type it can have:
- a value that completes at an erased domain of its own type keeps that
  domain in every type of the same skeleton (`Skel`, `eMarks`);
- any value keeps the domain in every type it can become along the
  program's flow (`flowAnalysis`, `reached`): the use sites where a value
  of one function type is used at another (a wrapper), and the `Box`
  positions it crosses. So a value that completes at an `lcAny` parameter
  of uniform code keeps a domain only where it reaches a type whose domain
  there is erased (test `RtErasedAnyFlow`), and flows of several steps are
  followed (a closure over the edges).
-/

namespace LeanToReussir
open Lean Compiler LCNF

/-- Whether mono type `d`, as a parameter or domain type, is erased: a
type, a type argument or a proof (`lcErased`, or a sort). The IO world
(`lcVoid`) and `Unit` are not. -/
def erasedDom (d : Expr) : Bool :=
  let d := d.consumeMData
  d.isErased || d.isSort

/-- Rule 4a, for a function with Lean parameter types `ps`: which
parameters it keeps (an erased parameter only when it is the last). -/
def keepMask (ps : Array Expr) : Array Bool :=
  ps.mapIdx fun i p => !erasedDom p || i + 1 == ps.size

/-- Tags of a skeleton's domains. -/
def skelE : UInt8 := 0
def skelD : UInt8 := 1
/-- A domain whose values may be of any type (`lcAny`, or another type
that Stage 4 represents by `Box`): it can be an erased domain of another
instantiation of the same type. -/
def skelA : UInt8 := 2

/-- The skeleton of a function type from one of its domains on: the tag of
each domain, and whether the codomain may hide further domains (a type
that Stage 4 may represent by `Box`). -/
structure Skel where
  tags : Array UInt8
  isOpen : Bool
  deriving BEq, Hashable, Inhabited

/-- Whether mono type `e` (not a function type) may be represented by
`Box` in Stage 4 (as `lowerType` does: `lcAny`, a type whose head is not
an inductive or a builtin type). Says `true` when unsure. -/
def mayBeBox (env : Environment) (e : Expr) : Bool :=
  let e := e.consumeMData.headBeta
  match e with
  | .forallE .. | .sort _ => false
  | _ =>
    match e.getAppFn with
    | .const n _ =>
      if n == ``lcAny then true
      else if n == ``lcErased || n == ``lcVoid then false
      else match env.find? (n ++ `_impl), env.find? n with
        | some (.inductInfo _), _ | _, some (.inductInfo _) => false
        | _, _ => true
    | _ => true

/-- The tag of domain type `d`. -/
def domTag (env : Environment) (d : Expr) : UInt8 :=
  if erasedDom d then skelE
  else if d.consumeMData.headBeta.isForall then skelD
  else if mayBeBox env d then skelA else skelD

/-- The skeleton of mono type `e` from its first domain on. -/
partial def skelOf (env : Environment) (e : Expr) : Skel :=
  go e #[]
where
  go (e : Expr) (acc : Array UInt8) : Skel :=
    match e.consumeMData.headBeta with
    | .forallE _ d b _ => go (b.instantiate1 anyExpr) (acc.push (domTag env d))
    | cod => { tags := acc, isOpen := mayBeBox env cod }

/-- The skeleton of mono type `e` from its domain at position `pos` on, if
it has one there. -/
def skelAt (env : Environment) (e : Expr) (pos : Nat) : Option Skel := Id.run do
  let mut e := e
  for _ in [:pos] do
    match e.consumeMData.headBeta with
    | .forallE _ _ b _ => e := b.instantiate1 anyExpr
    | _ => return none
  if e.consumeMData.headBeta.isForall then some (skelOf env e) else none

/-- Whether skeletons `a` and `b` can describe the same function type: the
same domains where both are known (an `lcAny` domain matches any domain),
and, where one ends first, a codomain that may hide the other's further
domains. -/
def Skel.unify (a b : Skel) : Bool := Id.run do
  let n := min a.tags.size b.tags.size
  for i in [:n] do
    let x := a.tags[i]!
    let y := b.tags[i]!
    unless x == y || x == skelA || y == skelA do return false
  if a.tags.size == b.tags.size then return true
  if a.tags.size < b.tags.size then return a.isOpen
  return b.isOpen

/-! ## Where function values go

A completion mark made at function type `S` keeps a domain of function type
`T` only if values of `S` can become values of `T`. In a program that
happens only through:
- `S = T` (the same mono type, `keyTy`);
- a conversion of function values `S → T` (a wrapper): a variable of type
  `S` used at a position of type `T` (an argument and its parameter, a
  constructor argument and its field, a returned value and the result type,
  a jump argument and its parameter, a field and the variable bound to it);
- a `Box`: a value boxed at `S` (used at an `lcAny` position) can come out
  wherever a `Box` is unboxed at `T` (an `lcAny` value used at `T`), if `S`
  and `T` can be one type (`Skel.unify`).

`flowAnalysis` collects these edges from mono LCNF, closes the marks over
them (`reachedMarks`), and gives the function types whose first domain
some value completes at (`ErasedInfo.reached`). Inside the analysis, an
unknown type counts as `lcAny` (an edge through a `Box`), so it never
misses an edge; it does not connect types that no value can go between.
-/

/-- A mono type in the form the analysis and `lowerType` compare: no
metadata, binders named alike, and the codomain of a function type
instantiated with `lcAny` (as `lowerType` lowers it). -/
partial def keyTy (e : Expr) : Expr :=
  match e.consumeMData.headBeta with
  | .forallE _ d b _ => .forallE `x (keyTy d) (keyTy (b.instantiate1 anyExpr)) .default
  | .lam _ d b _ => .lam `x (keyTy d) (keyTy b) .default
  | e@(.app ..) => e.withApp fun f args => mkAppN (keyTy f) (args.map keyTy)
  | e => e

/-- The number of domains of function type `e` (normalized). -/
def fnArity : Expr → Nat
  | .forallE _ _ b _ => fnArity b + 1
  | _ => 0

/-- Normalized function type `e` without its first `k` domains. -/
def dropDoms : Expr → Nat → Expr
  | e, 0 => e
  | .forallE _ _ b _, k + 1 => dropDoms b k
  | e, _ => e

/-- Whether normalized type `e` mentions a function type. -/
def hasFnTy (e : Expr) : Bool := (e.find? (·.isForall)).isSome

/-- The function type with domains `ps` and result `r`. -/
def mkFnTy (ps : Array Expr) (r : Expr) : Expr :=
  ps.foldr (fun p b => .forallE `x p b .default) r

/-- The mono types of the fields of constructor `ctor`, as the layout has
them (rule 1, `nominalType`: one layout per inductive, its fields computed
once with every parameter `lcAny`, so a field of a parameter's type is a
`Box` and a field that mentions a parameter has it at `lcAny`): the
constructor's type at `lcAny` parameters, each field through
`toMonoTypeKeep`. They do not depend on the instance (`inst`, kept for the
callers): a value of a field read at a typed binder is an edge from the
uniform field type, one stored there an edge to it. -/
def layoutFieldTypes (ctor : Name) (inst : Expr) : CoreM (Array Expr) := do
  let _ := inst
  let some (.ctorInfo ci) := (← getEnv).find? ctor | return #[]
  let ctorTy ← getOtherDeclBaseType ctor []
  let mut ty ← instantiateForall ctorTy (Array.replicate ci.numParams anyExpr)
  let mut out := #[]
  repeat
    match ty.headBeta with
    | .forallE _ d b _ =>
      out := out.push (← toMonoTypeKeep d)
      ty := b.instantiate1 anyExpr
    | _ => break
  return out

/-- What the lowering needs to decide erased domains: the skeletons after
which some value completes at an erased domain of its own type (`eMarks`,
kept by skeleton everywhere: such a completion is always real), and the
function types whose first domain some value completes at, along the
program's flow (`reached`, normalized). -/
structure ErasedInfo where
  eMarks : Array Skel := #[]
  reached : Std.HashSet Expr := {}
  deriving Inhabited

/-- Whether the erased domain at the head of function type `e` (skeleton
`k`) stays as a unit domain: it is the type's last domain, a value
completes right after an erased domain of that skeleton, or a value that
reaches `e` completes there. -/
def keptErasedHead (info : ErasedInfo) (k : Skel) (e : Expr) : Bool :=
  k.tags.size ≤ 1 || info.eMarks.any (·.unify k) || info.reached.contains (keyTy e)

structure FlowState where
  vars : Std.HashMap FVarId Expr := {}
  jps : Std.HashMap FVarId (Array Expr) := {}
  /-- Function type ↦ the function types its values become. -/
  edges : Std.HashMap Expr (Array Expr) := {}
  linked : Std.HashSet (Expr × Expr) := {}
  /-- Types (mentioning a function type) whose values go into a `Box`, and
  types a `Box` is unboxed at. -/
  boxed : Array Expr := #[]
  boxedSet : Std.HashSet Expr := {}
  unboxed : Array Expr := #[]
  unboxedSet : Std.HashSet Expr := {}
  /-- Function values created: (their type, the position they complete at). -/
  marks : Array (Expr × Nat) := #[]
  eMarks : Std.HashSet Skel := {}
  /-- `mayHoldFn`'s answers. -/
  holdsFn : Std.HashMap Expr Bool := {}
  /-- Whether the program can read a value as another type than its own
  (`programCasts`): a `Box` can then be unboxed at another inductive. -/
  casts : Bool := true

abbrev FlowM := StateRefT FlowState CoreM

/-- Whether `m` and `n` name one inductive (`T` and its implementation
`T._impl` alike). -/
def sameInductive (m n : Name) : Bool := m == n || m == n ++ `_impl || n == m ++ `_impl

/-- The inductive whose constructors build values of type `t` (`T._impl`
for a type with computed fields, as `lowerTypeApp`), if `t` is one (not a
proposition). -/
def inductiveOf (env : Environment) (t : Expr) : Option InductiveVal :=
  match t.getAppFn with
  | .const n _ =>
    match env.find? (n ++ `_impl), env.find? n with
    | some (.inductInfo iv), _ => some iv
    | _, some (.inductInfo iv) => if iv.type.getForallBody.isProp then none else some iv
    | _, _ => none
  | _ => none

/-- Whether a value of type `t` (normalized) can hold a function value:
some type reachable from `t` mentions a function type. From a type, its
type arguments (a container's elements: `Array`, `Thunk`, `Task`, a
reference, a promise, any inductive's parameters) and, for an inductive,
the fields of its constructors (`layoutFieldTypes`) are reachable. A plain
reachability with one visited set (linear in the types reached): a `false`
holds for every type visited, a `true` along the path that found it; both
are cached. (A search along every simple path, with the cycle cut on the
path only, took exponential time on a dense mutual block: review of
d8027f5, test `RtErasedDenseMutual`.) -/
partial def mayHoldFn (t : Expr) : FlowM Bool := do
  if hasFnTy t then return true
  if let some b := (← get).holdsFn[t]? then return b
  let visited ← IO.mkRef ({} : Std.HashSet Expr)
  let found ← go t visited
  unless found do
    for v in (← visited.get) do
      modify fun s => { s with holdsFn := s.holdsFn.insert v false }
  return found
where
  go (t : Expr) (visited : IO.Ref (Std.HashSet Expr)) : FlowM Bool := do
    if hasFnTy t then return true
    if let some b := (← get).holdsFn[t]? then return b
    if (← visited.get).contains t then return false
    visited.modify (·.insert t)
    let mut children := t.getAppArgs
    if let some iv := inductiveOf (← getEnv) t then
      for c in iv.ctors do
        for f in ← layoutFieldTypes c t do children := children.push (keyTy f)
    for c in children do
      if ← go c visited then
        modify fun s => { s with holdsFn := s.holdsFn.insert t true }
        return true
    return false

def FlowM.box (x : Expr) : FlowM Unit := do
  unless ← mayHoldFn x do return
  unless (← get).boxedSet.contains x do
    modify fun s => { s with boxed := s.boxed.push x, boxedSet := s.boxedSet.insert x }

def FlowM.unbox (y : Expr) : FlowM Unit := do
  unless ← mayHoldFn y do return
  unless (← get).unboxedSet.contains y do
    modify fun s => { s with unboxed := s.unboxed.push y, unboxedSet := s.unboxedSet.insert y }

mutual
/-- Values of mono type `x` become values of mono type `y` (see the section
comment): an edge between function types, their domains the other way
round, their results; for two instances of one inductive, their type
arguments and the fields of each constructor, both ways (Stage 4 converts
the value field by field, whichever way a field uses an argument); for
two inductives (a cast), the fields of their constructors at the same
position, both ways; a `Box` where one side may be `Box`, or where the two
cannot be compared. -/
partial def flowLink (x y : Expr) : FlowM Unit := do
  let x := keyTy x
  let y := keyTy y
  if x == y then return
  unless (← mayHoldFn x) || (← mayHoldFn y) do return
  if (← get).linked.contains (x, y) then return
  modify fun s => { s with linked := s.linked.insert (x, y) }
  let env ← getEnv
  let xAny := !x.isForall && mayBeBox env x
  let yAny := !y.isForall && mayBeBox env y
  if xAny && yAny then return
  if yAny then return ← FlowM.box x
  if xAny then return ← FlowM.unbox y
  match x, y with
  | .forallE .., .forallE .. =>
    modify fun s => { s with edges := s.edges.insert x ((s.edges.getD x #[]).push y) }
    let n := min (fnArity x) (fnArity y)
    let mut a := x
    let mut b := y
    for _ in [:n] do
      let (.forallE _ da ca _, .forallE _ db cb _) := (a, b) | break
      flowLink db da
      a := ca
      b := cb
    -- The rest: the results, or the domains one side has beyond the
    -- other's (behind a `Box` result, or a cast).
    flowLink a b
  | .lam _ _ bx _, .lam _ _ by_ _ =>
    flowLink (bx.instantiate1 anyExpr) (by_.instantiate1 anyExpr)
  | _, _ =>
    match x.getAppFn, y.getAppFn with
    | .const m _, .const n _ =>
      if sameInductive m n && x.getAppNumArgs == y.getAppNumArgs then
        for (a, b) in x.getAppArgs.zip y.getAppArgs do
          flowLink a b
          flowLink b a
        flowLinkFields x y true
      else
        flowLinkFields x y false
        FlowM.box x
        FlowM.unbox y
    | _, _ =>
      FlowM.box x
      FlowM.unbox y

/-- The fields of the constructors of `x`'s and `y`'s inductives, by
constructor position, linked both ways: each field with the field at the
same position (`same`: one inductive), or with every field (a cast between
two inductives; the fields a cast reads are not known here). -/
partial def flowLinkFields (x y : Expr) (same : Bool) : FlowM Unit := do
  let env ← getEnv
  let (some ix, some iy) := (inductiveOf env x, inductiveOf env y) | return
  for (cx, cy) in ix.ctors.zip iy.ctors do
    let fx ← layoutFieldTypes cx x
    let fy ← layoutFieldTypes cy y
    if same then
      for (a, b) in fx.zip fy do
        flowLink a b
        flowLink b a
    else
      for a in fx do
        for b in fy do
          flowLink a b
          flowLink b a
end

/-- Whether a value boxed at `b` can be unboxed at `u` (Lower's
`reprCompatible`, `boxCastable`): function types whose skeletons unify,
instances of one inductive, or (in a program that casts) of two. -/
def boxCompat (env : Environment) (casts : Bool) (b u : Expr) : Bool :=
  match b, u with
  | .forallE .., .forallE .. => (skelOf env b).unify (skelOf env u)
  | .forallE .., _ | _, .forallE .. => false
  | _, _ =>
    match b.getAppFn, u.getAppFn with
    | .const m _, .const n _ =>
      (sameInductive m n && b.getAppNumArgs == u.getAppNumArgs) ||
        (casts && (inductiveOf env b).isSome && (inductiveOf env u).isSome)
    | _, _ => false

/-- Link every boxed type with every type a `Box` is unboxed at that it can
be (`boxCompat`), until no link adds a boxed or unboxed type. -/
def flowThroughBoxes : FlowM Unit := do
  let env ← getEnv
  let mut doneB := 0
  let mut doneU := 0
  repeat
    let s ← get
    let nb := s.boxed.size
    let nu := s.unboxed.size
    if doneB == nb && doneU == nu then break
    -- New boxed types with every unboxed one, and old boxed ones with the
    -- new unboxed ones.
    for i in [:nb] do
      let b := s.boxed[i]!
      for j in [:nu] do
        if i < doneB && j < doneU then continue
        let u := s.unboxed[j]!
        if boxCompat env s.casts b u then flowLink b u
    doneB := nb
    doneU := nu

def FlowM.tyOf (x : FVarId) : FlowM Expr := do
  return (← get).vars.getD x anyExpr

def FlowM.setTy (x : FVarId) (t : Expr) : FlowM Unit :=
  modify fun s => { s with vars := s.vars.insert x t }

/-- Argument `a` used at a position of type `pos`. -/
def FlowM.use (a : Arg .pure) (pos : Expr) : FlowM Unit := do
  if let .fvar x := a then flowLink (← FlowM.tyOf x) pos

/-- A value created at function type `ty`, completing at position `pos`. -/
def FlowM.mark (ty : Expr) (pos : Nat) : FlowM Unit := do
  let ty := keyTy ty
  modify fun s => { s with marks := s.marks.push (ty, pos) }
  if let some sk := skelAt (← getEnv) ty pos then
    if sk.tags[0]? == some skelE then modify fun s => { s with eMarks := s.eMarks.insert sk }

/-- A value of type `fty` applied to `args`, the result used at type `res`
(the type of its binder): the arguments go to the domains; a `Box` callee
is applied as `Box → Box` (unboxed at that type, its arguments boxed). -/
def FlowM.apply (fty : Expr) (args : Array (Arg .pure)) (res : Expr) : FlowM Unit := do
  let env ← getEnv
  let mut t := keyTy fty
  let mut i := 0
  while i < args.size do
    match t with
    | .forallE _ d b _ =>
      FlowM.use args[i]! d
      t := b
      i := i + 1
    | _ =>
      if mayBeBox env t then
        FlowM.unbox (.forallE `x anyExpr anyExpr .default)
        for a in args[i:] do FlowM.use a anyExpr
        t := anyExpr
      break
  flowLink t res

/-- The arity, mono type and constructor (if it is one) of a constant
that a `let` applies, as Stage 4's `calleeOf` finds it. -/
def flowCallee (byName : Std.HashMap Name (Decl .pure)) (inits : Std.HashMap Name Expr) (f : Name) :
    CoreM (Option (Nat × Expr × Option ConstructorVal)) := do
  let env ← getEnv
  -- A constant defined by `initialize`: read from its once-cell, at the
  -- type the lowering gives the cell (`calleeOf`).
  if let some t := inits[f]? then return some (0, t, none)
  if let some (.ctorInfo c) := env.find? f then
    unless isExtern env f do
      return some (c.numParams + c.numFields, ← toMonoTypeKeep (← getOtherDeclBaseType f []), some c)
  if let some d := byName[f]? then return some (d.params.size, d.type, none)
  if let some d ← getMonoDecl? f then return some (d.params.size, d.type, none)
  if let some (.ctorInfo c) := env.find? f then
    return some (c.numParams + c.numFields, ← toMonoTypeKeep (← getOtherDeclBaseType f []), none)
  return none

/-- The fields of constructor `ctor` of inductive `typeName`, read from a
value of type `ty` (a `cases` or a projection) into variables of the types
`uses` (field index, variable type). An instance of `typeName`: its fields
at that instance. A `Box`: unboxed at the uniform instance first, whose
fields are read. Another inductive (a cast: Lower's `castCases`): the
fields of its constructor at `ctor`'s position, each to every variable,
and the uniform instance's. -/
def flowFieldUses (typeName ctor : Name) (ty : Expr) (uses : Array (Nat × Expr)) : FlowM Unit := do
  let env ← getEnv
  let ty := keyTy ty
  let uniform : FlowM Expr := do
    let some iv := inductiveOf env (mkConst typeName) | return mkConst typeName
    return mkAppN (mkConst typeName) (Array.replicate iv.numParams anyExpr)
  let toUses (inst : Expr) : FlowM Unit := do
    let fs ← layoutFieldTypes ctor inst
    for (i, t) in uses do flowLink (fs[i]?.getD anyExpr) t
  match ty.getAppFn with
  | .const n _ =>
    if sameInductive n typeName then return ← toUses ty
    if let some iv := inductiveOf env ty then
      -- A cast: the value's own constructor at the same position.
      let some iT := inductiveOf env (mkConst typeName) | return
      if let some k := iT.ctors.idxOf? ctor then
        if let some c := iv.ctors[k]? then
          for f in ← layoutFieldTypes c ty do
            for (_, t) in uses do flowLink f t
      toUses (← uniform)
      return
  | _ => pure ()
  -- A `Box` (or a type not known here).
  let u ← uniform
  FlowM.unbox u
  toUses u

/-- The flow of function values through declaration code `c`, whose
returned values have type `ret` (`inits`: the constants defined by
`initialize`, with their cells' types). -/
partial def flowCode (byName : Std.HashMap Name (Decl .pure)) (inits : Std.HashMap Name Expr) (ret : Expr)
    (c : Code .pure) : FlowM Unit := do
  match c with
  | .let d k =>
    FlowM.setTy d.fvarId d.type
    match d.value with
    | .fvar g args => FlowM.apply (← FlowM.tyOf g) args d.type
    | .const f _ args _ =>
      match ← flowCallee byName inits f with
      | some (n, ty, ctor?) =>
        -- The parameter types (a constructor's: its fields at the
        -- instance), and the type of the function.
        let (ps, fty) ← match ctor? with
          | some c =>
            let inst := if args.size ≥ n then d.type else (splitFn d.type (n - args.size)).2
            let fs ← layoutFieldTypes c.name inst
            let ps := Array.replicate c.numParams erasedExpr ++ fs
            pure (ps, mkFnTy ps inst)
          | none => pure ((splitFn ty n).1, ty)
        for h : i in [:min args.size n] do
          if let some p := ps[i]? then FlowM.use args[i]! p
        if args.size < n then
          -- A function value created: it completes at the last parameter.
          FlowM.mark fty (n - 1)
          flowLink (dropDoms (keyTy fty) args.size) d.type
        else
          FlowM.apply (dropDoms (keyTy fty) n) (args.extract n args.size) d.type
      | none =>
        -- An unknown constant: its arguments and result through a `Box`.
        for a in args do FlowM.use a anyExpr
        flowLink anyExpr d.type
    | .proj sn i y =>
      let env ← getEnv
      if let some iv := inductiveOf env (mkConst sn) then
        if let some ctor := iv.ctors.head? then
          flowFieldUses sn ctor (← FlowM.tyOf y) #[(i, d.type)]
    | _ => pure ()
    flowCode byName inits ret k
  | .fun d k _ =>
    FlowM.setTy d.fvarId d.type
    for p in d.params do FlowM.setTy p.fvarId p.type
    if d.params.size > 0 then FlowM.mark d.type (d.params.size - 1)
    flowCode byName inits (splitFn d.type d.params.size).2 d.value
    flowCode byName inits ret k
  | .jp d k =>
    for p in d.params do FlowM.setTy p.fvarId p.type
    modify fun s => { s with jps := s.jps.insert d.fvarId (d.params.map (·.type)) }
    flowCode byName inits ret d.value
    flowCode byName inits ret k
  | .jmp j args =>
    let ps := (← get).jps.getD j #[]
    for (a, p) in args.zip ps do FlowM.use a p
  | .return x => flowLink (← FlowM.tyOf x) ret
  | .cases cs =>
    let dty ← FlowM.tyOf cs.discr
    for alt in cs.alts do
      match alt with
      | .alt ctor ps k _ =>
        for p in ps do FlowM.setTy p.fvarId p.type
        flowFieldUses cs.typeName ctor dty (ps.mapIdx fun i p => (i, p.type))
        flowCode byName inits ret k
      | .default k => flowCode byName inits ret k
      | _ => pure ()
  | _ => pure ()
where
  /-- Parameter types and result of a function type with `n` parameters. -/
  splitFn (ty : Expr) (n : Nat) : Array Expr × Expr := Id.run do
    let mut ty := ty
    let mut ps := #[]
    for _ in [:n] do
      match ty.consumeMData.headBeta with
      | .forallE _ d b _ => ps := ps.push d; ty := b.instantiate1 anyExpr
      | _ => break
    return (ps, ty)

/-- Close the marks over the flow: a value created at `S`, completing at
position `c`, completes at `c` of every type it becomes (`edges`), and at
`c - k` of its type after `k` arguments. The function types whose first
domain some value completes at. -/
def reachedMarks (edges : Std.HashMap Expr (Array Expr)) (marks : Array (Expr × Nat)) :
    Std.HashSet Expr := Id.run do
  let mut seen : Std.HashSet (Expr × Nat) := {}
  let mut reached : Std.HashSet Expr := {}
  let mut work := marks
  while h : work.size > 0 do
    let (x, c) := work[work.size - 1]
    work := work.pop
    if seen.contains (x, c) then continue
    seen := seen.insert (x, c)
    if c == 0 then reached := reached.insert x
    else if let .forallE _ _ b _ := x then work := work.push (b, c - 1)
    for y in edges.getD x #[] do
      if fnArity y > c then work := work.push (y, c)
  return reached

/-- Rule 4's analysis of program `decls` (see the section comment);
`casts`: whether the program can read a value as another type
(`programCasts`); `inits`: its constants defined by `initialize`, each with
the declaration of its initializer. -/
def flowAnalysis (decls : Array (Decl .pure)) (casts : Bool) (inits : Array (Name × Name)) :
    CoreM ErasedInfo := do
  let byName : Std.HashMap Name (Decl .pure) := decls.foldl (fun m d => m.insert d.name d) {}
  -- The type of each `initialize` constant's cell (`calleeOf`).
  let mut initTys : Std.HashMap Name Expr := {}
  for (c, _) in inits do
    initTys := initTys.insert c (← toMonoTypeKeep (← getOtherDeclBaseType c []))
  let act : FlowM Unit := do
    for d in decls do
      let .code c := d.value | continue
      let (ps, r) := flowCode.splitFn d.type d.params.size
      for h : i in [:d.params.size] do
        let p := d.params[i]
        FlowM.setTy p.fvarId p.type
        -- Callers pass arguments at the declaration's type's parameter
        -- types; its body sees its parameters' own.
        if let some q := ps[i]? then flowLink q p.type
      flowCode byName initTys r c
    -- The startup glue stores an initializer's result (a field of its IO
    -- result) into the constant's cell.
    for (c, inst) in inits do
      let (some t, some d) := (initTys[c]?, byName[inst]?) | continue
      let (_, r) := flowCode.splitFn d.type d.params.size
      let r := keyTy r
      if let some iv := inductiveOf (← getEnv) r then
        for ctor in iv.ctors do
          for f in ← layoutFieldTypes ctor r do flowLink f t
    flowThroughBoxes
  let ((), st) ← act.run { casts }
  let reached := reachedMarks st.edges st.marks
  if (← IO.getEnv "L2R_DEBUG_RULE4").isSome then
    for (t, c) in st.marks do IO.eprintln s!"rule4 mark {c}: {t}"
    for (x, ys) in st.edges.toList do
      for y in ys do IO.eprintln s!"rule4 edge {x} ==> {y}"
    for b in st.boxed do IO.eprintln s!"rule4 boxed {b}"
    for u in st.unboxed do IO.eprintln s!"rule4 unboxed {u}"
    for r in reached.toList do IO.eprintln s!"rule4 reached {r}"
  return { eMarks := st.eMarks.toArray, reached }

end LeanToReussir
