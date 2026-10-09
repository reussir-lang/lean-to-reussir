import Lean
import LeanToReussir.MonoTypesKeep
import LeanToReussir.RR
import LeanToReussir.Relevance
import LeanToReussir.Collect
import LeanToReussir.Mono
import LeanToReussir.ErasedDomains
import LeanToReussir.ArrayKinds

/-!
# Stage 4 foundations: state and type translation

Translation plan §5.1. Every mono type becomes a Reussir type:

* builtin types map to native Reussir types or runtime (prelude) types;
* erased types (`◾`, types as values) and the IO world (`lcVoid`) become
  `unit`; an erased domain of a function type is a unit domain or a
  phantom one, which has no parameter at run time (rule 4, see
  `ErasedDomains`);
* every other inductive becomes one generated nominal type, whatever its
  type arguments: its constructors' fields are computed once, with every
  parameter `lcAny` (`nominalType`), so `Tree Nat` and `Tree α` are one type
  and a field of a parameter's type is a `Box`;
* the generic builtin types have one representation each, over `Box`:
  `Array α` is `RVec<Box>`, `Thunk α` and `Task α` a cell of one state type
  each, `ST.Ref σ α` one reference type holding a `Box`;
* function types become curried closures;
* `lcAny` (a type Lean itself does not know) becomes the uniform `Box`.
-/

namespace LeanToReussir
open Lean Compiler LCNF

/-- Layout of one constructor of a generated nominal type. -/
structure CtorLayout where
  /-- Reussir variant name (enums) — unused for structs. -/
  variant : String
  /-- Number of inductive parameters (leading arguments of a constructor
  application, dropped). -/
  numParams : Nat
  /-- One entry per Lean field: `some (i, ty)` when the field is relevant
  (its position among the Reussir fields and its type), `none` when it is
  erased and has no representation. `IO.Process.Child` has two more
  entries, its hidden fields (see `nominalType`). -/
  fields : Array (Option (Nat × RR.Ty))

/-- The relevant fields' values, given in Lean order, placed at their
positions in the Reussir record. -/
def CtorLayout.place (l : CtorLayout) (vals : Array RR.Expr) : Array RR.Expr := Id.run do
  let rel := l.fields.filterMap id
  let mut out := Array.replicate rel.size RR.Expr.unitVal
  for h : k in [:rel.size] do
    out := out.set! rel[k].1 (vals[k]?.getD .unitVal)
  return out

/-- The relevant fields' types in record position order. -/
def CtorLayout.posTys (l : CtorLayout) : Array RR.Ty := Id.run do
  let rel := l.fields.filterMap id
  let mut out := Array.replicate rel.size RR.Ty.unit
  for (p, t) in rel do out := out.set! p t
  return out

inductive Shape where
  /-- All constructors without relevant fields: `enum [value]`. -/
  | enumLike
  /-- One constructor: `struct`. -/
  | struct
  /-- Several constructors, some with fields: `enum`. -/
  | enum
  deriving BEq, Inhabited

structure TypeInfo where
  name : String
  shape : Shape
  ctors : NameMap CtorLayout
  /-- Constructor names in declaration order. -/
  ctorOrder : Array Name
  /-- A `[value]` struct (one field; see `nominalType`). -/
  value : Bool := false

structure LowerCtx where
  /-- Functions the runtime prelude defines. -/
  preludeFns : Std.HashSet String := {}
  /-- Externs of the program (not of Lean's library) that lean2rr refuses,
  with the reason (`Mono.ExternRoute.refused`): a call of one is reported
  (`calleeOf`), and the program rejected (`lowerProgram`). -/
  externRefusals : NameMap String := {}
  /-- Result types of the prelude's functions (from their signatures). -/
  preludeRets : Std.HashMap String RR.Ty := {}
  /-- Parameter types of the prelude's non-generic functions. -/
  preludeParams : Std.HashMap String (Array RR.Ty) := {}
  /-- The prelude's generic functions whose result type is one of their
  type parameters, with the index of the first parameter declared at it
  (`genericRetParams`). -/
  preludeRetArg : Std.HashMap String Nat := {}
  /-- Instances of the `IO.Error` builders, by runtime error kind. -/
  ioErrorBuilders : Array (Option Name) := #[]
  /-- Generic prelude functions over plain values (see
  `valueGenericPreludeFns`), with their number of type parameters. -/
  valueGenericFns : Std.HashMap String Nat := {}
  /-- Which parameters of those functions are Reussir closures. -/
  valueGenericCls : Std.HashMap String (Array Bool) := {}
  /-- Constants evaluated where they are used instead of cached in a
  once-cell (`chainConsts`, see `lowerDecl`). -/
  uncachedConsts : NameSet := {}
  /-- Unary Lean definitions returning a `String` that are replaced by a
  prelude function with the same results: definition ↦ prelude function and
  its parameter type (`PassConfig.preludeReplacements`). -/
  preludeReplacements : NameMap (String × RR.Ty) := {}
  /-- Whether a structure with a single relevant field is a `[value]`
  struct (`PassConfig.valueStructs`, see `nominalType`); otherwise it is a
  shared record like the others. -/
  valueStructs : Bool := false
  /-- Whether a placeholder that would allocate is built once and kept in
  a once-cell (`zeroValue`, `PassConfig.cachePlaceholders`). -/
  cachePlaceholders : Bool := false
  /-- Whether a constant whose boxing allocates (a `Float`, a `UInt64`
  from 2^63, ...) is boxed once and kept in a once-cell (`boxOf`,
  `PassConfig.boxedConsts`). -/
  boxedConsts : Bool := false
  /-- The order of a constructor's relevant fields in its record, given
  their alignments (`fieldAlign`): the record position of each field, as a
  permutation (`PassConfig.fieldOrder`). Reussir keeps the given order (the
  driver turns its own member packing off). -/
  fieldOrder : Array Nat → Array Nat := fun aligns => (List.range aligns.size).toArray
  /-- Whether the program can read a value as another type than its own
  (`unsafe` code of its own, or a cast justified by `sorry` or an axiom,
  but not by one of Lean's axioms of native evaluation; `programCasts`):
  otherwise a `Box` holding a value of one inductive is
  never read as another, and an unboxing reads only its own type's payload,
  in line (`boxCastable`, `tryCoerce`). -/
  programCasts : Bool := true
  /-- Whether the program creates tasks (`programCreatesTasks`): then its
  reference operations are the task-aware ones (`refCellOp`), and it has
  `l2r_std_drop_workers` (`stdContextFns`). lean-runtime's scheduler itself
  starts at run time, at the first task (its lazy start, `sched::start_lazy`,
  which `leanrt::task::start` calls at `main`'s start). -/
  createsTasks : Bool := false
  /-- The mono declarations of the program (code and extern instances). -/
  decls : NameMap (Decl .pure)
  /-- Instance name ↦ instance key (original declaration and type arguments). -/
  keys : NameMap InstKey
  /-- The declarations that are in a cycle of direct calls, each with the
  declarations of its cycle (its strongly connected component of the call
  graph, itself included): a tail call of one of them closes a loop. -/
  callCycles : NameMap NameSet := {}
  /-- Whether the helpers generated at the end (unboxing, application and
  conversion functions of function values) are
  generated only for what live code reaches, and unreachable functions
  dropped (`PassConfig.convLiveness`, Lower/Live). -/
  convLiveness : Bool := false
  /-- Where the program's function values complete, along its flow
  (`flowAnalysis`): which erased domains of function types stay as unit
  domains (`keptErasedHead`, `lowerType`). -/
  erased : ErasedInfo := {}
  /-- The storage kinds whose arrays are compact (`RVec<k>`;
  optimization `compact-arrays`, `compactArrayKinds`): an `Array S` whose
  element type has one of these kinds (`arrayStorage`). Empty: every array
  is an array of `Box`es. -/
  compactKindsOn : Array String := #[]
  /-- The inductives whose fields of type `Array α` (`α` a parameter) are a
  `Box` instead of an array of boxes, because the program also stores a
  compact array there (`arrayFieldInductives`, `nominalType`). -/
  boxedArrayFields : NameSet := {}

/-- How the target of a function value is called with all its arguments
(data, so that the lowering state can hold it; see Lower's
`targetCall`). -/
inductive FnCall where
  /-- A declaration of the program. -/
  | code (fn : String)
  /-- An extern, as `lowerExternCall` takes it. -/
  | extern (orig : Name) (typeArgs : Array Expr) (params : Array Expr) (ret : Expr)
  /-- A constructor, building a value of `fullRt`. -/
  | ctor (c : Name) (fullRt : RR.Ty)
  /-- Field `field` of the standard stream record `streamTy` on descriptor
  `fd` (see `streamValue`). -/
  | stream (fd : Nat) (field : Nat) (streamTy : RR.Ty)
  deriving Inhabited

/-- Something a function value can be a partial application of: Reussir
parameter types (one per Lean parameter), result type, and how it is
called. `id` is an identifier naming it in variant names. -/
structure FnTarget where
  id : String
  params : Array RR.Ty
  ret : RR.Ty
  call : FnCall
  /-- Which Lean parameters the target takes (rule 4a, `keepMask`); empty:
  all of them. The call passes the arguments of these only. -/
  keep : Array Bool := #[]
  /-- The target's function type, with its phantom domains (`lowerType` of
  its Lean type: Lean positions); `none`: `params → ret` (no erased
  domain). -/
  ty : Option RR.Ty := none
  deriving Inhabited

/-- A variant of a function-value enum besides `z` (the `box(0)`
placeholder) and `raw` (a Reussir closure): `part id j` is target `id`
applied to its first `j` Lean arguments (it captures those it takes);
`wrap src dst` is a function value of another representation `src` of the
same Lean type, as a value of type `dst` (the enum is `dst`'s run-time
type, which several types with phantom domains can share: `dst` says where
they are). -/
inductive FnVariant where
  | part (id : String) (j : Nat)
  | wrap (src : RR.Ty) (dst : RR.Ty)
  deriving BEq, Hashable, Inhabited

/-- A function whose body is generated at the end, once the variants it
matches are known (Lower/Live, `finishLive`): unboxing a `Box` to type `t`
(nominal or function type), applying a function value of type `t` to `j`
arguments, converting a function value from representation `src` to
`dst`. -/
inductive LiveHelper where
  | unbox (t : RR.Ty)
  | apply (t : RR.Ty) (j : Nat)
  | fconv (src dst : RR.Ty)
  deriving Inhabited

/-- What `conv-liveness` knows (Lower/Live): the names reached from the
roots, the variants live code builds, and the helpers it reaches. -/
structure LiveState where
  /-- The names reached: functions (generated or not yet), and the
  identifiers of raw text and atoms, which count as names too. -/
  names : Std.HashSet String := {}
  /-- Names reached and not looked up yet. -/
  work : Array String := #[]
  /-- The `Box` variants (by name) that live code builds. -/
  madeBox : Std.HashSet String := {}
  /-- The variants of function-value enums (enum name, variant name) that
  live code builds, and how many per enum. -/
  madeFn : Std.HashSet (String × String) := {}
  madeFnCount : Std.HashMap String Nat := {}
  /-- The items of `fns` before this position have been looked at
  (`dropFns` keeps it in step). -/
  seen : Nat := 0
  /-- The helpers requested so far, by function name, and how far each
  request array (`unboxTargets`, `fnUnboxTargets`, `fnApplies`, `fnConvs`)
  has been indexed. -/
  helperOf : Std.HashMap String LiveHelper := {}
  indexed : Array Nat := #[0, 0, 0, 0]
  /-- The live helpers, and the version (the number of variants they
  match that live code builds) of their body. -/
  helpers : Array (String × LiveHelper) := #[]
  done : Std.HashMap String Nat := {}

structure LowerState where
  /-- The state optional passes keep for the whole program (analyses they
  compute once), by the pass's name (`LowerState.getExt?`). -/
  ext : NameMap Dynamic := {}
  /-- `enumCtorCount?`'s answers, by inductive (`arrayKindOf`). -/
  enumCounts : Std.HashMap Name (Option Nat) := {}
  /-- Targets of function values, by id. -/
  fnTargets : Std.HashMap String FnTarget := {}
  /-- Variants of each function-value type (an `RR.Ty.fn`, at run time:
  `RR.Ty.rt`), besides `z` and `raw`. -/
  fnVariants : Std.HashMap RR.Ty (Array FnVariant) := {}
  /-- `keptErasedHead`'s decisions, by the function type whose first
  domain they decide (`lowerType`). -/
  keptErasedOf : Std.HashMap Expr Bool := {}
  /-- Requested application functions: function type and number of arguments. -/
  fnApplies : Array (RR.Ty × Nat) := #[]
  /-- The elements of `fnApplies` (a scan was linear: round 9 RV9S-02). -/
  fnApplySet : Std.HashSet (RR.Ty × Nat) := {}
  /-- Function types that some `Box` value is unboxed to. -/
  fnUnboxTargets : Array RR.Ty := #[]
  /-- The elements of `fnUnboxTargets` (a scan was linear: round 9 RV9S-02). -/
  fnUnboxTargetSet : Std.HashSet RR.Ty := {}
  /-- Generated application functions, with the number of variants of their
  type they were generated for. -/
  fnApplyDone : Std.HashMap (RR.Ty × Nat) Nat := {}
  /-- Conversions between two representations of a function type (source,
  target), and the source variant count their body was generated for. -/
  fnConvs : Array (RR.Ty × RR.Ty) := #[]
  /-- The elements of `fnConvs` (a scan was linear: round 9 RV9S-02). -/
  fnConvSet : Std.HashSet (RR.Ty × RR.Ty) := {}
  fnConvDone : Std.HashMap (RR.Ty × RR.Ty) Nat := {}
  /-- Inductive ↦ its generated type's name (one type per inductive). -/
  typeNames : NameMap String := {}
  typeInfos : Std.HashMap String TypeInfo := {}
  /-- Generated type name ↦ the inductive it represents. -/
  typeHeads : Std.HashMap String Name := {}
  /-- Generated type items, in creation order. -/
  typeItems : Array RR.Item := #[]
  /-- The payload types of `Box` and their names (`b<number>`, or `i…` for
  an immediate type), in order (the box API: `boxPayload`). -/
  boxVariants : Array (RR.Ty × String) := #[]
  /-- `boxVariants` by type (a scan was linear: round 9 RV9S-02). -/
  boxVariantOf : Std.HashMap RR.Ty String := {}
  /-- The payload numbers of the program's pointer payload types (`boxNum`):
  16 and up, types whose cell has a wide header from `boxWideBit` + 16 up,
  leaf types from `boxLeafBit` + 16 up. -/
  boxNums : Std.HashMap RR.Ty Nat := {}
  boxNextNum : Nat := 16
  boxNextWide : Nat := 0x4000 + 16
  boxNextLeaf : Nat := 0x8000 + 16
  /-- Function types whose nullary variants an unboxing builds by index
  (`l2r_fn_of_index_T`, generated with the program's box item). -/
  fnIndexReqs : Array RR.Ty := #[]
  /-- Types of constants whose value is traversed for tasks when it is
  first computed (`persistCall`); the traversals are generated at the end,
  once all variants of function types and `Box` are known
  (`finishPersistFns`), with the number of variants they were generated
  for. -/
  persistReqs : Array RR.Ty := #[]
  persistDone : Option (Nat × Nat) := none
  /-- Generated `[value]` structs carrying several join-point arguments. -/
  tupleTypes : Std.HashMap (Array RR.Ty) String := {}
  /-- The key of each of `tupleTypes`, by name (finding it by scanning
  `tupleTypes` was linear: round 9 RV9S-02). -/
  tupleKeys : Std.HashMap String (Array RR.Ty) := {}
  /-- Generated functions (declarations and outlined join points). A
  function replaced by another of the same name leaves a tombstone
  (`fnTombstone`, dropped at the end) where it was, so that positions stay
  valid. -/
  fns : Array RR.Item := #[]
  /-- The position in `fns` of each generated function, by name, for the
  items `fns[0:fnIndexed]` (`syncFnIndex`, `hasFn`): looking a helper up by
  scanning every item was quadratic (a program that imports a large
  library emits over 100000 items: round 9 RV9S-02).
  Invariant: each function name appears at most once among the functions
  in `fns` (tombstones aside). Every generator asks `hasFn` (or its own
  cache) before it emits, or uses a fresh name, and `replaceFn` turns the
  earlier function into a tombstone; so the index keeps one position per
  name. `syncFnIndex` stops with an internal error on a second function
  of a name (review R9S2R-01). -/
  fnPos : Std.HashMap String Nat := {}
  fnIndexed : Nat := 0
  /-- Whether `fns` holds the conversion counter (`convTickFn`, test
  builds only; a raw item, which `hasFn` does not index). -/
  convTickEmitted : Bool := false
  /-- Externs called by their C symbol that the prelude does not define, and
  externs of the program that lean2rr refuses: the symbol and the extern's
  declaration (`lowerExternCall`, `calleeOf`; reported by `lowerProgram`). -/
  missingExterns : Array (String × Name) := #[]
  /-- Nominal types that some `Box` value is unboxed to (converter bodies
  are generated at the end, once all `Box` variants are known). -/
  unboxTargets : Array String := #[]
  /-- The elements of `unboxTargets` (a scan was linear: round 9 RV9S-02). -/
  unboxTargetSet : Std.HashSet String := {}
  /-- Next once-cell slot for constants. -/
  cafSlots : Nat := 0
  /-- The `_init` functions of the once-cells (`cafAccessor`): kept out of
  rrc's MLIR inliner (`anchoredFns`). -/
  cafInits : Array String := #[]
  /-- First of the three cell slots holding the current standard streams
  (stdin, stdout, stderr), and the stream record type, once used. -/
  stdSlots : Option Nat := none
  stdStreamTy : Option RR.Ty := none
  /-- Once-cell slots of constants defined by `initialize`. -/
  initSlots : NameMap Nat := {}
  /-- Conversions between inductives read through `unsafeCast` being
  generated (for recursive types, `structConv`). -/
  convsInProgress : Std.HashSet String := {}
  /-- Which arguments of a call of a declaration or an extern are boxed
  positions (`boxedArgMask`, for `boxedOnlyVars`), by callee. -/
  boxedArgMasks : NameMap (Array (Option Bool)) := {}
  /-- Conversions of `structConv` that can never return a value (every
  constructor's value is `l2r_unreachable`): a use is `l2r_unreachable` in
  line (`convCall`), and the function is not generated unless a conversion
  being generated called it first (`convsCalledEarly`). -/
  deadConvs : Std.HashSet String := {}
  /-- Conversions called while they were being generated (a recursive or
  mutually recursive field): generated even when dead, as a function whose
  body is `l2r_unreachable`. -/
  convsCalledEarly : Std.HashSet String := {}
  /-- Lean's borrowed parameters of the program's declarations, and the
  variables they lend (`Lower/Borrow`), once computed. -/
  borrowInfo : Option (NameMap (Array Bool) × FVarIdSet) := none
  /-- Generated placeholder (`box(0)`) functions, per type. -/
  zeroFns : Std.HashMap RR.Ty String := {}
  /-- Types without a finite placeholder (their function in `zeroFns` is
  `l2r_unreachable`). -/
  zeroNone : Std.HashSet RR.Ty := {}
  /-- Types whose placeholder is being built, with their depth in that
  search (`zeroTry`). -/
  zeroBusy : Std.HashMap RR.Ty Nat := {}
  /-- The variables bound to a closed value that boxing treats as native
  Lean does (`boxOf`): a placeholder (`zeroValue`), a nullary declaration
  of the program (a constant or closed term), a `UInt64` literal from
  2^63. By name (names are unique in the program): the value and its
  type. -/
  closedLets : Std.HashMap String (RR.Expr × RR.Ty) := {}
  /-- The once-cells of boxed constants (`boxedConst`), by constant and
  type: the accessor. -/
  boxedConstFns : Std.HashMap String String := {}
  /-- Whether the code being lowered is the body of a declaration without
  parameters (`lowerDecl`), which runs once: `boxOf` boxes a constant in
  line there. -/
  inConstBody : Bool := false
  /-- Variants of the state machine being built (J4): name, fields, body. -/
  smArms : Array (String × Array (String × RR.Ty) × RR.Block) := #[]
  /-- String literals of the program, by id (see `strLit`). -/
  strLits : Array String := #[]
  strLitIds : Std.HashMap String Nat := {}
  /-- The state type of thunks and the state type of tasks (see
  `lazyState`), once made. -/
  thunkState : Option String := none
  taskState : Option String := none
  /-- Whether a task is registered with the runtime (`taskTag`: the task
  state type's tag, 0): the program then has functions that run the tasks
  the runtime hands over (`taskDispatchFns`). -/
  taskTagged : Bool := false
  /-- Names of generated thunk/task helper functions (see `lazyFn`). -/
  lazyFnNames : Std.HashSet String := {}
  /-- The name of the reference type (see `refType`), once made. -/
  refName : Option String := none
  counter : Nat := 0
  /-- The state of `conv-liveness` (Lower/Live; unused without it). -/
  live : LiveState := {}

abbrev LowerM := ReaderT LowerCtx (StateRefT LowerState CoreM)

/-- A part of the state, computed now, as a value of its own. Lean's
compiler moves a pure computation to where its result is used: with
`(← get).fns.size` used only after a probe, the state (or its `fns`) is
kept alive until then, so that every update meanwhile copies the struct
and every push onto `fns` copies the array (round 9 RV9S-02). A call that
is not inlined computes `f` before it returns. -/
@[noinline] def getPart {α : Type} (f : LowerState → α) : LowerM α :=
  modifyGet fun s => (f s, s)

/-- What a function replaced by another of the same name leaves in `fns`
(`replaceFn`), dropped at the end (`liveFns`). -/
def fnTombstone : RR.Item := .raw ""

/-- `fns` without the tombstones of replaced functions. -/
def liveFns (fns : Array RR.Item) : Array RR.Item :=
  fns.filter fun | .raw "" => false | _ => true

/-- Index the functions emitted since the last call (`fnPos`). Done inside
one `modifyGet`, with the map taken out of the state, so that neither the
map nor `fns` is shared when it is updated (a shared array is copied at
every push). A name indexed at another position that still holds its
function (not a tombstone) breaks the invariant of `fnPos`: an internal
error. -/
def syncFnIndex : LowerM Unit := do
  let dup ← modifyGet fun (s : LowerState) => Id.run do
    if s.fnIndexed == s.fns.size then return (none, s)
    -- Fewer items than indexed: `fns` was filtered (`dropFns`); start over.
    let start := if s.fnIndexed > s.fns.size then 0 else s.fnIndexed
    let pos := if start == 0 then {} else s.fnPos
    let s := { s with fnPos := {} }
    let mut pos := pos
    let mut dup : Option String := none
    for i in [start:s.fns.size] do
      if let some (RR.Item.fn n ..) := s.fns[i]? then
        if let some j := pos[n]? then
          let live := match s.fns[j]? with
            | some (RR.Item.fn m ..) => m == n
            | _ => false
          if j != i && live then dup := some n
        pos := pos.insert n i
    return (dup, { s with fnPos := pos, fnIndexed := s.fns.size })
  if let some n := dup then
    throwError "lean2rr: function {n} emitted twice (internal error)"

/-- Whether a function named `name` has been emitted. -/
def hasFn (name : String) : LowerM Bool := do
  syncFnIndex
  return (← get).fnPos.contains name

/-- Emit `item`, function `name`, replacing an earlier one of that name: the
earlier one's place becomes a tombstone, and `item` goes at the end (where
removing the earlier one and appending `item` would put it). -/
def replaceFn (name : String) (item : RR.Item) : LowerM Unit := do
  syncFnIndex
  modify fun (s : LowerState) =>
    match s.fnPos[name]? with
    | some i => { s with fns := (s.fns.setIfInBounds i fnTombstone).push item }
    | none => { s with fns := s.fns.push item }

/-- Remove the functions whose names satisfy `p` (the index starts over;
the liveness's `seen` counts the items kept before it). -/
def dropFns (p : String → Bool) : LowerM Unit :=
  modify fun (s : LowerState) => Id.run do
    let keep : RR.Item → Bool := fun | .fn n .. => !p n | _ => true
    let mut seen := 0
    for h : i in [:min s.live.seen s.fns.size] do
      if keep (s.fns[i]'(Nat.lt_of_lt_of_le h.upper (Nat.min_le_right _ _))) then seen := seen + 1
    return { s with
      fns := s.fns.filter keep
      fnPos := {}, fnIndexed := 0, live := { s.live with seen } }

def fresh (pre : String) : LowerM String := do
  let n ← getPart (·.counter)
  modify fun s => { s with counter := n + 1 }
  return s!"{pre}{n}"

/-- An injective, identifier-safe encoding of a string: ASCII letters and
digits are kept, `_` becomes `__`, and any other character `c` becomes
`_<hex code point>_`. -/
def identEscape (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    if c.isAlphanum && c.toNat < 128 then acc.push c
    else if c == '_' then acc ++ "__"
    else acc ++ "_" ++ (Nat.toDigits 16 c.toNat).asString ++ "_"

/-- An identifier-safe rendering of a Lean name, for readable hints in
generated names (uniqueness always comes from a numeric component). -/
def nameHint (n : Name) : String :=
  let s := n.toString (escape := false)
  let s := s.map fun c => if c.isAlphanum then c else '_'
  if s.length > 40 then (s.drop (s.length - 40)).toString else s

/-- Reussir function name of a Lean declaration (Lean's own C mangling,
which is injective and yields valid identifiers). -/
def fnName (n : Name) : String := n.mangle "l_"

/-! ## The box API

`Box` (the prelude's `LAny`, `leanrt::any`) holds a value whose type is not
known statically (`lcAny`): every field, array element, reference and thunk
or task value of a parameter's type (one representation per type), and the
`lcAny` binders of uniform code. It is one word, as Lean's `lean_object*`:
an odd word is an immediate `(v << 1) | 1` (scalars, an enumeration's
index, a shared enum's nullary variant by index, small `Nat`/`Int` words,
unit = `box(0)` = the word 1); an even word owns a reference to a counted
object, its address in the low 48 bits and the number of its payload type
in the top 16 (1 to 15: leanrt's kinds; 16 and up: the program's, given by
`boxNum`, leaf types with `boxLeafBit`, types whose cell has a wide header
with `boxWideBit`). Every place that boxes a value,
takes one out, makes or tests for `box(0)`, or looks at what a box can hold
goes through this section, which alone knows the encoding (with
`boxTypeItems` in `Lower/Finish`, which emits the program's release of
each payload type, `l2r_any_rel_<n>`, its trampoline and the table that
installs them in leanrt). Outside it only
`Lower/Live` reads the encoding: it recognizes the payloads live code
builds by the number a box construction passes (`l2r_any_of<T>(x, n)`,
`l2r_any_of_fn<T>(x, n)`: the payload `b<n>`, `boxPayload`); and the
runtime's generic `l2r_sink`, `l2r_ptr_addr_rec` and `l2r_persist_seen`
take a box as one counted handle (the prelude's `l2r_ptr_addr_rec` answers
`LAny::addr` for a box). -/

def boxName : String := "LAny"

/-- The uniform type. -/
def RR.Ty.box : RR.Ty := .named boxName

/-- Types that may cross Reussir's FFI boundary as parameters: integers,
floats, `bool`, and RC pointers (opaque runtime types, `Nat`/`Int` among
them, and shared records). -/
def isBoundaryTy (t : RR.Ty) : LowerM Bool := do
  match t with
  | .named n =>
    if n ∈ ["u8", "u16", "u32", "u64", "i8", "i16", "i32", "i64", "f32", "f64", "bool",
            "Nat", "Int", "LStr", "LHandle", boxName] then return true
    -- A reference is a shared record (see `refType`).
    if (← get).refName == some n then return true
    match (← get).typeInfos[n]? with
    | some info => return info.shape != .enumLike && !info.value
    | none => return false
  | .app n _ => return n == "RVec" || n == "LRef" || n == "LCell"
  -- A function value is a shared enum.
  | .fn .. => return true
  | .cls .. => return false

/-- The type a runtime cell (a once-cell of a constant, a polymorphic
extern's value of a type parameter) stores values of Reussir type `t` as,
and whether it wraps them: a type that cannot cross the FFI boundary is
wrapped in a one-field shared struct `ElemBox`. -/
def cellStorage (t : RR.Ty) : LowerM (RR.Ty × Bool) := do
  if ← isBoundaryTy t then return (t, false)
  let key := #[t, .named "__elem_box"]
  if let some n := (← get).tupleTypes[key]? then return (.named n, true)
  let n ← fresh "ElemBox"
  modify fun s => { s with
    tupleTypes := s.tupleTypes.insert key n
    tupleKeys := s.tupleKeys.insert n key
    typeItems := s.typeItems.push (.struct n false #[t]) }
  return (.named n, true)

/-- The value type an `ElemBox` (see `cellStorage`) wraps, if `t` is one. -/
def elemBoxOf? (t : RR.Ty) : LowerM (Option RR.Ty) := do
  let .named n := t | return none
  let some k := (← get).tupleKeys[n]? | return none
  if k.size == 2 && k[1]! == .named "__elem_box" then return some k[0]! else return none

/-- The fields of generated positional struct `n`: a `Tuple`'s (its key,
see `tupleType`) or an `ElemBox`'s one field (see `cellStorage`), if `n` is
one of them. -/
def tupleFields? (n : String) : LowerM (Option (Array RR.Ty)) := do
  let some k := (← get).tupleKeys[n]? | return none
  return some (if k.size == 2 && k[1]! == .named "__elem_box" then #[k[0]!] else k)

/-- The representation of an `ST.Ref σ α`, whatever `α` is (translation
plan §5.1): one shared record holding Reussir's mutable cell of a `Box`,
`L2RRef_N(Cell<Box>)` (all aliases of a reference share the record). -/
def refType : LowerM RR.Ty := do
  if let some n := (← get).refName then return .named n
  let n ← fresh "L2RRef"
  modify fun s => { s with
    refName := some n
    typeItems := s.typeItems.push (.struct n false #[.app "Cell" #[RR.Ty.box]]) }
  return .named n

/-- Whether `t` is the reference type (`refType`). -/
def isRefType (t : RR.Ty) : LowerM Bool := do
  let .named n := t | return false
  return (← get).refName == some n

/-- The index of a value of an enumeration type (a generated `[value]`
enum without fields), as `u64`: a generated `match`. -/
def enumIndexFn (tn : String) : LowerM String := do
  let name := s!"l2r_enum_index_{tn}"
  unless (← hasFn name) do
    let some info := (← get).typeInfos[tn]? | throwError "lean2rr: no enumeration {tn}"
    let arms := info.ctorOrder.zipIdx.filterMap fun (c, i) => (info.ctors.find? c).map fun l =>
      { ty := tn, ctor := some l.variant, binders := #[], body := ⟨#[("i", some (.named "u64"), .atom (toString i))], .var "i"⟩ : RR.Arm }
    let body : RR.Block := if arms.isEmpty then .ofExpr (.call "l2r_unreachable" #[.named "u64"] #[])
      else .ofExpr (.mtch (.var "x") arms)
    modify fun s => { s with fns := s.fns.push (.fn name #[("x", .named tn)] (.named "u64") body) }
  return name

/-- The value of enumeration type `tn` with index `i : u64` (a generated
chain of comparisons). -/
def enumOfIndexFn (tn : String) : LowerM String := do
  let name := s!"l2r_enum_of_index_{tn}"
  unless (← hasFn name) do
    let some info := (← get).typeInfos[tn]? | throwError "lean2rr: no enumeration {tn}"
    let ls := info.ctorOrder.filterMap info.ctors.find?
    let some last := ls.back? | do
      -- No values: the conversion is unreachable.
      modify fun s => { s with fns := s.fns.push (.fn name #[("x", .named "u64")] (.named tn)
        (.ofExpr (.call "l2r_unreachable" #[.named tn] #[]))) }
      return name
    let mut e : RR.Expr := .ctor tn (some last.variant) #[]
    for j in [:ls.size - 1] do
      let i := ls.size - 2 - j
      let some l := ls[i]? | continue
      e := .block ⟨#[("k", some (.named "u64"), .atom (toString i))],
        .ite (.atom "x == k") (.ofExpr (.ctor tn (some l.variant) #[])) (.ofExpr e)⟩
    modify fun s => { s with fns := s.fns.push (.fn name #[("x", .named "u64")] (.named tn) (.ofExpr e)) }
  return name

/-- `l2r_bool_of_u8(x)`: the `bool` that a compact array of `Bool`s stores
as the byte `x` (`elemOfStorage?`). -/
def boolOfU8Fn : LowerM String := do
  let name := "l2r_bool_of_u8"
  unless (← hasFn name) do
    modify fun s => { s with fns := s.fns.push (.fn name #[("x", .named "u8")] .bool
      ⟨#[("z", some (.named "u8"), .atom "0")], .atom "x != z"⟩) }
  return name

/-- Whether `tn` is an enumeration (a generated `[value]` enum without
fields). -/
def isEnumType (tn : String) : LowerM Bool :=
  return ((← get).typeInfos[tn]?.map (·.shape == .enumLike)).getD false

/-- Value `v` of Reussir type `vt` as an element of compact storage `st`
(optimization `compact-arrays`), when that is not `coerce`'s conversion: a
`bool` as its byte (`lean_bool_to_uint8`), an enumeration as the byte of
its index (`l2r_enum_index_T`). A box needs no more: its immediate is the
byte (`l2r_any_as_u8`). -/
def elemToStorage? (v : RR.Expr) (vt st : RR.Ty) : LowerM (Option RR.Expr) := do
  unless st == .named "u8" do return none
  let .named tn := vt | return none
  if tn == "bool" then return some (.call "lean_bool_to_uint8" #[] #[v])
  if ← isEnumType tn then return some (.cast (.call (← enumIndexFn tn) #[] #[v]) (.named "u8"))
  return none

/-- An element `v` of compact storage `st` as a value of Reussir type `vt`
(the inverse of `elemToStorage?`): a byte as a `bool` (`l2r_bool_of_u8`),
or as an enumeration by index (`l2r_enum_of_index_T`). -/
def elemOfStorage? (v : RR.Expr) (st vt : RR.Ty) : LowerM (Option RR.Expr) := do
  unless st == .named "u8" do return none
  let .named tn := vt | return none
  if tn == "bool" then return some (.call (← boolOfU8Fn) #[] #[v])
  if ← isEnumType tn then return some (.call (← enumOfIndexFn tn) #[] #[.cast v (.named "u64")])
  return none

/-- How values of a payload type are held in a box (`boxKind`). -/
inductive BoxKind where
  /-- The unit: `box(0)`, the word 1. -/
  | unit
  /-- A scalar (`u8`, `u16`, `u32`, `bool`, `f32`): the immediate of its
  word, by the prelude's `l2r_any_of_<k>` and `l2r_any_as_<k>`. As
  natively, the immediate does not say which type boxed it: a word read at
  another word type (`unsafeCast`) reads the same word. -/
  | scalar (k : String)
  /-- `u64`, `f64`, and the signed `i8`…`i64` as their bits: an immediate
  below 2^63, else a cell (`l2r_any_of_u64`, `l2r_any_of_f64`); the bits
  of an `i8`, `i16` or `i32` zero-extended, so always an immediate (as
  native Lean boxes a signed scalar of 32 bits or fewer). -/
  | word (k : String)
  /-- An enumeration (a `[value]` enum without fields): the immediate of
  its index. -/
  | enumIdx (tn : String)
  /-- A `[value]` struct: boxed as its one field (`ft`); a field that is a
  `Box` (`ST.Out σ α`) is the box itself. -/
  | valueStruct (tn : String) (ft : RR.Ty)
  /-- One of leanrt's kinds, with its fixed number: `Nat` 1, `Int` 2,
  `LStr` 3, `RVec<Box>` 6, `RVec<u8>` 7, `RVec<f64>` 8, and the compact
  arrays `RVec<u16>` 9, `RVec<u32>` 10, `RVec<u64>` 11, `RVec<f32>` 12 (`l2r_any_of<T>`;
  `l2r_any_as<T>` decodes `box(0)` as the kind's zero). -/
  | leanrt (num : Nat)
  /-- A program payload: a pointer with the program's number `num`
  (`boxNum`). `store` is the type the pointer is a handle of: an `ElemBox`
  around a type that cannot cross the FFI boundary (`wrapped`), else the
  type itself. `nullary`: the variants without fields of a shared enum, by
  index (Reussir represents them as immediates, which the box keeps as the
  immediate of the index); `isFn`: a function value (`l2r_any_of_fn`:
  its nullary variants keep their type, `(num << 32) | index`). -/
  | prog (num : Nat) (store : RR.Ty) (wrapped : Bool) (nullary : Array (Nat × String)) (isFn : Bool)

/-- The number of the first leaf payload type (`LEAF_BIT` in
`leanrt::any`): a leaf type's payloads are released directly, never
deferred (also inside a free). -/
def boxLeafBit : Nat := 0x8000

/-- A type whose values hold nothing counted or observable: a number, a
`bool`, the unit, an enumeration, a `[value]` struct of one of those. -/
partial def boxPlainScalar (t : RR.Ty) : LowerM Bool := do
  let .named n := t | return false
  if n ∈ ["u8", "u16", "u32", "u64", "i8", "i16", "i32", "i64", "f32", "f64", "bool", "L2RUnit"] then
    return true
  match (← get).typeInfos[n]? with
  | some info =>
    if info.shape == .enumLike then return true
    if info.value then
      match (info.ctors.find? info.ctorOrder[0]!).bind (·.posTys[0]?) with
      | some ft => return ← boxPlainScalar ft
      | none => return true
    return false
  | none => return false

/-- Whether pointer payloads of type `t` are leaves: a shared record or
enum whose fields are all plain scalars (`boxPlainScalar`), so that freeing
one frees nothing else and releases nothing observable. -/
def boxIsLeaf (t : RR.Ty) : LowerM Bool := do
  let .named n := t | return false
  let some info := (← get).typeInfos[n]? | return false
  if info.shape == .enumLike || info.value then return false
  for c in info.ctorOrder do
    let some l := info.ctors.find? c | return false
    for ft in l.posTys do
      unless ← boxPlainScalar ft do return false
  return true

/-- The number of the first payload type whose Reussir cell has a wide
header (`WIDE_BIT` in `leanrt::any`; `boxIsWide`): leanrt defers such a
payload's cell with `__reussir_drop_defer_wide`, which links the cell to the
cell deferred before it through that header, so the boxed heads of a list
freed whole take no memory on Reussir's pending stack. Only on numbers
without `boxLeafBit` (a leaf payload is released directly, never deferred). -/
def boxWideBit : Nat := 0x4000

/-- The most constructors a shared enum's cell can have and keep a wide
header (`hasWideHeader`: the fused tag stays below 2^16, since the
deferral links through the upper 16 bits of its word): `boxIsWide`, and
the check of a boxed function type's enum in `fnTypeItems`. -/
def boxWideMaxCtors : Nat := 0x10000

/-- Whether a record member of Reussir type `t` is 8-byte aligned in
Reussir's layout (`memberStorageType` and `deriveCompoundLayout` in
Reussir's `lib/IR/ReussirTypes.cpp`): a 64-bit scalar; a member that Reussir
stores as a pointer (a shared record or enum, an `ElemBox`, the reference
record, a function value, a Reussir `Cell` or closure, an opaque runtime
type such as `Nat`, `LStr`, `LAny` or `RVec`, which the frontend stores as
a shared link); or a `[value]` struct or tuple that holds one. Any other
type answers false: a payload is then deferred without the wide mark, which
costs memory, never correctness. -/
partial def rrAlign8 (t : RR.Ty) : LowerM Bool := do
  match t with
  | .named n =>
    if n ∈ ["u64", "i64", "f64", "Nat", "Int", "LStr", "LHandle", boxName] then return true
    if (← get).refName == some n then return true
    match (← get).typeInfos[n]? with
    | some info =>
      if info.shape == .enumLike then return false
      if !info.value then return true
      match (info.ctors.find? info.ctorOrder[0]!).bind (·.posTys[0]?) with
      | some ft => rrAlign8 ft
      | none => return false
    | none =>
      if (← elemBoxOf? t).isSome then return true
      match ← tupleFields? n with
      | some fs => fs.anyM rrAlign8
      | none => return false
  | .app n _ => return n ∈ ["RVec", "LRef", "LCell", "Cell"]
  | .fn .. | .cls .. => return true

/-- Whether the Reussir cell of a pointer payload whose handle has type
`store` (`BoxKind.prog`) has a wide header: its first 8 bytes are the
32-bit count and a 32-bit word that is a fused tag below 2^16 or padding.
That is Reussir's own rule for `__reussir_drop_defer_wide`
(`hasWideHeader` in Reussir's
`lib/Conversion/BasicOpsLowering/BasicOpsLowering.cpp`): a shared enum of
at most 2^16 constructors (Reussir fuses its tag into the header), or a
shared struct whose alignment is 8 (its members start at offset 8, after 4
bytes of padding; `rrAlign8` of a member): a generated record of the
program, the reference record, an `ElemBox`; a function value, the
shared enum `L2RFn_…` of its run-time type (`fnTypeItems`). A function
type's variants are known only at the end of the translation, so
`fnTypeItems` stops with an internal error if the enum of a function type
boxed with the mark has more than `boxWideMaxCtors` constructors: the mark
is never wrong. Not a runtime type (`RVec`, `LCell`, `LHandle`: blocks of
leanrt or Reussir's runtime, not Reussir records). That exclusion is
needed for safety, not only for accuracy: the deferral writes the second
word of the header, and those blocks keep data there (an `LCell`, a
thunk's or task's cell, its task index; an `RVec` header its `SCANNED`
mark), so a runtime type must never get the mark. A false answer only
costs memory; a true one for a cell without a wide header corrupts it. -/
def boxIsWide (store : RR.Ty) : LowerM Bool := do
  -- A function value (its handle type is the function type, `boxKind`):
  -- the enum of its run-time type, which `fnTypeItems` checks.
  if store matches .fn .. then return store.rt matches .fn ..
  let .named n := store | return false
  if (← get).refName == some n then return true
  match (← get).typeInfos[n]? with
  | some info =>
    if info.shape == .enumLike || info.value then return false
    if info.shape == .enum then return info.ctorOrder.size ≤ boxWideMaxCtors
    let some l := info.ctors.find? info.ctorOrder[0]! | return false
    l.posTys.anyM rrAlign8
  | none =>
    match ← elemBoxOf? store with
    | some t => rrAlign8 t
    | none => return false

/-- The program's payload number of pointer payload type `t`, whose handle
has type `store`, given once: 16 and up; `boxWideBit` + 16 and up for a
type whose cell has a wide header (`boxIsWide`); `boxLeafBit` + 16 and up
for a leaf type (`boxIsLeaf`; never wide). -/
def boxNum (t store : RR.Ty) : LowerM Nat := do
  if let some n := (← get).boxNums[t]? then return n
  let leaf ← boxIsLeaf t
  let wide ← if leaf then pure false else boxIsWide store
  let n ← getPart fun s => if leaf then s.boxNextLeaf else if wide then s.boxNextWide else s.boxNextNum
  if n ≥ (if leaf then 0x10000 else if wide then boxLeafBit else boxWideBit) then
    throwError "lean2rr: more payload types of Box than its 16-bit numbers hold"
  modify fun s => { s with
    boxNums := s.boxNums.insert t n
    boxNextNum := if leaf || wide then s.boxNextNum else n + 1
    boxNextWide := if wide then n + 1 else s.boxNextWide
    boxNextLeaf := if leaf then n + 1 else s.boxNextLeaf }
  return n

/-- How values of type `t` are boxed (`BoxKind`). -/
def boxKind (t : RR.Ty) : LowerM BoxKind := do
  -- A box is never boxed again: a `[value]` struct over a box is the box
  -- itself (`boxValue`, `boxUnbox`, `boxPayload`, `boxAllocates`), and no
  -- other path asks.
  if t == RR.Ty.box then throwError "lean2rr: boxKind of Box itself (internal error)"
  match t with
  | .named n =>
    if n == "L2RUnit" then return .unit
    if n ∈ ["u8", "u16", "u32", "bool", "f32"] then return .scalar n
    -- No Lean value has a signed type (Lean's `toMonoType` erases `Int8`…
    -- `Int64` and `ISize` to `UInt8`…`USize`): the signed words keep the
    -- box API total over Reussir's integer types; no caller boxes one today.
    if n ∈ ["u64", "f64", "i8", "i16", "i32", "i64"] then return .word n
    if n == "Nat" then return .leanrt 1
    if n == "Int" then return .leanrt 2
    if n == "LStr" then return .leanrt 3
    if let some info := (← get).typeInfos[n]? then
      if info.shape == .enumLike then return .enumIdx n
      if info.value then
        if let some ft := (info.ctors.find? info.ctorOrder[0]!).bind (·.posTys[0]?) then
          return .valueStruct n ft
        return .unit
      let nullary := info.ctorOrder.zipIdx.filterMap fun (c, i) =>
        (info.ctors.find? c).bind fun l => if l.fields.all Option.isNone then some (i, l.variant) else none
      return .prog (← boxNum t t) t false (if info.shape == .enum then nullary else #[]) false
    if ← isBoundaryTy t then return .prog (← boxNum t t) t false #[] false
    let (st, wrapped) ← cellStorage t
    return .prog (← boxNum t st) st wrapped #[] false
  | .app "RVec" #[e] =>
    if e == RR.Ty.box then return .leanrt 6
    if e == .named "u8" then return .leanrt 7
    if e == .named "f64" then return .leanrt 8
    -- Compact arrays (`compact-arrays`): leanrt's kinds for `Vec<u16>`,
    -- `Vec<u32>`, `Vec<u64>` and `Vec<f32>` (an `Array UInt8`, `Bool` or
    -- enumeration is kind 7, an `Array Float` kind 8, as `ByteArray` and
    -- `FloatArray`).
    if e == .named "u16" then return .leanrt 9
    if e == .named "u32" then return .leanrt 10
    if e == .named "u64" then return .leanrt 11
    if e == .named "f32" then return .leanrt 12
    return .prog (← boxNum t t) t false #[] false
  | .app .. => return .prog (← boxNum t t) t false #[] false
  | .fn .. => return .prog (← boxNum t t) t false #[] true
  | .cls .. =>
    let (st, wrapped) ← cellStorage t
    return .prog (← boxNum t st) st wrapped #[] false

/-- Register payload type `t` (values of `t` may be boxed), once; its name
(`b<number>` for a pointer payload, which liveness reads off the number a
box construction passes; `i…` for an immediate type; a `[value]` struct
has its field's). -/
partial def boxPayload (t : RR.Ty) : LowerM String := do
  if let some v ← getPart (·.boxVariantOf[t]?) then return v
  let k ← boxKind t
  -- A `[value]` struct over a box (`ST.Out σ α`) is the box itself: no
  -- payload (the name is not used).
  if let .valueStruct _ ft := k then
    if ft == RR.Ty.box then return "box"
  let v ← match k with
    | .unit => pure "b0"
    | .scalar _ | .word _ | .enumIdx _ => pure s!"i{t.enc}"
    | .valueStruct _ ft => boxPayload ft
    | .leanrt n => pure s!"b{n}"
    | .prog n .. => pure s!"b{n}"
  modify fun s => { s with boxVariants := s.boxVariants.push (t, v), boxVariantOf := s.boxVariantOf.insert t v }
  return v

/-- Start the program's box: the unit payload first. -/
def boxInit : LowerM Unit := do
  let _ ← boxPayload .unit

/-- The payload types registered so far, in order, with their names. -/
def boxPayloads : LowerM (Array (RR.Ty × String)) := getPart (·.boxVariants)

/-- The number and the stored type of a payload type a box holds as a
pointer (leanrt's kinds and the program's), if it is one; `wrapped`: the
pointer holds an `ElemBox` around the value. -/
def boxPointer? (t : RR.Ty) : LowerM (Option (Nat × RR.Ty × Bool)) := do
  match ← boxKind t with
  | .leanrt n => return some (n, t, false)
  | .prog n st wrapped .. => return some (n, st, wrapped)
  | _ => return none

/-- `box(0)`: the box Lean passes where a value is never inspected, and the
boxed unit: the word 1. -/
def boxZero : LowerM RR.Expr := return .call "l2r_any_unit" #[] #[]

/-- Whether `boxZero` allocates (then a placeholder of type `Box` is built
once, `zeroTry`): it does not. -/
def boxZeroAllocates : Bool := false

/-- Whether boxing a value of type `t` can allocate (`boxKind`): a `u64`,
`i64` or `f64` word (a `Float`, a `UInt64` from 2^63, a negative `i64`),
a `[value]` struct of one, a value wrapped in an `ElemBox`. An immediate
never does: `u8`/`u16`/`u32` (`Char`), `bool`, `f32`, an enumeration, the
unit, and `i8`/`i16`/`i32`, boxed as their zero-extended bits. Lean's
`Int8`…`Int64` and `ISize` are not signed types here: Lean's `toMonoType`
erases them to `UInt8`…`USize` (`hasTrivialStructure?`), so they are
`u8`…`u64`. -/
partial def boxAllocates (t : RR.Ty) : LowerM Bool := do
  match ← boxKind t with
  -- The signed words: no Lean value has one (`boxKind`).
  | .word k => return k ∉ ["i8", "i16", "i32"]
  | .valueStruct _ ft => if ft == RR.Ty.box then return false else boxAllocates ft
  | .prog _ _ wrapped _ _ => return wrapped
  | _ => return false

/-- `e : t` boxed (`t` is not `Box` itself). -/
partial def boxValue (e : RR.Expr) (t : RR.Ty) : LowerM RR.Expr := do
  let _ ← boxPayload t
  match ← boxKind t with
  | .unit =>
    if e matches .ctor "L2RUnit" (some "u") #[] then return ← boxZero
    let d ← fresh "du"
    return .block ⟨#[(d, some t, e)], ← boxZero⟩
  | .scalar k => return .call s!"l2r_any_of_{k}" #[] #[e]
  | .word "u64" => return .call "l2r_any_of_u64" #[] #[e]
  | .word "f64" => return .call "l2r_any_of_f64" #[] #[e]
  -- `i8`/`i16`/`i32`: the bits zero-extended (an immediate); `i64`: its
  -- bits. No Lean value reaches these arms: Lean erases its signed integers
  -- to unsigned words (`boxKind`).
  | .word "i8" => return .call "l2r_any_of_u64" #[] #[.cast (.cast e (.named "u8")) (.named "u64")]
  | .word "i16" => return .call "l2r_any_of_u64" #[] #[.cast (.cast e (.named "u16")) (.named "u64")]
  | .word "i32" => return .call "l2r_any_of_u64" #[] #[.cast (.cast e (.named "u32")) (.named "u64")]
  | .word _ => return .call "l2r_any_of_u64" #[] #[.cast e (.named "u64")]
  | .enumIdx tn => return .call "l2r_any_imm" #[] #[.call (← enumIndexFn tn) #[] #[e]]
  | .valueStruct _ ft =>
    let v ← fresh "bv"
    -- Over a box (`ST.Out σ α`): the box itself.
    if ft == RR.Ty.box then return .block ⟨#[(v, some t, e)], .field (.var v) 0⟩
    return .block ⟨#[(v, some t, e)], ← boxValue (.field (.var v) 0) ft⟩
  | .leanrt n => return .call "l2r_any_of" #[t] #[e, .atom (toString n)]
  | .prog n st wrapped nullary isFn =>
    let v := if wrapped then (match st with | .named sn => RR.Expr.ctor sn none #[e] | _ => e) else e
    -- Without nullary variants the handle is always a pointer: no test for
    -- a nullary variant's immediate (`l2r_any_of_ptr`).
    let f := if isFn then "l2r_any_of_fn" else if nullary.isEmpty then "l2r_any_of_ptr" else "l2r_any_of"
    return .call f #[st] #[v, .atom (toString n)]

/-- The value of type `t` a pointer word `w` (owning its reference) of
payload `t` holds: `l2r_any_raw_take` (the number was checked). -/
def boxTake (w : RR.Expr) (t : RR.Ty) : LowerM RR.Expr := do
  let some (_, st, wrapped) ← boxPointer? t | throwError "lean2rr: {t.render} is not a pointer payload (internal error)"
  let x := RR.Expr.call "l2r_any_raw_take" #[st] #[w]
  return if wrapped then .field x 0 else x

/-- The box `b` as its word: `k w` with `w` (a fresh name) the word, which
owns the box's reference (`l2r_any_raw`). -/
def boxWithWord (b : RR.Expr) (k : String → LowerM RR.Expr) : LowerM RR.Expr := do
  let w ← fresh "bw"
  return .block ⟨#[(w, some (.named "u64"), .call "l2r_any_raw" #[] #[b])], ← k w⟩

/-- The prelude's reads of an element of an array of boxes (`RVec<Box>`)
that have a variant reading the element at a type, an immediate without a
copy of the box (`<name>_as<T>`, `l2r_view_take_as`). -/
def boxWordReads : List String :=
  ["lean_array_fget", "lean_array_fget_borrowed", "lean_array_get", "lean_array_get_borrowed",
   "lean_array_uget", "lean_array_uget_borrowed"]

/-- The array read `b` (a call of a `boxWordReads` read at `Box`, maybe in
the block of `bindReadIndex`) as the read of the element at `at` (`u64`:
the box's word, for an unboxing at a type held only as an immediate;
`Nat`, `Int`), without a copy of the box when it is an immediate: one test
of bit 0, no reference counting (`boxUnbox`). -/
partial def boxWordRead? (b : RR.Expr) (at_ : RR.Ty) : Option RR.Expr :=
  match b with
  | .call f #[t] args =>
    if t == RR.Ty.box && boxWordReads.contains f then some (.call (f ++ "_as") #[at_] args) else none
  | .block ⟨lets, r⟩ => (boxWordRead? r at_).map fun r' => .block ⟨lets, r'⟩
  | _ => none

/-- Box `b` unboxed at type `t`, as the prelude's
rule for generated unboxes says: an immediate is `t`'s scalar, its
enumeration index, one of its nullary variants by index, or, for the word
1 (`box(0)`, index 0), its zero (`zeroOf t`); a pointer is checked against
`t`'s number. Anything else is a cast (`slow`: the generated function
`Box → t` that reads values of the types Lean represents alike, in a
program that casts) or unreachable (the box released first). A function
type (`t` itself, or the field of a `[value]` struct) is unboxed by the
generated function `fnUnbox t` (`unboxFnFn`: it reads every
representation of the function type and the typed immediates of
`l2r_any_of_fn`). -/
partial def boxUnbox (b : RR.Expr) (t : RR.Ty) (zeroOf : RR.Ty → LowerM RR.Expr)
    (fnUnbox : RR.Ty → LowerM String) (slow : Option String := none) : LowerM RR.Expr := do
  let u64 := RR.Ty.named "u64"
  let back (w : String) : RR.Expr := .call "l2r_any_of_raw" #[] #[.var w]
  let otherwise (w : String) : RR.Block := match slow with
    | some f => .ofExpr (.call f #[] #[back w])
    | none => ⟨#[("l2rbs", some u64, .call "l2r_any_drop_raw" #[] #[.var w])], .call "l2r_unreachable" #[t] #[]⟩
  let isImm (w : String) : RR.Expr := .call "l2r_any_raw_is_imm" #[] #[.var w]
  -- `if <the word's number is n> { yes } else { no }`
  let ifNum (w : String) (n : Nat) (yes no : RR.Block) : LowerM RR.Expr := do
    let k ← fresh "bn"
    let m ← fresh "bm"
    return .block ⟨#[(k, some u64, .call "l2r_any_raw_num" #[] #[.var w]), (m, some u64, .atom (toString n))],
      .ite (.atom s!"{k} == {m}") yes no⟩
  match ← boxKind t with
  | .unit =>
    let d ← fresh "du"
    return .block ⟨#[(d, some RR.Ty.box, b)], .unitVal⟩
  | .scalar k =>
    let dec (e : RR.Expr) : RR.Expr := .call s!"l2r_any_as_{k}" #[] #[e]
    if slow.isNone then
      -- An array element read at once: its word, without a copy of the box
      -- (`boxWordRead?`).
      if k != "f32" then
        if let some w := boxWordRead? b (.named "u64") then return .call s!"l2r_any_word_as_{k}" #[] #[w]
      return dec b
    boxWithWord b fun w => return .ite (isImm w) (.ofExpr (dec (back w))) (otherwise w)
  | .word k =>
    let dec (e : RR.Expr) : RR.Expr := match k with
      | "u64" => .call "l2r_any_as_u64" #[] #[e]
      | "f64" => .call "l2r_any_as_f64" #[] #[e]
      -- The signed words: no Lean value has one (`boxKind`).
      | _ => .cast (.call "l2r_any_as_u64" #[] #[e]) t
    if slow.isNone then return dec b
    -- leanrt reads its immediates and both cells (`u64` and `f64` read
    -- each other's bits); any other pointer is a cast.
    boxWithWord b fun w => do
      let k ← fresh "bn"
      let c4 ← fresh "bm"
      let c5 ← fresh "bm"
      let ptr : RR.Block := ⟨#[(k, some u64, .call "l2r_any_raw_num" #[] #[.var w]), (c4, some u64, .atom "4"), (c5, some u64, .atom "5")],
         .ite (.atom s!"{k} == {c4}") (.ofExpr (dec (back w)))
           (.ofExpr (.ite (.atom s!"{k} == {c5}") (.ofExpr (dec (back w))) (otherwise w)))⟩
      return .ite (isImm w) (.ofExpr (dec (back w))) ptr
  | .enumIdx tn =>
    let ofIdx ← enumOfIndexFn tn
    if slow.isNone then
      if let some w := boxWordRead? b (.named "u64") then return .call ofIdx #[] #[.call "l2r_any_word_imm" #[] #[w]]
      return .call ofIdx #[] #[.call "l2r_any_as_imm" #[] #[b]]
    boxWithWord b fun w => do
      let yes := RR.Block.ofExpr (.call ofIdx #[] #[.call "l2r_any_raw_imm" #[] #[.var w]])
      return .ite (isImm w) yes (otherwise w)
  | .valueStruct tn ft =>
    -- Over a box (`ST.Out σ α`): the struct around the box itself.
    if ft == RR.Ty.box then return .ctor tn none #[b]
    -- The field's own unboxing (its zero is the field of the struct's zero);
    -- a function value's through `fnUnbox` (a recursive structure whose one
    -- field is a function, `inductive G | mk : (Nat → Option (Nat × G)) → G`).
    return .ctor tn none #[← boxUnbox b ft zeroOf fnUnbox none]
  | .leanrt n =>
    if slow.isNone then
      -- An array element read at once as a `Nat` or `Int`: an immediate
      -- without a copy of the box (`boxWordRead?`).
      if n == 1 || n == 2 then
        if let some r := boxWordRead? b t then return r
      return .call "l2r_any_as" #[t] #[b, .atom (toString n)]
    boxWithWord b fun w => do
      let yes := RR.Block.ofExpr (.call "l2r_any_as" #[t] #[back w, .atom (toString n)])
      return .ite (isImm w) yes (.ofExpr (← ifNum w n yes (otherwise w)))
  | .prog n _ _ nullary isFn =>
    if isFn then return .call (← fnUnbox t) #[] #[b]
    boxWithWord b fun w => do
      -- An immediate: the index (0 first: `box(0)`).
      let immB : RR.Block ← if nullary.isEmpty then do
          let one ← fresh "bm"
          pure ⟨#[(one, some u64, .atom "1")], .ite (.atom s!"{w} == {one}") (.ofExpr (← zeroOf t)) (otherwise w)⟩
        else do
          let i ← fresh "bi"
          let tn := match t with | .named tn => tn | _ => ""
          let zero0 : Option (Nat × String) := nullary.find? (fun (k, _) => k == 0)
          let zeroArm ← match zero0 with
            | some (_, v) => pure (RR.Arm.lit 0 (.ofExpr (.ctor tn (some v) #[])))
            | none => pure (RR.Arm.lit 0 (.ofExpr (← zeroOf t)))
          let rest : Array (Nat × String) := nullary.filter (fun (k, _) => k != 0)
          let arms := #[zeroArm] ++ rest.map (fun (k, v) => RR.Arm.lit k (.ofExpr (.ctor tn (some v) #[])))
            |>.push { ty := tn, ctor := none, binders := #[], body := otherwise w }
          pure ⟨#[(i, some u64, .call "l2r_any_raw_imm" #[] #[.var w])], .mtch (.var i) arms⟩
      let ptrB ← ifNum w n (.ofExpr (← boxTake (.var w) t)) (otherwise w)
      return .ite (isImm w) immB (.ofExpr ptrB)

/-- The array read of a box that `boxWordRead?` made a read at a type. -/
partial def boxWordReadBack? (w : RR.Expr) : Option RR.Expr :=
  match w with
  | .call f #[_] args =>
    match boxWordReads.find? (· ++ "_as" == f) with
    | some r => some (.call r #[RR.Ty.box] args)
    | none => none
  | .block ⟨lets, r⟩ => (boxWordReadBack? r).map fun r' => .block ⟨lets, r'⟩
  | _ => none

/-- The box `b` if `e` is `boxUnbox b t` (any `slow`): `boxValue e t` is
then `b` itself (`tryCoerce`). Folding the round trip passes the box on, as
native code passes the object on. What a box can hold reads alike before
and after: `box(0)` is read as `t`'s zero by every unboxing at `t`, where
`box(zero)` was before; a nullary variant boxes back to its own immediate;
a word or a cell (`Float`, a large `UInt64`) is passed on unchanged instead
of being read and boxed again (a new cell). -/
partial def boxUnboxed? (e : RR.Expr) (t : RR.Ty) : LowerM (Option RR.Expr) := do
  -- `boxWithWord`'s block: the unboxings of the program's payloads, and
  -- every unboxing with a `slow` function.
  let ofWordBlock : Option RR.Expr := match e with
    | .block ⟨#[(_, some (.named "u64"), .call "l2r_any_raw" #[] #[b])], _⟩ => some b
    | _ => none
  match ← boxKind t with
  | .unit => return none
  | .scalar k =>
    if let .call f #[] #[b] := e then
      if f == s!"l2r_any_as_{k}" then return some b
      -- An array element read as its word (`boxWordRead?`): the read of the box.
      if f == s!"l2r_any_word_as_{k}" then return boxWordReadBack? b
    return ofWordBlock
  | .word k =>
    match e with
    | .call "l2r_any_as_u64" #[] #[b] => return if k == "u64" then some b else none
    | .call "l2r_any_as_f64" #[] #[b] => return if k == "f64" then some b else none
    | .cast (.call "l2r_any_as_u64" #[] #[b]) _ => return if k != "u64" && k != "f64" then some b else none
    | _ => return ofWordBlock
  | .enumIdx tn =>
    if let .call f #[] #[.call "l2r_any_as_imm" #[] #[b]] := e then
      if f == s!"l2r_enum_of_index_{tn}" then return some b
    if let .call f #[] #[.call "l2r_any_word_imm" #[] #[w]] := e then
      if f == s!"l2r_enum_of_index_{tn}" then return boxWordReadBack? w
    return ofWordBlock
  | .valueStruct tn ft =>
    match e with
    | .ctor n none #[inner] =>
      if n != tn then return none
      -- Over a box: the box itself (`boxUnbox`).
      if ft == RR.Ty.box then return some inner
      boxUnboxed? inner ft
    | _ => return none
  | .leanrt _ =>
    if let .call "l2r_any_as" #[_] #[b, _] := e then return some b
    if let some b := boxWordReadBack? e then return some b
    return ofWordBlock
  | .prog _ _ _ _ isFn => return if isFn then none else ofWordBlock

/-- An arm of `boxDispatch`: a pointer payload type, the binder of its
value (at that type), and the arm's code. -/
structure BoxArm where
  payload : RR.Ty
  binder : Option String := none
  body : RR.Block

/-- A match on the payload number of box `b`: an arm per pointer payload
type in `arms` (its value taken out at its type), `imm` for an immediate
(given the word's name and the box back) and `other` for any other number
(given the box back). -/
def boxDispatch (b : RR.Expr) (arms : Array BoxArm) (imm : String → RR.Expr → LowerM RR.Block)
    (other : RR.Expr → LowerM RR.Block) : LowerM RR.Expr := do
  boxWithWord b fun w => do
    let back := RR.Expr.call "l2r_any_of_raw" #[] #[.var w]
    let mut out : Array RR.Arm := #[]
    let mut seen : Std.HashSet Nat := {}
    for a in arms do
      let some (n, _, _) ← boxPointer? a.payload | continue
      if seen.contains n then continue
      seen := seen.insert n
      let take ← boxTake (.var w) a.payload
      let lets := match a.binder with
        | some x => #[(x, some a.payload, take)]
        | none => #[("l2rbd", some (.named "u64"), .call "l2r_any_drop_raw" #[] #[.var w])]
      out := out.push (RR.Arm.lit n { a.body with lets := lets ++ a.body.lets })
    let k ← fresh "bn"
    let o ← other back
    let num : RR.Expr := if out.isEmpty then .block o
      else .block ⟨#[(k, some (.named "u64"), .call "l2r_any_raw_num" #[] #[.var w])],
        .mtch (.var k) (out.push { ty := "_", ctor := none, binders := #[], body := o })⟩
    return .ite (.call "l2r_any_raw_is_imm" #[] #[.var w]) (← imm w back) (.ofExpr num)

/-- A `let` releasing box `b` (`l2r_any_addr` takes it; a fixed name: the
only binding of the arm it is used in). -/
def boxSink (b : RR.Expr) : String × Option RR.Ty × RR.Expr :=
  ("l2rbs", some (.named "u64"), .call "l2r_any_addr" #[] #[b])

/-- `ptrAddrUnsafe` of box `b`: its payload's address, or an immediate's
word (`l2r_any_addr`). -/
def boxAddr (b : RR.Expr) : RR.Expr := .call "l2r_any_addr" #[] #[b]

/-- The function `l2r_fn_of_index_T` builds the nullary variant of index
`i` of function type `t` (a typed immediate's index, `l2r_any_of_fn`);
generated with the box item (`boxTypeItems`), when every variant of `t` is
known. -/
def boxFnOfIndex (t : RR.Ty) : LowerM String := do
  unless (← getPart (·.fnIndexReqs)).contains t do
    modify fun s => { s with fnIndexReqs := s.fnIndexReqs.push t }
  return s!"l2r_fn_of_index_{t.enc}"

/-- The state type of thunks (`task = false`) or of tasks: one each, over
`Box` values (whatever `α` is in `Thunk α`, `Task α`): a generated shared
enum `{ pending(L2RUnit -> Box), busy, done(Box) }` (tasks also
`bind(L2RUnit -> LCell<S>)`) held in a runtime cell `LCell<S>` (translation
plan §5.14). A thunk starts `pending` (or `done`, for `Thunk.pure`) and is
`busy` while its closure runs; a task is `done` from the start unless it is
a deferred IO task. -/
def lazyState (task : Bool) : LowerM String := do
  if let some n ← getPart (if task then (·.taskState) else (·.thunkState)) then return n
  let n ← fresh (if task then "L2RTask" else "L2RThunk")
  let t := RR.Ty.box
  let cellTy := RR.Ty.app "LCell" #[.named n]
  let item := RR.Item.enum n false (#[("pending", #[.fn .unit t]), ("busy", #[]), ("done", #[t])] ++
    -- `bind`: an `IO.bindTask` task before it has run `f` (its computation
    -- yields the task it continues as, see `taskStepFn`).
    (if task then #[("bind", #[.fn .unit cellTy])] else #[]))
  modify fun s => if task then { s with taskState := some n, typeItems := s.typeItems.push item }
    else { s with thunkState := some n, typeItems := s.typeItems.push item }
  let _ ← boxPayload cellTy
  return n

/-- The state type of a thunk or task representation `LCell<S>`, and
whether it is the tasks', if `t` is one. Its value is a `Box`. -/
def lazyOf? (t : RR.Ty) : LowerM (Option (String × Bool)) := do
  let .app "LCell" #[.named s] := t | return none
  let st ← get
  if st.taskState == some s then return some (s, true)
  if st.thunkState == some s then return some (s, false)
  return none

/-- A string literal: `l2r_str_lit(id)`, which builds the string from a
table of byte strings generated with the program (`strLitTable`). Passing
a Reussir `str` to the runtime would go through a stack slot whose address
escapes, which keeps LLVM from turning tail calls of the enclosing function
into loops. -/
def strLit (s : String) : LowerM RR.Expr := do
  let id ← match (← get).strLitIds[s]? with
    | some id => pure id
    | none =>
      let id ← getPart (·.strLits.size)
      modify fun st => { st with strLits := st.strLits.push s, strLitIds := st.strLitIds.insert s id }
      pure id
  return .call "l2r_str_lit" #[] #[.atom (toString id)]

/-- The runtime function behind `strLit`: the literals as Rust byte strings.
`[` is escaped too, so that no `[:` in a literal can be taken for a texture
placeholder `[:Name:]` (Reussir bug 21 dropped an unterminated one). -/
def strLitTable (lits : Array String) : String :=
  let hex := "0123456789abcdef".toList.toArray
  let esc (s : String) : String := s.toUTF8.foldl (init := "") fun acc b =>
    if b ≥ 0x20 && b < 0x7f && b != 0x22 && b != 0x5c && b != 0x5b then acc.push (Char.ofNat b.toNat)
    else acc ++ "\\x" |>.push hex[(b / 16).toNat]! |>.push hex[(b % 16).toNat]!
  let items := lits.toList.map fun s => s!"b\"{esc s}\""
  "#[ffi(import)]\nfn l2r_str_lit(id : u64) -> LStr [{ {\n" ++
  s!"    const LITS: &[&[u8]] = &[{", ".intercalate items}];\n" ++
  "    leanrt::string::from_bytes(LITS[id as usize])\n} }];\n"

/-- The element type of runtime array type `t` (`RVec<e>`: the storage
type of `Array α`, `arrayStorage`, `u8` for `ByteArray`, `f64` for
`FloatArray`), if it is one. -/
def arrayElem? (t : RR.Ty) : Option RR.Ty :=
  match t with
  | .app "RVec" #[e] => some e
  | _ => none

/-- A call of the runtime array primitive `l2r_array_<op>` at element type
`e`. -/
def arrayCall (e : RR.Ty) (op : String) (args : Array RR.Expr) : RR.Expr :=
  .call s!"l2r_array_{op}" #[e] args

/-- Alignment class of a field type: 1, 2, 4 or 8 bytes (pointers,
64-bit scalars, `Nat`/`Int` and records are 8). -/
def fieldAlign (t : RR.Ty) : LowerM Nat := do
  match t with
  | .named n =>
    if n ∈ ["u8", "i8", "bool", "L2RUnit"] then return 1
    if n ∈ ["u16", "i16"] then return 2
    if n ∈ ["u32", "i32", "f32"] then return 4
    match (← get).typeInfos[n]? with
    | some info => if info.shape == .enumLike then return (if info.ctorOrder.size ≤ 256 then 1 else 2) else return 8
    | none => return 8
  | _ => return 8

/-- A `[value]` struct type carrying several values: the arguments of a
join point (J2), or a result of optimization `flatten-structs`
(`flatTupleName`). -/
def tupleType (tys : Array RR.Ty) : LowerM String := do
  if let some n := (← get).tupleTypes[tys]? then return n
  let n ← fresh "Tuple"
  modify fun s => { s with
    tupleTypes := s.tupleTypes.insert tys n
    tupleKeys := s.tupleKeys.insert n tys
    typeItems := s.typeItems.push (.struct n true tys) }
  return n

/-- The structure `L2RFlat.Tuple<k>` (`k` type parameters, one field of
each) that optimization `flatten-structs` (Opt/Flatten) adds to the
environment for a function that returns the fields of a structure instead
of the structure. Unlike every other inductive, its values are a `[value]`
struct of its fields at their own types (`tupleType`): it is lean2rr's own
type, built and projected only by the code of that pass, never boxed. -/
def flatTupleName (k : Nat) : Name := .str `L2RFlat s!"Tuple{k}"

/-- Its constructor. -/
def flatTupleCtor (k : Nat) : Name := .str (flatTupleName k) "mk"

/-- The `k` of `L2RFlat.Tuple<k>`, if `n` is one. -/
def flatTupleArity? (n : Name) : Option Nat :=
  match n with
  | .str `L2RFlat s =>
    if s.startsWith "Tuple" then (List.range 257).find? (fun k => s == s!"Tuple{k}") else none
  | _ => none

/-- The `k` of `L2RFlat.Tuple<k>.mk`, if `n` is that constructor. -/
def flatTupleCtorArity? : Name → Option Nat
  | .str p "mk" => flatTupleArity? p
  | _ => none

/-- The type constants `lowerTypeApp` translates itself (not through
`nominalType`). -/
def builtinTypeNames : List Name :=
  [``UInt8, ``UInt16, ``UInt32, ``UInt64, ``USize, ``Float, ``Float32, ``Bool, ``IO.FS.Handle,
   ``Unit, ``PUnit, ``lcVoid, ``lcErased, ``lcAny, ``Nat, ``Int, ``String, ``Thunk, ``Task,
   ``ByteArray, ``FloatArray, ``Array]

mutual
  /-- Translate a mono type. -/
  partial def lowerType (e : Expr) : LowerM RR.Ty := do
    let e := e.consumeMData.headBeta
    match e with
    | .forallE _ d b _ =>
      -- An erased domain (rule 4, `ErasedDomains`): a unit domain where a
      -- function value can complete after it, otherwise a phantom one.
      if erasedDom d then
        let kept ← match (← get).keptErasedOf[e]? with
          | some b => pure b
          | none => do
            let b := keptErasedHead (← read).erased (skelOf (← getEnv) e) e
            modify fun s => { s with keptErasedOf := s.keptErasedOf.insert e b }
            pure b
        return .fn (if kept then .unit else RR.Ty.phantom) (← lowerType (b.instantiate1 anyExpr))
      return .fn (← lowerType d) (← lowerType (b.instantiate1 anyExpr))
    | .sort _ => return .unit
    | .const .. | .app .. =>
      match e.getAppFn with
      | .const n _ =>
        -- `flatten-structs`' tuples: a `[value]` struct of the fields.
        if let some k := flatTupleArity? n then
          let args := e.getAppArgs
          if args.size == k then return .named (← tupleType (← args.mapM lowerType))
        -- An array: of its element type's storage (`compact-arrays`).
        if n == ``Array && e.getAppNumArgs == 1 then
          return .app "RVec" #[← arrayStorage e.appArg!]
        lowerTypeApp n
      | _ => return RR.Ty.box
    | _ => return RR.Ty.box

  /-- The storage kind of an array element of mono type `t`, as
  `scalarKind?` (`ArrayKinds.lean`) gives it, which the whole-program check
  uses: an enumeration (`enumCtorCount?`, cached) is exactly a type
  `nominalType` gives the shape `enumLike`, stored as its index (`u8`). The
  element type is not lowered here, so that generated types keep their
  order (and names) with the optimization on. -/
  partial def arrayKindOf (t : Expr) : LowerM (Option String) := do
    let .const n _ := t.consumeMData.headBeta.getAppFn | return none
    match n with
    | ``UInt8 | ``Bool => return some "u8"
    | ``UInt16 => return some "u16"
    | ``UInt32 => return some "u32"
    | ``UInt64 | ``USize => return some "u64"
    | ``Float32 => return some "f32"
    | ``Float => return some "f64"
    | _ =>
      let k ← match (← get).enumCounts[n]? with
        | some k => pure k
        | none => do
          let k ← enumCtorCount? n
          modify fun s => { s with enumCounts := s.enumCounts.insert n k }
          pure k
      match k with
      | some k => return if 1 ≤ k && k ≤ 256 then some "u8" else none
      | none => return none

  /-- The storage type of the elements of an `Array t` (`t` a mono type):
  its storage kind (`arrayKindOf`) when the program stores that kind
  compactly (`LowerCtx.compactKindsOn`, optimization `compact-arrays`),
  otherwise `Box` (rule 1: one array of boxes for every other type). A
  `Bool` is stored as its `u8`, an enumeration as its index. -/
  partial def arrayStorage (t : Expr) : LowerM RR.Ty := do
    let on := (← read).compactKindsOn
    if on.isEmpty then return RR.Ty.box
    match ← arrayKindOf t with
    | some k => return if on.contains k then .named k else RR.Ty.box
    | none => return RR.Ty.box

  /-- Translate a mono type whose head is constant `n` (its arguments do
  not change the representation, rule 1; an `Array` with its element type
  is `lowerType`'s). -/
  partial def lowerTypeApp (n : Name) : LowerM RR.Ty := do
    match n with
    | ``UInt8 => return .named "u8"
    | ``UInt16 => return .named "u16"
    | ``UInt32 => return .named "u32"
    | ``UInt64 | ``USize => return .named "u64"
    | ``Float => return .named "f64"
    | ``Float32 => return .named "f32"
    | ``Bool => return .bool
    | ``IO.FS.Handle => return .named "LHandle"
    | ``Unit | ``PUnit | ``lcVoid | ``lcErased => return .unit
    | ``lcAny => return RR.Ty.box
    | ``Nat => return .named "Nat"
    | ``Int => return .named "Int"
    | ``String => return .named "LStr"
    -- One representation each, over `Box`, whatever the element type.
    | ``Thunk | ``Task => return .app "LCell" #[.named (← lazyState (n == ``Task))]
    | ``ByteArray => return .app "RVec" #[.named "u8"]
    | ``FloatArray => return .app "RVec" #[.named "f64"]
    | ``Array => return .app "RVec" #[RR.Ty.box]
    | _ =>
      -- An inductive with computed fields is represented by its
      -- implementation inductive `T._impl` (whose constructors also store
      -- the computed fields); mono code uses both names for the same values.
      if let some (.inductInfo ival) := (← getEnv).find? (n ++ `_impl) then
        return ← nominalType ival
      match (← getEnv).find? n with
      | some (.inductInfo ival) =>
        -- A proposition has no representation (its values are proofs).
        if ival.type.getForallBody.isProp then return .unit
        nominalType ival
      | _ => return RR.Ty.box

  /-- The generated nominal type of inductive `ival` (rule 1 of the
  layouts of generic types: one type per inductive, whatever its
  arguments). Its constructors' fields are computed once,
  from their declared types with every parameter `lcAny`, through Lean's
  own `toMonoTypeKeep` so representation decisions (trivial structures,
  `Decidable`, …) match: a field of a parameter's type (`x : α`) is a
  `Box`, `xs : List α` is the one `List` type, `f : α → β` is `Box → Box`,
  a concrete field (`n : Nat`, `x : Float`) keeps its type. A field whose
  type is a proof or a type (`none`) has no representation; one whose type
  is a parameter is a `Box` at every instantiation, also where the
  parameter is a proof or a type (its value is then `box(0)`). -/
  partial def nominalType (ival : InductiveVal) : LowerM RR.Ty := do
    if let some n := (← get).typeNames.find? ival.name then return .named n
    let name ← fresh s!"T_{nameHint ival.name}_"
    modify fun s => { s with typeNames := s.typeNames.insert ival.name name, typeHeads := s.typeHeads.insert name ival.name }
    let params := Array.replicate ival.numParams anyExpr
    let mut monos : Array (Array (Option Expr)) := #[]
    for ctorName in ival.ctors do
      let ctorTy ← getOtherDeclBaseType ctorName []
      let mut ty ← instantiateForall ctorTy params
      let mut ms := #[]
      repeat
        match ty.headBeta with
        | .forallE _ d b _ =>
          let mono ← toMonoTypeKeep d
          ms := ms.push (if mono.isErased || mono == mkConst ``lcVoid then none else some mono)
          ty := b.instantiate1 anyExpr
        | _ => break
      monos := monos.push ms
    -- Constructor layouts.
    let mut ctors : NameMap CtorLayout := {}
    let mut variants : Array (String × Array RR.Ty) := #[]
    for (ctorName, ms) in ival.ctors.toArray.zip monos do
      let mut fields := #[]
      let mut rrFields := #[]
      for m in ms do
        match m with
        | none => fields := fields.push none
        | some mono =>
          -- A field `Array α` (`Array lcAny` here) of an inductive that the
          -- program also uses with a compact array there (`compact-arrays`,
          -- `arrayFieldInductives`): a `Box`, which holds either array.
          let t ← if mono.isAppOfArity ``Array 1 && mono.appArg!.consumeMData == anyExpr &&
              (← read).boxedArrayFields.contains ival.name then pure RR.Ty.box else lowerType mono
          fields := fields.push (some (rrFields.size, t))
          rrFields := rrFields.push t
      -- `IO.Process.Child`: native Lean's object also carries the pid
      -- (`uint32`) and whether the child was spawned with `setsid`
      -- (`uint8`) after its three fields (`src/runtime/process.cpp`). They
      -- are two hidden fields after the Lean ones, set and read only by the
      -- process glue (Lean code cannot build a `Child`: its constructor is
      -- private to `Init.System.IO`).
      if ival.name == ``IO.Process.Child then
        for t in #[RR.Ty.named "u32", RR.Ty.bool] do
          fields := fields.push (some (rrFields.size, t))
          rrFields := rrFields.push t
      -- The constructor's name relative to its type (`T.c._impl` for the
      -- constructors of a computed-field implementation `T._impl`).
      let base := match ival.name with | .str p "_impl" => p | n => n
      -- Lean's name mangling (as for declarations, `fnName`) has a
      -- demangler, so distinct constructor names give distinct variants:
      -- `«a.b»` (one component) and `a.b` (two) printed alike (review
      -- RV9L-01), and printing with Lean's escapes still merged pseudo-syntax
      -- roots (`«?a.b»`), inaccessible names (`✝`) and macro scopes, which
      -- Lean prints unescaped (RV9L-01a). Plain ASCII names keep their
      -- spelling (`c_node`, `c_a_b`).
      let variant := (ctorName.replacePrefix base .anonymous).mangle "c_"
      -- The record's field order (`fieldOrder`; Opt/FieldOrder sorts by
      -- decreasing alignment, so the record has no padding): Reussir keeps
      -- the given order (the driver turns its own member packing off, see
      -- scripts/l2r.py).
      let aligns ← rrFields.mapM fieldAlign
      let perm := (← read).fieldOrder aligns
      let mut posOf := Array.replicate rrFields.size 0
      for h : r in [:perm.size] do posOf := posOf.set! perm[r] r
      let placed := fields.map (·.map fun (i, t) => (posOf[i]!, t))
      let packed := perm.map (rrFields[·]!)
      ctors := ctors.insert ctorName { variant, numParams := ival.numParams, fields := placed }
      variants := variants.push (variant, packed)
    let shape :=
      if variants.all (·.2.isEmpty) then Shape.enumLike
      else if variants.size == 1 then Shape.struct
      else Shape.enum
    -- A structure with a single field (after dropping irrelevant ones, e.g.
    -- `ST.Out`, the result of every `BaseIO` call, once the world is gone)
    -- is a `[value]` struct, when the configuration says so
    -- (`valueStructs`, Opt/ValueStructs): passed by value, no heap cell per
    -- value. Its field must be of a finished type (or a primitive), so that
    -- no type contains itself by value: a generated type whose fields are
    -- being lowered (an enclosing call) has a name but no `typeInfos` yet.
    let value ← do
      if shape != .struct || !(← read).valueStructs then pure false else
      match variants[0]!.2 with
      | #[.named fn] =>
        if (← get).typeInfos.contains fn then pure true
        else pure !((← get).typeHeads.contains fn)
      | #[.app _ _] | #[.fn ..] => pure true
      | _ => pure false
    let item := match shape with
      | .enumLike => RR.Item.enum name true (if variants.isEmpty then #[("c_impossible", #[])] else variants)
      | .struct => RR.Item.struct name value variants[0]!.2
      | .enum => RR.Item.enum name false variants
    modify fun s => { s with
      typeInfos := s.typeInfos.insert name { name, shape, ctors, ctorOrder := ival.ctors.toArray, value }
      typeItems := s.typeItems.push item }
    return .named name
end

/-- The generated type of inductive `ind` (the same at every type
argument, see `nominalType`), when it has one. -/
def uniformType (ind : Name) : LowerM RR.Ty := do
  let some (.inductInfo _) := (← getEnv).find? ind | return RR.Ty.box
  lowerTypeApp ind

/-- Name of the generated function converting a `Box` to nominal type `t`
(its body is generated at the end). -/
def unboxFn (t : String) : LowerM String := do
  unless ← getPart (·.unboxTargetSet.contains t) do
    modify fun s => { s with unboxTargets := s.unboxTargets.push t, unboxTargetSet := s.unboxTargetSet.insert t }
  return s!"l2r_unbox_{t}"

end LeanToReussir
