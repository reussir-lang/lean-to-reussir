import Lean
import LeanToReussir.MonoTypesKeep
import LeanToReussir.RR
import LeanToReussir.Relevance
import LeanToReussir.Collect
import LeanToReussir.Mono

/-!
# Stage 4 foundations: state and type translation

Translation plan §5.1. Every mono type becomes a Reussir type:

* builtin types map to native Reussir types or runtime (prelude) types;
* erased types (`◾`, types as values) and the IO world (`lcVoid`) become
  `unit` — values of these types still occupy parameter positions, so
  arities are exactly Lean's;
* every other inductive becomes one generated nominal type per
  instantiation, keyed only by its *relevant* type arguments;
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
  table : RelevanceTable
  /-- Functions the runtime prelude defines. -/
  preludeFns : Std.HashSet String := {}
  /-- Result types of the prelude's functions (from their signatures). -/
  preludeRets : Std.HashMap String RR.Ty := {}
  /-- Parameter types of the prelude's non-generic functions. -/
  preludeParams : Std.HashMap String (Array RR.Ty) := {}
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
  /-- Whether `Array Nat`/`Array Int` are the runtime's one-word-per-element
  `LNatArr`/`LIntArr` (`PassConfig.natArrays`); otherwise they are arrays
  like the others. -/
  natArrays : Bool := false
  /-- The order of a constructor's relevant fields in its record, given
  their alignments (`fieldAlign`): the record position of each field, as a
  permutation (`PassConfig.fieldOrder`). Reussir keeps the given order (the
  driver turns its own member packing off). -/
  fieldOrder : Array Nat → Array Nat := fun aligns => (List.range aligns.size).toArray
  /-- Whether the program can ask for an object's identity or sharing
  (`ptrAddrUnsafe`, what inlines to it, `ST.Ref.ptrEq`, `dbgTraceIfShared`;
  `programObservesIdentity`): otherwise a value and an equal copy cannot be
  told apart. -/
  observesIdentity : Bool := true
  /-- Whether the program can read a value as another type than its own
  (`unsafe` code of its own, or a cast justified by `sorry` or an axiom;
  `programCasts`): otherwise a `Box` holding a value of one inductive is
  never read as another, and an unboxing function matches only the
  instantiations of its own inductive (`boxCastable`, `finishUnboxFns`). -/
  programCasts : Bool := true
  /-- The mono declarations of the program (code and extern instances). -/
  decls : NameMap (Decl .pure)
  /-- Instance name ↦ instance key (original declaration and type arguments). -/
  keys : NameMap InstKey

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
parameter types, result type, and how it is called. `id` is an identifier
naming it in variant names. -/
structure FnTarget where
  id : String
  params : Array RR.Ty
  ret : RR.Ty
  call : FnCall
  deriving Inhabited

/-- A variant of a function-value enum besides `z` (the `box(0)`
placeholder) and `raw` (a Reussir closure): `part id m` is target `id`
with its first `m` arguments captured; `wrap src` is a function value of
another representation `src` of the same Lean type. -/
inductive FnVariant where
  | part (id : String) (m : Nat)
  | wrap (src : RR.Ty)
  deriving BEq, Hashable, Inhabited

/-- How a reference's cell stores its element (see `refType`). -/
inductive RefKind where
  /-- `L2RRef_N(Cell<e>)`. -/
  | direct
  /-- `L2RRef_N(Cell<ElemBox(e)>)`, for `[value]` structures. -/
  | boxed (bn : String)
  /-- The prelude's `L2RNatRef` / `L2RIntRef`. -/
  | nat
  | int
  deriving BEq, Inhabited

structure LowerState where
  /-- The state optional passes keep for the whole program (analyses they
  compute once), by the pass's name (`LowerState.getExt?`). -/
  ext : NameMap Dynamic := {}
  /-- Targets of function values, by id. -/
  fnTargets : Std.HashMap String FnTarget := {}
  /-- Variants of each function-value type (an `RR.Ty.fn`), besides `z` and `raw`. -/
  fnVariants : Std.HashMap RR.Ty (Array FnVariant) := {}
  /-- Requested application functions: function type and number of arguments. -/
  fnApplies : Array (RR.Ty × Nat) := #[]
  /-- Function types that some `Box` value is unboxed to. -/
  fnUnboxTargets : Array RR.Ty := #[]
  /-- Generated application functions, with the number of variants of their
  type they were generated for. -/
  fnApplyDone : Std.HashMap (RR.Ty × Nat) Nat := {}
  /-- Conversions between two representations of a function type (source,
  target), and the source variant count their body was generated for. -/
  fnConvs : Array (RR.Ty × RR.Ty) := #[]
  fnConvDone : Std.HashMap (RR.Ty × RR.Ty) Nat := {}
  /-- Mono type (keyed by relevant arguments) ↦ generated type name. -/
  typeNames : Std.HashMap Expr String := {}
  typeInfos : Std.HashMap String TypeInfo := {}
  /-- Generated type name ↦ the (keyed) Lean type it represents, for diagnostics. -/
  typeKeys : Std.HashMap String Expr := {}
  /-- Generated type items, in creation order. -/
  typeItems : Array RR.Item := #[]
  /-- Variants of the uniform `Box` type: boxed Reussir type ↦ variant name. -/
  boxVariants : Array (RR.Ty × String) := #[]
  /-- Types of constants whose value is traversed for tasks when it is
  first computed (`persistCall`); the traversals are generated at the end,
  once all variants of function types and `Box` are known
  (`finishPersistFns`), with the number of variants they were generated
  for. -/
  persistReqs : Array RR.Ty := #[]
  persistDone : Option (Nat × Nat) := none
  /-- Generated `[value]` structs carrying several join-point arguments. -/
  tupleTypes : Std.HashMap (Array RR.Ty) String := {}
  /-- Generated functions (declarations and outlined join points). -/
  fns : Array RR.Item := #[]
  /-- Nominal types that some `Box` value is unboxed to (converter bodies
  are generated at the end, once all `Box` variants are known). -/
  unboxTargets : Array String := #[]
  /-- Array types that some `Box` value is unboxed to, with the name of
  their converter (bodies generated at the end, like `unboxTargets`). -/
  unboxArrTargets : Array (RR.Ty × String) := #[]
  /-- Next once-cell slot for constants. -/
  cafSlots : Nat := 0
  /-- First of the three cell slots holding the current standard streams
  (stdin, stdout, stderr), and the stream record type, once used. -/
  stdSlots : Option Nat := none
  stdStreamTy : Option RR.Ty := none
  /-- Once-cell slots of constants defined by `initialize`. -/
  initSlots : NameMap Nat := {}
  /-- Types whose fields are being lowered, and whether they will be
  boundary types (see `nominalType`). -/
  pendingBoundary : Std.HashMap String Bool := {}
  /-- Whether an inductive's mutual block uses one of its types at other
  arguments than its parameters (`nonUniformInductive`), once computed. -/
  nonUniformInds : NameMap Bool := {}
  /-- Structural conversions being generated (for recursive types). -/
  convsInProgress : Std.HashSet String := {}
  /-- Whether the body of a structural conversion is being generated: a
  conversion it needs is the bare one (`_w`), not the one that records and
  looks up origins (`l2r_origin_note`, see `structConv`). -/
  convNested : Bool := false
  /-- Lean's borrowed parameters of the program's declarations, and the
  variables they lend (`Lower/Borrow`), once computed. -/
  borrowInfo : Option (NameMap (Array Bool) × FVarIdSet) := none
  /-- Generated placeholder (`box(0)`) functions, per type. -/
  zeroFns : Std.HashMap RR.Ty String := {}
  /-- Placeholder functions whose body is being generated. -/
  zeroBusy : Std.HashSet RR.Ty := {}
  /-- Variants of the state machine being built (J4): name, fields, body. -/
  smArms : Array (String × Array (String × RR.Ty) × RR.Block) := #[]
  /-- String literals of the program, by id (see `strLit`). -/
  strLits : Array String := #[]
  strLitIds : Std.HashMap String Nat := {}
  /-- Generated element-wise array conversions, per (source, target) storage. -/
  vecConvs : Std.HashMap (RR.Ty × RR.Ty) String := {}
  /-- State types of thunks and tasks (see `lazyState`): (is a task, value
  type) ↦ generated enum name, and back. -/
  lazyStates : Std.HashMap (Bool × RR.Ty) String := {}
  lazyInfos : Std.HashMap String (Bool × RR.Ty) := {}
  /-- Task state types that IO tasks use, indexed by their runtime tag. -/
  taskTags : Array String := #[]
  /-- Names of generated thunk/task helper functions (see `lazyFn`). -/
  lazyFnNames : Std.HashSet String := {}
  /-- Function types whose identity function (`l2r_fn_addr_T`, see `addrOf`)
  is requested, and the variant count its body was generated for. -/
  fnAddrTargets : Array RR.Ty := #[]
  fnAddrDone : Std.HashMap RR.Ty Nat := {}
  /-- Whether `l2r_box_addr` is requested, and the `Box` variant count its
  body was generated for. -/
  boxAddrWanted : Bool := false
  boxAddrDone : Nat := 0
  /-- Reference types (see `refType`): element type ↦ name, and back (with
  how the cell stores the element). -/
  refTypes : Std.HashMap RR.Ty String := {}
  refInfos : Std.HashMap String (RR.Ty × RefKind) := {}
  /-- Operations on references held in a `Box` (see Lower's
  `refBoxOpFn`): operation and element type. -/
  refBoxOps : Array (String × RR.Ty) := #[]
  counter : Nat := 0

abbrev LowerM := ReaderT LowerCtx (StateRefT LowerState CoreM)

def fresh (pre : String) : LowerM String := do
  let n := (← get).counter
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

def boxName : String := "L2RBox"

/-- The uniform type. -/
def RR.Ty.box : RR.Ty := .named boxName

/-- Types that may cross Reussir's FFI boundary as parameters: integers,
floats, `bool`, and RC pointers (opaque runtime types and shared records). -/
def isBoundaryTy (t : RR.Ty) : LowerM Bool := do
  match t with
  | .named n =>
    if n ∈ ["u8", "u16", "u32", "u64", "i8", "i16", "i32", "i64", "f32", "f64", "bool",
            "LStr", "LBig", "LNatArr", "LIntArr", "LHandle", boxName] then return true
    -- A reference is a shared record (see `refType`).
    if (← get).refInfos.contains n then return true
    match (← get).typeInfos[n]? with
    | some info => return info.shape != .enumLike && !info.value
    -- A type whose fields are being lowered: decided from its shape
    -- beforehand (`nominalType`), so that `Array T` in its own fields has
    -- the representation it has everywhere else.
    | none => return ((← get).pendingBoundary[n]?).getD false
  | .app n _ => return n == "RVec" || n == "LRef" || n == "LCell" || n == "L2RIx"
  -- A function value is a shared enum.
  | .fn .. => return true
  | .cls .. => return false

/-- The state type of a thunk (`task = false`) or task over values of type
`t`: a generated shared enum `{ pending(L2RUnit -> t), busy, done(t),
conv(L2RUnit -> t, Box, u64), convdone(t, Box, u64) }`
(tasks also `bind(L2RUnit -> LCell<S>)`)
held in a runtime cell `LCell<S>` (translation plan §5.14). A thunk
starts `pending` (or `done`, for `Thunk.pure`) and is `busy` while its
closure runs; a task is `done` from the start unless it is a deferred IO
task. -/
def lazyState (task : Bool) (t : RR.Ty) : LowerM String := do
  if let some n := (← get).lazyStates[(task, t)]? then return n
  let n ← fresh (if task then "L2RTask" else "L2RThunk")
  -- `conv`: converted from another representation (see `lazyConv`): the
  -- computation, the original cell (boxed), the original's identity. It
  -- stays `conv` while it is forced (its computation forces the original,
  -- whose state is the copy's, see `lazyGetFn`).
  let cellTy := RR.Ty.app "LCell" #[.named n]
  modify fun s => { s with
    lazyStates := s.lazyStates.insert (task, t) n
    lazyInfos := s.lazyInfos.insert n (task, t)
    typeItems := s.typeItems.push (.enum n false (#[("pending", #[.fn .unit t]), ("busy", #[]), ("done", #[t]),
      ("conv", #[.fn .unit t, RR.Ty.box, .named "u64"]),
      -- `convdone`: a converted cell with its value: the value, the
      -- original (kept, so that its address stays this cell's identity),
      -- the original's identity.
      ("convdone", #[t, RR.Ty.box, .named "u64"])] ++
      -- `bind`: an `IO.bindTask` task before it has run `f` (its computation
      -- yields the task it continues as, see `taskStepFn`).
      (if task then #[("bind", #[.fn .unit cellTy])] else #[])))
    boxVariants := if s.boxVariants.any (·.1 == cellTy) then s.boxVariants
      else s.boxVariants.push (cellTy, s!"b{s.boxVariants.size}") }
  return n

/-- The state type and value type of a thunk or task representation
`LCell<S>`, if `t` is one. -/
def lazyOf? (t : RR.Ty) : LowerM (Option (String × Bool × RR.Ty)) := do
  let .app "LCell" #[.named s] := t | return none
  return (← get).lazyInfos[s]?.map (s, ·)

/-- The element type stored in a runtime array: values that cannot cross the
FFI boundary are wrapped in a one-field shared struct (Lean boxes array
elements too). -/
def arrayElemTy (t : RR.Ty) : LowerM (RR.Ty × Bool) := do
  if ← isBoundaryTy t then return (t, false)
  let key := #[t, .named "__elem_box"]
  if let some n := (← get).tupleTypes[key]? then return (.named n, true)
  let n ← fresh "ElemBox"
  modify fun s => { s with
    tupleTypes := s.tupleTypes.insert key n
    typeItems := s.typeItems.push (.struct n false #[t]) }
  return (.named n, true)

/-- An enumeration (a generated `[value]` enum without fields) or the unit
type, which arrays store as an index (translation plan §5.1, where native
Lean stores a tagged scalar): its index type (`u8`, `u16` or `u32`, by the
number of constructors) and the generated conversions to and from it
(`l2r_ix_of_T`, `l2r_ix_to_T`; an index past the last constructor gives the
last one, as `ofIndex`). -/
def ixStorage? (t : RR.Ty) : LowerM (Option (RR.Ty × String × String)) := do
  let .named tn := t | return none
  let ctors ← if tn == "L2RUnit" then pure #["u"] else
    match (← get).typeInfos[tn]? with
    | some info =>
      if info.shape != .enumLike then return none
      pure (info.ctorOrder.filterMap fun c => (info.ctors.find? c).map (·.variant))
    | none => return none
  let w := RR.Ty.named (if ctors.size ≤ 256 then "u8" else if ctors.size ≤ 65536 then "u16" else "u32")
  let ofFn := s!"l2r_ix_of_{tn}"
  let toFn := s!"l2r_ix_to_{tn}"
  unless (← get).fns.any (fun | .fn n .. => n == ofFn | _ => false) do
    let lit (i : Nat) : RR.Block := ⟨#[("i", some w, .atom (toString i))], .var "i"⟩
    let ofBody : RR.Block :=
      if ctors.isEmpty then .ofExpr (.call "l2r_unreachable" #[w] #[])
      else if tn == "L2RUnit" then lit 0
      else .ofExpr (.mtch (.var "x") (ctors.zipIdx.map fun (v, i) =>
        { ty := tn, ctor := some v, binders := #[], body := lit i : RR.Arm }))
    -- A binary search over the constructor positions.
    let rec search (lo hi : Nat) (fuel : Nat) : RR.Expr :=
      match fuel with
      | 0 => .ctor tn (some ctors[lo]!) #[]
      | fuel + 1 =>
        if hi ≤ lo + 1 then .ctor tn (some ctors[lo]!) #[]
        else
          let mid := (lo + hi) / 2
          .block ⟨#[(s!"m{mid}", some w, .atom (toString mid))],
            .ite (.atom s!"i < m{mid}") (.ofExpr (search lo mid fuel)) (.ofExpr (search mid hi fuel))⟩
    let toBody : RR.Block :=
      if ctors.isEmpty then .ofExpr (.call "l2r_unreachable" #[t] #[])
      else .ofExpr (search 0 ctors.size 64)
    modify fun s => { s with fns := s.fns ++ #[.fn ofFn #[("x", t)] w ofBody, .fn toFn #[("i", w)] t toBody] }
  return some (w, ofFn, toFn)

/-- The storage type of array elements of Reussir type `t`: an index for an
enumeration or the unit type (`ixStorage?`), otherwise as `arrayElemTy`. -/
def arrayStorage (t : RR.Ty) : LowerM RR.Ty := do
  if let some (w, _, _) ← ixStorage? t then return .app "L2RIx" #[w, t]
  return (← arrayElemTy t).1

/-- The element type an array storage type holds, and whether the storage
is a one-field wrapper (see `arrayElemTy`). -/
def storageElem (st : RR.Ty) : LowerM (RR.Ty × Bool) := do
  if let .app "L2RIx" #[_, v] := st then return (v, false)
  let .named n := st | return (st, false)
  for (k, v) in (← get).tupleTypes.toList do
    if v == n && k.size == 2 && k[1]! == .named "__elem_box" then return (k[0]!, true)
  return (st, false)

/-- The representation of an `ST.Ref` whose contents have Reussir type `e`
(translation plan §5.1): a shared record holding Reussir's mutable cell, one
per element type, which stores the element in its own representation (all
aliases of a reference share the record). A `Nat` or `Int` is stored as in
`LNatArr` (a tagged word in a `Cell<u64>`, a big value in a second cell:
the prelude's `L2RNatRef`/`L2RIntRef`), a `[value]` structure in an
`ElemBox` (Reussir's cells do not hold `[value]` records with counted
members); other values as they are, `L2RRef_N(Cell<e>)`. -/
def refType (e : RR.Ty) : LowerM RR.Ty := do
  if let some n := (← get).refTypes[e]? then return .named n
  let register (n : String) (k : RefKind) (item : Option RR.Item) : LowerM RR.Ty := do
    modify fun s => { s with
      refTypes := s.refTypes.insert e n
      refInfos := s.refInfos.insert n (e, k)
      typeItems := match item with | some it => s.typeItems.push it | none => s.typeItems }
    return .named n
  if e == .named "Nat" then return ← register "L2RNatRef" .nat none
  if e == .named "Int" then return ← register "L2RIntRef" .int none
  let direct ← match e with
    | .named t =>
      if t ∈ ["u8", "u16", "u32", "u64", "i8", "i16", "i32", "i64", "f32", "f64", "bool", "L2RUnit"] then pure true
      else if ((← get).typeInfos[t]?.map (·.shape == .enumLike)).getD false then pure true
      else isBoundaryTy e
    | .cls .. => pure false
    | _ => isBoundaryTy e
  let n ← fresh "L2RRef"
  if direct then return ← register n .direct (some (.struct n false #[.app "Cell" #[e]]))
  let (st, _) ← arrayElemTy e
  let .named bn := st | return ← register n .direct (some (.struct n false #[.app "Cell" #[e]]))
  register n (.boxed bn) (some (.struct n false #[.app "Cell" #[st]]))

/-- The element type of reference type `t` and how its cell stores it, if
`t` is a reference type. -/
def refElem? (t : RR.Ty) : LowerM (Option (RR.Ty × RefKind)) := do
  let .named n := t | return none
  return (← get).refInfos[n]?

/-- A string literal: `l2r_str_lit(id)`, which builds the string from a
table of byte strings generated with the program (`strLitTable`). Passing
a Reussir `str` to the runtime would go through a stack slot whose address
escapes, which keeps LLVM from turning tail calls of the enclosing function
into loops. -/
def strLit (s : String) : LowerM RR.Expr := do
  let id ← match (← get).strLitIds[s]? with
    | some id => pure id
    | none =>
      let id := (← get).strLits.size
      modify fun st => { st with strLits := st.strLits.push s, strLitIds := st.strLitIds.insert s id }
      pure id
  return .call "l2r_str_lit" #[] #[.atom (toString id)]

/-- The runtime function behind `strLit`: the literals as Rust byte strings. -/
def strLitTable (lits : Array String) : String :=
  let hex := "0123456789abcdef".toList.toArray
  let esc (s : String) : String := s.toUTF8.foldl (init := "") fun acc b =>
    if b ≥ 0x20 && b < 0x7f && b != 0x22 && b != 0x5c then acc.push (Char.ofNat b.toNat)
    else acc ++ "\\x" |>.push hex[(b / 16).toNat]! |>.push hex[(b % 16).toNat]!
  let items := lits.toList.map fun s => s!"b\"{esc s}\""
  "#[ffi(import)]\nfn l2r_str_lit(id : u64) -> LStr [{ {\n" ++
  s!"    const LITS: &[&[u8]] = &[{", ".intercalate items}];\n" ++
  "    leanrt::string::from_bytes(LITS[id as usize])\n} }];\n"

/-- How a Lean array is represented: the runtime function family
(`l2r_array_*` generic over the storage type, or the one-word
`l2r_natarr_*`/`l2r_intarr_*`), the type arguments its functions take, the
element's storage type, the element's own type, and whether the storage
wraps it. -/
structure ArrayRepr where
  family : String
  tyArgs : Array RR.Ty
  storage : RR.Ty
  value : RR.Ty
  wrapped : Bool
  /-- For an enumeration stored as an index (`ixStorage?`): the conversions
  to and from the index. -/
  ix : Option (String × String) := none

def arrayRepr? (t : RR.Ty) : LowerM (Option ArrayRepr) := do
  match t with
  | .named "LNatArr" => return some { family := "natarr", tyArgs := #[], storage := .named "Nat", value := .named "Nat", wrapped := false }
  | .named "LIntArr" => return some { family := "intarr", tyArgs := #[], storage := .named "Int", value := .named "Int", wrapped := false }
  | .app "RVec" #[st] =>
    let (v, w) ← storageElem st
    let ix ← if st matches .app "L2RIx" _ then pure ((← ixStorage? v).map fun (_, o, t) => (o, t)) else pure none
    return some { family := "array", tyArgs := #[st], storage := st, value := v, wrapped := w, ix }
  | _ => return none

/-- A call of runtime array primitive `l2r_<family>_<op>`. -/
def ArrayRepr.call (r : ArrayRepr) (op : String) (args : Array RR.Expr) : RR.Expr :=
  .call s!"l2r_{r.family}_{op}" r.tyArgs args

/-- Store / load an element (wrapping into the storage type if needed). -/
def ArrayRepr.store (r : ArrayRepr) (x : RR.Expr) : RR.Expr :=
  match r.ix with
  | some (o, _) => .call o #[] #[x]
  | none => if r.wrapped then match r.storage with | .named n => .ctor n none #[x] | _ => x else x
def ArrayRepr.load (r : ArrayRepr) (x : RR.Expr) : RR.Expr :=
  match r.ix with
  | some (_, t) => .call t #[] #[x]
  | none => if r.wrapped then .field x 0 else x

/-- The runtime function implementing Lean array extern `sym` for arrays of
family `fam` (`natarr`, `intarr`): the same argument list, element type
`Nat`/`Int`. -/
def natArrSym? (sym fam : String) : Option String :=
  if sym.startsWith "lean_array_" then some ("lean_" ++ fam ++ "_" ++ (sym.drop 11).toString)
  else if sym == "lean_mk_empty_array_with_capacity" then some s!"lean_mk_empty_{fam}_with_capacity"
  else if sym == "lean_mk_empty_array" then some s!"lean_mk_empty_{fam}"
  else if sym == "lean_mk_array" then some s!"lean_mk_{fam}"
  else none

/-- Relevance of the parameters of inductive `ind` (see `Relevance.lean`). -/
def relevanceOf (ind : Name) (numParams : Nat) : LowerM (Array Bool) := do
  match (← read).table.find? ind with
  | some r => return r
  | none => return Array.replicate numParams true

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

/-- The type constants `lowerTypeApp` translates itself (not through
`nominalType`). -/
def builtinTypeNames : List Name :=
  [``UInt8, ``UInt16, ``UInt32, ``UInt64, ``USize, ``Float, ``Float32, ``Bool, ``IO.FS.Handle,
   ``Unit, ``PUnit, ``lcVoid, ``lcErased, ``lcAny, ``Nat, ``Int, ``String, ``Thunk, ``Task,
   ``ByteArray, ``FloatArray, ``Array, typedRefName]

/-- The key of the generated type for inductive `ival` applied to `args`
(only relevant arguments distinguish instances). -/
def nominalKey (ival : InductiveVal) (args : Array Expr) : LowerM Expr := do
  let rel ← relevanceOf ival.name ival.numParams
  -- Phantom (irrelevant) arguments do not create distinct types.
  let keyArgs := (List.range ival.numParams).toArray.map fun i =>
    if rel.getD i true then (args[i]?.getD anyExpr).consumeMData else erasedExpr
  return mkAppN (.const ival.name []) keyArgs

/-- Whether `e` mentions one of the inductives `all` applied to other
arguments than `ps` (see `nonUniformInductive`). -/
partial def usesOtherArgs (all : List Name) (ps : Array Expr) (e : Expr) : Bool :=
  let args := e.getAppArgs
  let go := usesOtherArgs all ps
  let here := match e.getAppFn with
    | .const j _ => all.contains j && (args.size < ps.size || args.extract 0 ps.size != ps)
    | .forallE _ d b _ | .lam _ d b _ => go d || go b
    | .mdata _ b => go b
    | .letE _ t v b _ => go t || go v || go b
    | .proj _ _ x => go x
    | _ => false
  here || args.any go

/-- Whether the mutual block of inductive `ival` uses one of its types at
other arguments than the block's parameters in a constructor field
(`unsafe inductive Nest α | cons (x : α) (rest : Nest (α × α))`, also nested
in another type, `List (Rose (Option α))`, or a function type). Lean accepts
this only for `unsafe` inductives: a safe inductive always uses its
parameters as they are. -/
def nonUniformInductive (ival : InductiveVal) : LowerM Bool := do
  if let some b := (← get).nonUniformInds.find? ival.name then return b
  let ps := (List.range ival.numParams).toArray.map fun i => Expr.fvar ⟨.num `_l2r_param i⟩
  let go := usesOtherArgs ival.all ps
  let mut r := false
  for ind in ival.all do
    let some (.inductInfo iv) := (← getEnv).find? ind | continue
    for c in iv.ctors do
      let some (.ctorInfo ci) := (← getEnv).find? c | continue
      let mut ty ← instantiateForall ci.type ps
      repeat
        match ty with
        | .forallE _ d b _ =>
          if go d then r := true
          ty := b.instantiate1 anyExpr
        | .mdata _ b => ty := b
        | _ => break
  modify fun s => { s with nonUniformInds := s.nonUniformInds.insert ival.name r }
  return r

/-- Whether instantiation `key` of inductive `ival`, requested while the
fields of the types on the path (`pendingBoundary`) are being lowered,
grows: polymorphic recursion in a type (`unsafe inductive Nest α | cons
(x : α) (rest : Nest (α × α))`), whose instances `Nest Nat`,
`Nest (Nat × Nat)`, … would never end. Only an inductive whose block uses
its types at other arguments (`nonUniformInductive`) can grow: a safe one
(`inductive Tree | node (kids : List (Nat × Tree))`, whose `List Tree`
reaches `List (Nat × Tree)`) is never cut. As for instances of declarations
(Mono's `instanceName`): the key grows if some instantiation of the same
inductive on the path has a relevant argument that the key's argument at
that position strictly contains (or, for type functions, is strictly larger
than), or if that instantiation is the uniform one and the key's arguments
are built from its `lcAny` (`Nest (lcAny × lcAny)`, the uniform type's own
field). Growth that no containment shows is cut by a bound: 256
instantiations of one inductive on the path. Such a key is translated at
the uniform instantiation instead (see `nominalType`). -/
def typeGrowsOnPath (ival : InductiveVal) (key : Expr) : LowerM Bool := do
  let s ← get
  let head := key.getAppFn
  let bs := key.getAppArgs
  unless s.pendingBoundary.toList.any (fun (n, _) =>
      (s.typeKeys[n]?.map (·.getAppFn == head)).getD false) do return false
  unless ← nonUniformInductive ival do return false
  let grows (a b : Expr) : Bool :=
    a != b && a != anyExpr && a != erasedExpr &&
      ((b.find? (· == a)).isSome ||
       ((a.isLambda || b.isLambda) && treeSizeUpTo b 1000 > treeSizeUpTo a 1000))
  let mut same := 0
  for (n, _) in s.pendingBoundary do
    let some k := s.typeKeys[n]? | continue
    unless k.getAppFn == head && k.getAppNumArgs == bs.size do continue
    same := same + 1
    let pairs := (k.getAppArgs.zip bs).filter fun (a, _) => a != erasedExpr
    if pairs.isEmpty then continue
    if pairs.all (·.1 == anyExpr) then
      if pairs.any fun (_, b) => b != anyExpr && !b.isLambda && (b.find? (· == anyExpr)).isSome then
        return true
    else if pairs.any fun (a, b) => grows a b then return true
  return same ≥ 256

/-- The type arguments inductive `ival` is translated at when requested at
`args`, and the key of that translation: `args` themselves, or every
argument `lcAny` (the uniform instantiation) when the request grows
(`typeGrowsOnPath`). -/
def nominalArgs (ival : InductiveVal) (args : Array Expr) : LowerM (Array Expr × Expr) := do
  let key ← nominalKey ival args
  if ival.numParams == 0 || !(← typeGrowsOnPath ival key) then return (args, key)
  let uargs := Array.replicate ival.numParams anyExpr
  return (uargs, ← nominalKey ival uargs)

/-- Whether mono type `e` translates to a generated nominal type whose
fields are being lowered (see `nominalType`). -/
def inProgressType (e : Expr) : LowerM Bool := do
  let e := e.consumeMData.headBeta
  let .const n _ := e.getAppFn | return false
  if builtinTypeNames.contains n then return false
  let ival? := match (← getEnv).find? (n ++ `_impl), (← getEnv).find? n with
    | some (.inductInfo iv), _ => some iv
    | _, some (.inductInfo iv) => if iv.type.getForallBody.isProp then none else some iv
    | _, _ => none
  let some ival := ival? | return false
  let some name := (← get).typeNames[(← nominalArgs ival e.getAppArgs).2]? | return false
  return !(← get).typeInfos.contains name

mutual
  /-- Translate a mono type. -/
  partial def lowerType (e : Expr) : LowerM RR.Ty := do
    let e := e.consumeMData.headBeta
    match e with
    | .forallE _ d b _ => return .fn (← lowerType d) (← lowerType (b.instantiate1 anyExpr))
    | .sort _ => return .unit
    | .const .. | .app .. =>
      match e.getAppFn with
      | .const n _ => lowerTypeApp n e.getAppArgs
      | _ => return RR.Ty.box
    | _ => return RR.Ty.box

  partial def lowerTypeApp (n : Name) (args : Array Expr) : LowerM RR.Ty := do
    if n == typedRefName then
      return ← refType (← match args[0]? with
        | some a => lowerType a
        | none => pure RR.Ty.box)
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
    | ``Thunk | ``Task =>
      let elem ← match args[0]? with
        | some a => lowerType a
        | none => pure RR.Ty.box
      return .app "LCell" #[.named (← lazyState (n == ``Task) elem)]
    | ``ByteArray => return .app "RVec" #[.named "u8"]
    | ``FloatArray => return .app "RVec" #[.named "f64"]
    | ``Array =>
      let elem ← match args[0]? with
        | some a => lowerType a
        | none => pure RR.Ty.box
      -- Arrays of `Nat`/`Int` store one word per element, like Lean's
      -- boxed scalars (runtime `LNatArr`/`LIntArr`).
      if (← read).natArrays then
        if elem == .named "Nat" then return .named "LNatArr"
        if elem == .named "Int" then return .named "LIntArr"
      return .app "RVec" #[← arrayStorage elem]
    | _ =>
      -- An inductive with computed fields is represented by its
      -- implementation inductive `T._impl` (whose constructors also store
      -- the computed fields); mono code uses both names for the same values.
      if let some (.inductInfo ival) := (← getEnv).find? (n ++ `_impl) then
        return ← nominalType ival args
      match (← getEnv).find? n with
      | some (.inductInfo ival) =>
        -- A proposition has no representation (its values are proofs).
        if ival.type.getForallBody.isProp then return .unit
        nominalType ival args
      | _ => return RR.Ty.box

  /-- The generated nominal type for an instantiated inductive. -/
  partial def nominalType (ival : InductiveVal) (args : Array Expr) : LowerM RR.Ty := do
    -- A field type that grows (polymorphic recursion in a type, `Nest (α × α)`
    -- in `Nest α`) is the uniform instantiation (`nominalArgs`); values of the
    -- typed instantiations convert to it where they meet (§5.1).
    let (args, key) ← nominalArgs ival args
    if let some n := (← get).typeNames[key]? then return .named n
    let name ← fresh s!"T_{nameHint ival.name}_"
    modify fun s => { s with typeNames := s.typeNames.insert key name, typeKeys := s.typeKeys.insert name key }
    -- The fields' mono types, through Lean's own `toMonoTypeKeep` so
    -- representation decisions (trivial structures, `Decidable`, …) match;
    -- `none` for an erased field.
    let mut monos : Array (Array (Option Expr)) := #[]
    for ctorName in ival.ctors do
      let ctorTy ← getOtherDeclBaseType ctorName []
      let mut ty ← instantiateForall ctorTy (args[:ival.numParams].toArray.map (·.consumeMData))
      let mut ms := #[]
      repeat
        match ty.headBeta with
        | .forallE _ d b _ =>
          let mono ← toMonoTypeKeep d
          ms := ms.push (if mono.isErased || mono == mkConst ``lcVoid then none else some mono)
          ty := b.instantiate1 anyExpr
        | _ => break
      monos := monos.push ms
    -- Whether the type will be a boundary type (a shared record), decided
    -- from its shape before its fields are lowered: a field `Array T` (a
    -- rose tree's children) must get the storage `Array T` gets everywhere
    -- else, `RVec<T>` rather than `RVec<ElemBox(T)>`. A one-field structure
    -- is a `[value]` struct (below) unless its field is of a type whose
    -- fields are being lowered too.
    let relCounts := monos.map fun ms => (ms.filter Option.isSome).size +
      (if ival.name == ``IO.Process.Child then 2 else 0)
    let predictValue ← do
      if !(← read).valueStructs || relCounts.size != 1 || relCounts[0]! != 1 then pure false else
      match (monos[0]!.filterMap id)[0]? with
      | some m => pure !(← inProgressType m)
      | none => pure false
    let boundary := relCounts.any (· > 0) && !predictValue
    modify fun s => { s with pendingBoundary := s.pendingBoundary.insert name boundary }
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
          let t ← lowerType mono
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
      let rel := (ctorName.replacePrefix base .anonymous).toString (escape := false)
      let variant := "c_" ++ identEscape rel
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
    -- no type contains itself by value.
    let value ← do
      if shape != .struct || !predictValue then pure false else
      match variants[0]!.2 with
      | #[.named fn] =>
        if (← get).typeInfos.contains fn then pure true
        else pure !((← get).typeKeys.contains fn)
      | #[.app _ _] | #[.fn ..] => pure true
      | _ => pure false
    let item := match shape with
      | .enumLike => RR.Item.enum name true (if variants.isEmpty then #[("c_impossible", #[])] else variants)
      | .struct => RR.Item.struct name value variants[0]!.2
      | .enum => RR.Item.enum name false variants
    modify fun s => { s with
      typeInfos := s.typeInfos.insert name { name, shape, ctors, ctorOrder := ival.ctors.toArray, value }
      typeItems := s.typeItems.push item
      pendingBoundary := s.pendingBoundary.erase name }
    return .named name
end

/-- The variant of `Box` holding values of type `t`. -/
def boxVariant (t : RR.Ty) : LowerM String := do
  if let some (_, v) := (← get).boxVariants.find? (·.1 == t) then return v
  let v := s!"b{(← get).boxVariants.size}"
  modify fun s => { s with boxVariants := s.boxVariants.push (t, v) }
  return v

/-- The uniform instance of an inductive: every relevant type argument is
`lcAny` (so data of those types is stored as `Box`). -/
def uniformType (ind : Name) : LowerM RR.Ty := do
  let some (.inductInfo ival) := (← getEnv).find? ind | return RR.Ty.box
  lowerTypeApp ind ((List.range ival.numParams).toArray.map fun _ => anyExpr)

/-- Name of the generated function converting a `Box` to nominal type `t`
(its body is generated at the end). -/
def unboxFn (t : String) : LowerM String := do
  unless (← get).unboxTargets.contains t do
    modify fun s => { s with unboxTargets := s.unboxTargets.push t }
  return s!"l2r_unbox_{t}"

/-- Name of the generated function converting a `Box` to array type `t`
(its body is generated at the end): an array may have been boxed under the
variant of any array representation of the same Lean type, e.g. as
`RVec<Box>` when it was built by uniform-representation code. -/
def unboxArrFn (t : RR.Ty) : LowerM String := do
  if let some (_, f) := (← get).unboxArrTargets.find? (·.1 == t) then return f
  let f := s!"l2r_unbox_arr_{(← get).unboxArrTargets.size}"
  modify fun s => { s with unboxArrTargets := s.unboxArrTargets.push (t, f) }
  return f

/-- A `[value]` struct type carrying several join-point arguments. -/
def tupleType (tys : Array RR.Ty) : LowerM String := do
  if let some n := (← get).tupleTypes[tys]? then return n
  let n ← fresh "Tuple"
  modify fun s => { s with
    tupleTypes := s.tupleTypes.insert tys n
    typeItems := s.typeItems.push (.struct n true tys) }
  return n

/-- Relevance for every inductive mentioned by the program's types. -/
def programRelevance (decls : Array (Decl .pure)) : CoreM RelevanceTable := do
  let env ← getEnv
  let inds := decls.foldl (fun s d => foldDeclTypes (addInductives env) d s) ({} : NameSet)
  let inds := closeInductives env inds
  let (table, _) ← Meta.MetaM.run' <| computeRelevance inds.toArray
  return table

end LeanToReussir
