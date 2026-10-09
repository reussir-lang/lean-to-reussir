import LeanToReussir.Lower.LazyForce
import LeanToReussir.CompileRecord

/-! # Conversions -/

namespace LeanToReussir
open Lean Compiler LCNF

/-- The inductive a generated nominal type represents. -/
def nominalHead (n : String) : LowerM (Option Name) := do
  return (← get).typeHeads[n]?

/-- Whether a value of type `t` can hold a task (in fields, array
elements, a task's value, a thunk's value or computation, a function
value's captured values, a `Box`'s payload, a reference's value): a search
of the types reachable from `t`, each looked at once (the least fixed
point, for recursive types; a search along every path was exponential in
the number of function types of polymorphic recursion). With `final`, the
variants of function types and the payloads of `Box` are final (the walks
generated at the end, `holdsTask`); otherwise any function value or `Box`
may hold one (`mayHoldTask`). -/
partial def typeHoldsTask (t : RR.Ty) (final : Bool) : LowerM Bool := do
  go t (← IO.mkRef {})
where
  go (t : RR.Ty) (seen : IO.Ref (Std.HashSet RR.Ty)) : LowerM Bool := do
    if (← seen.get).contains t then return false
    seen.modify (·.insert t)
    match t with
    | .app "LCell" _ =>
      match ← lazyOf? t with
      | some (_, true) => return true
      | some (_, false) => return (← go RR.Ty.box seen) || (← go (.fn .unit RR.Ty.box) seen)
      | none => return false
    | .app "RVec" #[st] => go st seen
    | .fn .. =>
      unless final do return true
      for v in (← getPart (·.fnVariants)).getD t.rt #[] do
        for f in ← fnVariantFields v do
          if ← go f seen then return true
      return false
    | .named n =>
      if n == boxName then
        unless final do return true
        for (vt, _) in ← boxPayloads do
          if ← go vt seen then return true
        return false
      if let some info := (← get).typeInfos[n]? then
        for c in info.ctorOrder do
          let some l := info.ctors.find? c | continue
          for ft in l.posTys do
            if ← go ft seen then return true
        return false
      -- A reference, through its value.
      if ← isRefType t then return ← go RR.Ty.box seen
      match ← tupleFields? n with
      | some fields =>
        for ft in fields do
          if ← go ft seen then return true
        return false
      | none => return false
    | _ => return false

/-- Whether a value of type `t` may contain a task, as far as can be told
before all variants of function types and `Box` are known
(`typeHoldsTask`). In a program that creates no task
(`LowerCtx.createsTasks`: no extern that makes an unfinished task or a
promise) no value holds one: the walk of a constant could wait for nothing
(a `Task.pure` cell has finished). -/
def mayHoldTask (t : RR.Ty) : LowerM Bool := do
  unless (← read).createsTasks do return false
  typeHoldsTask t (final := false)

/-- The name of the traversal of values of type `t` for tasks
(`finishPersistFns`). -/
def persistFnName (t : RR.Ty) : String := s!"l2r_persist_{t.enc}"

/-- `l2r_persist_T(v)` for the value `v : t` of a constant when it is first
computed, if `t` may contain tasks: native Lean calls `lean_mark_persistent`
on a closed term when it is first evaluated (`lean_obj_once_cold`), which
waits for every task it reaches (`lean_task_get`), through fields, arrays,
the values of tasks, thunks (their computation, or their value: not
forcing them), closures (their captured values), references (their
value) and boxed values. A
`Task.spawn` extracted as a closed term has finished once the term has
been evaluated. The traversal is generated at the end
(`finishPersistFns`). -/
def persistCall (t : RR.Ty) (v : RR.Expr) : LowerM (Option RR.Expr) := do
  unless ← mayHoldTask t do return none
  unless (← get).persistReqs.contains t do
    modify fun s => { s with persistReqs := s.persistReqs.push t }
  return some (.call (persistFnName t) #[] #[v])

/-- The accessor of a constant (a declaration without parameters): its value
is computed once, by `<name>_init`, and kept in a runtime once-cell for the
rest of the run, like native Lean's CAFs and closed terms (translation plan
§5.12). The cell stores a boundary type; other values are boxed. A value
that may contain tasks first waits for them (`persistCall`), unless `walk`
is false: a placeholder (`zeroTry`) is natively `box(0)`, which
`lean_mark_persistent` never sees, and the never-forced `pending` cell one
can hold must not be run.

The accessor reads the cell in one place, after the test:

    let r : u64 = if l2r_once_ready(k) { 0 }
                  else { if l2r_once_claim(k) { 0 } else { l2r_once_put<T>(k, init) } };
    l2r_once_get<T>(k)

`l2r_once_ready` is one load from the runtime's table at a fixed address
(the slot is a literal), and `l2r_once_get` loads the same word again,
which LLVM merges: a read of a set constant is one load, a test and the
increment, with no call. `l2r_once_claim` (the scheduler's wait for a
context computing it, and the slots whose word is 0) and the computation
are the slow path. The computation `<name>_init` runs once: it is kept out
of rrc's MLIR inliner (`anchoredFns`), so that the accessor stays small
enough to be inlined where the constant is read (a literal table's
initializer, a run of pushes of boxed immediates, made the accessor too big
for the loops that read it: tests/runtime/const-read-check.sh). -/
def cafAccessor (name : String) (ret : RR.Ty) (walk := true) : LowerM RR.Item := do
  let slot ← getPart (·.cafSlots)
  modify fun s => { s with cafSlots := slot + 1, cafInits := s.cafInits.push (name ++ "_init") }
  let (st, boxed) ← cellStorage ret
  let wrap (e : RR.Expr) : RR.Expr := match st with
    | .named bn => if boxed then .ctor bn none #[e] else e
    | _ => e
  let unwrap (e : RR.Expr) : RR.Expr := if boxed then .field e 0 else e
  let k := RR.Expr.atom (toString slot)
  let init := RR.Expr.call (name ++ "_init") #[] #[]
  let init := match ← (if walk then persistCall ret (.var "v") else pure none) with
    | some p => RR.Expr.block ⟨#[("v", some ret, init), ("p", some (.named "u64"), p)], .var "v"⟩
    | none => init
  -- `l2r_once_claim`: a context of the runtime's scheduler that needs the
  -- value while another computes it waits for it.
  let zero := RR.Block.ofExpr (.atom "0")
  let fill := RR.Expr.ite (.call "l2r_once_ready" #[] #[k]) zero
    (.ofExpr (.ite (.call "l2r_once_claim" #[] #[k]) zero
      (.ofExpr (.call "l2r_once_put" #[st] #[k, wrap init]))))
  let body : RR.Block := ⟨#[("r", some (.named "u64"), fill)], unwrap (.call "l2r_once_get" #[st] #[k])⟩
  return .fn name #[] ret body

/-- The placeholder of `t` (`zeroValue`), searched for depth first: a
constructor without fields if there is one, else the first constructor
whose fields have placeholders (a reference: its element's; a thunk or
task: a cell `done` with its value's, else a cell `pending` with a function
value that is never applied, so that any such cell has one). A type whose
placeholder is being built (an enclosing call: `zeroBusy`) cannot be used
for a field, which keeps the placeholders finite; a constructor that needs
one is skipped, and so is one whose field turns out to have no placeholder
(the search goes on with the next). The result is a call of a generated
function `l2r_zero_N`, kept for every later use (`zeroFns`): it is a finite
value of `t` whatever types were avoided to find it. Or it is `none` when
there is no placeholder avoiding those types, with the smallest depth of
an enclosing type the search avoided (`low`); only a `none` that avoided no
type enclosing `t` holds wherever `t` is asked for, and is kept
(`zeroNone`). A placeholder that
would allocate (a string, an array, a record, a reference, a boxed unit)
is built once and kept in a once-cell like a constant (`cafAccessor`, but
without the walk for tasks: see there): `Array.modify` stores one per
update, and it is never inspected, so a shared value does as well as a
fresh one. -/
partial def zeroTry (t : RR.Ty) : LowerM (Option RR.Expr × Nat) := do
  let inf := 1000000000
  if t == .unit then return (some .unitVal, inf)
  if (← get).zeroNone.contains t then return (none, inf)
  if let some f := (← get).zeroFns[t]? then return (some (.call f #[] #[]), inf)
  if let some d := (← get).zeroBusy[t]? then return (none, d)
  let depth ← getPart (·.zeroBusy.size)
  let f ← fresh "l2r_zero_"
  modify fun s => { s with zeroBusy := s.zeroBusy.insert t depth }
  let lit (text : String) : RR.Block := ⟨#[("z", some t, .atom text)], .var "z"⟩
  -- The placeholders of `tys`, unless one of them is being built or has
  -- none (`low`: the smallest depth avoided).
  let fieldsZero (tys : Array RR.Ty) : LowerM (Option (Array RR.Expr) × Nat) := do
    let busy ← getPart (·.zeroBusy)
    let hit := tys.foldl (fun m ft => match busy[ft]? with | some d => min m d | none => m) inf
    if hit < inf then return (none, hit)
    let mut vals := #[]
    let mut low := inf
    for ft in tys do
      let (v?, l) ← zeroTry ft
      low := min low l
      let some v := v? | return (none, low)
      vals := vals.push v
    return (some vals, low)
  let (body?, low) : Option RR.Block × Nat ← match t with
    | .named n =>
      if n ∈ ["u8", "u16", "u32", "u64", "i8", "i16", "i32", "i64"] then pure (some (lit "0"), inf)
      else if n ∈ ["f32", "f64"] then pure (some (lit "0.0"), inf)
      else if n == "bool" then pure (some (.ofExpr (.atom "false")), inf)
      else if n == "Nat" then
        pure (some ⟨#[("z", some (.named "u64"), .atom "0")], .call "l2r_nat_small" #[] #[.var "z"]⟩, inf)
      else if n == "Int" then
        pure (some ⟨#[("z", some (.named "i64"), .atom "0")], .call "l2r_int_small" #[] #[.var "z"]⟩, inf)
      else if n == "LStr" then pure (some (.ofExpr (← strLit "")), inf)
      else if n == boxName then pure (some (.ofExpr (← boxZero)), inf)
      else if ← isRefType t then
        -- A reference (never used: any cell will do).
        let (vs?, l) ← fieldsZero #[RR.Ty.box]
        pure (vs?.map fun vs => .ofExpr (refNew t vs[0]!), l)
      else if let some info := (← get).typeInfos[n]? then
        -- A constructor without fields, else the first whose fields have
        -- placeholders.
        let fieldsOf (layout : CtorLayout) := layout.posTys
        let cands := info.ctorOrder.filterMap info.ctors.find?
        let build (layout : CtorLayout) (vals : Array RR.Expr) : RR.Block :=
          .ofExpr <| match info.shape with
            | .struct => .ctor n none vals
            | _ => .ctor n (some layout.variant) vals
        match cands.find? (fieldsOf · |>.isEmpty) with
        | some layout => pure (some (build layout #[]), inf)
        | none =>
          let mut found : Option RR.Block := none
          let mut low := inf
          for layout in cands do
            let (vs?, l) ← fieldsZero (fieldsOf layout)
            low := min low l
            if let some vs := vs? then
              found := some (build layout vs)
              break
          pure (found, low)
      else
        -- Generated positional structs (`Tuple…`, `ElemBox…`).
        match ← tupleFields? n with
        | some fields =>
          let (vs?, l) ← fieldsZero fields
          pure (vs?.map fun vs => .ofExpr (.ctor n none vs), l)
        | none => pure (none, inf)
    | .app "RVec" #[e] => pure (some (.ofExpr (.call "l2r_array_empty" #[e] #[])), inf)
    | .app "LCell" _ =>
      match ← lazyOf? t with
      | some (z, _) =>
        let vt := RR.Ty.box
        match ← fieldsZero #[vt] with
        | (some vs, l) => pure (some (.ofExpr (lazyDone z vs[0]!)), l)
        | (none, _) =>
          -- A cell that is never forced: `pending` with a function value
          -- that is never applied.
          let ft := RR.Ty.fn .unit vt
          pure (some (.ofExpr (.call "l2r_lcell_new" #[.named z]
            #[.ctor z (some "pending") #[.ctor (RR.fnTypeName ft) (some "z") #[]]])), inf)
      | none => pure (none, inf)
    -- A function value that is never applied (applying it gives a zero).
    | .fn .. => pure (some (.ofExpr (.ctor (RR.fnTypeName t) (some "z") #[])), inf)
    | _ => pure (none, inf)
  modify fun s => { s with zeroBusy := s.zeroBusy.erase t }
  -- No placeholder: that holds wherever `t` is asked for only if the search
  -- avoided no type enclosing `t`.
  let kept := low ≥ depth
  let low := if kept then inf else low
  let some body := body? | do
    if kept then
      let item := RR.Item.fn f #[] t (.ofExpr (.call "l2r_unreachable" #[t] #[]))
      modify fun s => { s with zeroNone := s.zeroNone.insert t }
      modify fun s => { s with zeroFns := s.zeroFns.insert t f }
      modify fun s => { s with fns := s.fns.push item }
    return (none, low)
  -- A placeholder holds everywhere (a finite value of `t`, built from
  -- functions that are finished).
  modify fun s => { s with zeroFns := s.zeroFns.insert t f }
  -- Heap values are shared (a nullary constructor of a shared enum does not
  -- allocate).
  let heap ← match t with
    | .named n =>
      if n == "LStr" || (n == boxName && boxZeroAllocates) || (← isRefType t) then pure true
      else match (← get).typeInfos[n]? with
        | some info => pure (info.shape != .enumLike && !info.value)
        | none => pure (← elemBoxOf? t).isSome
    | .app "RVec" _ | .fn .. => pure true
    | _ => pure false
  let nullary := match body with
    | ⟨#[], .ctor _ _ #[]⟩ => true
    | _ => false
  if heap && !nullary && (← read).cachePlaceholders then
    let acc ← cafAccessor f t (walk := false)
    modify fun s => { s with fns := s.fns.push (.fn (f ++ "_init") #[] t body) |>.push acc }
  else
    modify fun s => { s with fns := s.fns.push (.fn f #[] t body) }
  return (some (.call f #[] #[]), inf)

/-- A placeholder of Reussir type `t`. Lean passes `box(0)` for values that
are never inspected: erased arguments (`◾`) at relevant types, and the
`unsafeCast ()` its library stores into array slots so that the element
being updated stays unshared (`Array.modifyMUnsafe`, `Array.mapMUnsafe`).
lean2rr materializes `box(0)` at the expected type as that type's zero:
`0`, `false`, a constructor whose fields have zeros, a closure returning a
zero, an empty array (for `Nat`, `Bool` and enumerations this is exactly
what `box(0)` denotes in Lean). Each placeholder is a generated function
`l2r_zero_N` (`zeroTry`). Only a type without a finite value (`Empty`, a
type whose every constructor needs itself) gets `l2r_unreachable`; such a
placeholder is evaluated only where no value of the type can exist. -/
def zeroValue (t : RR.Ty) : LowerM RR.Expr := do
  if t == .unit then return .unitVal
  if let (some e, _) ← zeroTry t then return e
  match (← get).zeroFns[t]? with
  | some f => return .call f #[] #[]
  | none => return .call "l2r_unreachable" #[t] #[]

/-- Whether type `t` has a finite placeholder (`zeroValue` builds no
`l2r_unreachable` into it). -/
def zeroFinite (t : RR.Ty) : LowerM Bool := do
  if t == .unit then return true
  return (← zeroTry t).1.isSome

/-- The box of constant `v : t` (a call of a nullary declaration, or a
literal), built once and kept in a once-cell (`cafAccessor`, without the
walk for tasks: the constant's own accessor walked its value): the
accessor `l2r_boxed_N`, one per constant and type. -/
def boxedConst (v : RR.Expr) (t : RR.Ty) : LowerM RR.Expr := do
  let key := match v with
    | .call f _ _ => s!"{f}:{t.enc}"
    | .atom a => s!"#{a}:{t.enc}"
    | _ => ""
  if let some f ← getPart (·.boxedConstFns[key]?) then return .call f #[] #[]
  let f ← fresh "l2r_boxed_"
  modify fun s => { s with boxedConstFns := s.boxedConstFns.insert key f }
  let body : RR.Block := ⟨#[("c", some t, v)], ← boxValue (.var "c") t⟩
  let acc ← cafAccessor f RR.Ty.box (walk := false)
  modify fun s => { s with fns := s.fns.push (.fn (f ++ "_init") #[] RR.Ty.box body) |>.push acc }
  return .call f #[] #[]

/-- `e : t` boxed (the box API's `boxValue`), as native Lean boxes:
- a placeholder of `t` (`zeroValue`: Lean's `box(0)` read at `t`) is
  `box(0)` again (`l2r_any_unit`), not `t`'s zero boxed. `Array.modify`
  stores `unsafeCast ()` in the slot it updates: on an `Array Float` that
  was `0.0` boxed, a new cell per update. `box(0)` reads back as `t`'s
  zero at every type (`boxUnbox`);
- with `boxed-consts`, a variable bound to a constant whose boxing
  allocates (`closedLets`, `boxAllocates`) is boxed once
  (`boxedConst`), as Lean's `_boxed_const`: the default of `a[i]!` on an
  `Array Float` (`instInhabitedFloat`) was a new cell per read. Not in
  the body of a declaration without parameters (`inConstBody`), which runs
  once: a once-cell there saves nothing (a table of 600 big `UInt64`
  literals had 1200 more functions).
A variable's value is in `closedLets` (bound in `lowerCode`), a
placeholder also in line (`coerce` of a unit-like value). -/
def boxOf (e : RR.Expr) (t : RR.Ty) : LowerM RR.Expr := do
  let bound ← match e with
    | .var n => pure <| (← getPart (·.closedLets[n]?)).bind fun (v, vt) => if vt == t then some v else none
    | _ => pure none
  if let .call f #[] #[] := bound.getD e then
    if (← getPart (·.zeroFns[t]?)) == some f then return ← boxZero
  if let some v := bound then
    if (← read).boxedConsts && !(← getPart (·.inConstBody)) && (← boxAllocates t) then
      return ← boxedConst v t
  boxValue e t

/-- Unwrap a `Box` at Reussir type `t`, fixed by the Lean types (the box
API's `boxUnbox`): its payload, or, for `box(0)`, the placeholder of `t`
(see `zeroValue`); any other payload is unreachable (the box released
first), or goes to the generated unboxing function `slow` (values of other
types read through `unsafeCast`). A function value (the field of a
`[value]` struct) through the generated unboxing function of its type
(`unboxFnFn`). -/
def unboxMatch (e : RR.Expr) (t : RR.Ty) (slow : Option String := none) : LowerM RR.Expr :=
  boxUnbox e t zeroValue unboxFnFn slow

/-- An enumeration: `bool`, or a generated `[value]` enum without fields. -/
def isEnumName (n : String) : LowerM Bool := do
  if n == "bool" then return true
  return ((← get).typeInfos[n]?.map (·.shape == .enumLike)).getD false

/-- The word `lean_unbox` gives for value `e` of Reussir type `n` natively
represented by a boxed scalar of its own (`UInt8/16/32`, `Char`, `Bool`, an
enumeration: its index), as `u64`. `none` for other types. -/
def scalarWord (e : RR.Expr) (n : String) : LowerM (Option RR.Expr) := do
  let u64 := RR.Ty.named "u64"
  if n ∈ ["u8", "u16", "u32"] then return some (.cast e u64)
  if n == "bool" then
    let o ← fresh "ix"
    return some (.ite e ⟨#[(o, some u64, .atom "1")], .var o⟩ ⟨#[(o, some u64, .atom "0")], .var o⟩)
  if ← isEnumName n then return some (.call (← enumIndexFn n) #[] #[e])
  return none

/-- Whether a generated type has a constructor without relevant fields
(natively the boxed scalar of its index). -/
def hasNullaryCtor (info : TypeInfo) : Bool :=
  info.ctorOrder.any fun c => (info.ctors.find? c).any (·.fields.all Option.isNone)

/-- Lean's native layout slot of each field of constructor `c` (Lean's own
`getCtorLayout`): `(0, i, 8)` the `i`-th object field, `(1, i, 8)` the
`i`-th `usize` field, `(2, offset, size)` a scalar in the scalar area;
`none` for a field without data. `none` if Lean has no layout for it. -/
def nativeSlots (c : Name) : LowerM (Option (Array (Option (Nat × Nat × Nat)))) := do
  try
    let l ← Lean.Compiler.LCNF.getCtorLayout c
    return some (l.fieldInfo.map fun
      | .object i _ => some (0, i, 8)
      | .usize i => some (1, i, 8)
      | .scalar sz off _ => some (2, off, sz)
      | _ => none)
  catch _ => return none

/-- Whether constructor `c` (layout `l`) is natively a boxed scalar (the
`lean_box` of its index): it has no field with data. -/
def nativeScalarCtor (c : Name) (l : CtorLayout) : LowerM Bool := do
  match ← nativeSlots c with
  | some ss => return ss.all Option.isNone
  | none => return l.fields.all Option.isNone

/-- Whether `[value]` struct `n` is natively a constructor object with one
field: Lean does not erase its inductive to the field
(`hasTrivialImpureStructure?` gives `none`: an `unsafe` or recursive
inductive). Lean erases the others (`ST.Out σ α`, whose other field is a
`Void σ`), and so do generated structs of no inductive (`false`). -/
def valueStructIsObject (n : String) : LowerM Bool := do
  let some ind := (← get).typeHeads[n]? | return false
  try return (← hasTrivialImpureStructure? ind).isNone
  catch _ => return false

/-- A generated type whose values are heap objects natively when they have
fields: a shared struct or enum, or a `[value]` struct that Lean keeps as
a constructor object (`valueStructIsObject`); not an enumeration. -/
def isObjectNominal (n : String) : LowerM Bool := do
  match (← get).typeInfos[n]? with
  | some info =>
    if info.shape == .enumLike then return false
    if info.value then return ← valueStructIsObject n
    return true
  | none => return false

/-- The word lean2rr gives a heap object read as a word (`unsafeCast` to a
boxed scalar type). Natively that word is the object's address shifted
(`lean_unbox`): nonzero, a multiple of 4, far above any constructor index,
and different on every run. lean2rr has no such address, so it uses a
deterministic number with those properties: `2^44 + 8i` for a constructor
with fields of index `i` (constructors stay distinct), `2^44` for other
objects (plan §10). -/
def objectWordBase : Nat := 2 ^ 44

/-- `l2r_ctor_word_T(x)`: the word `lean_unbox` reads from a value of
generated type `tn`. A constructor without fields is natively the boxed
scalar of its index, so it reads as that index. A constructor with fields
is natively an object (`objectWordBase`). -/
def ctorWordFn (tn : String) (info : TypeInfo) : LowerM String := do
  let name := s!"l2r_ctor_word_{tn}"
  unless (← hasFn name) do
    let u64 := RR.Ty.named "u64"
    let mut arms : Array RR.Arm := #[]
    let mut complete := true
    for h : i in [:info.ctorOrder.size] do
      let some l := info.ctors.find? info.ctorOrder[i] | complete := false; continue
      let binders := Array.replicate (l.fields.filterMap id).size (none : Option String)
      let w := if ← nativeScalarCtor info.ctorOrder[i] l then i else objectWordBase + 8 * i
      arms := arms.push { ty := tn, ctor := some l.variant, binders,
                          body := ⟨#[("i", some u64, .atom (toString w))], .var "i"⟩ }
    unless complete && !arms.isEmpty do
      arms := arms.push { ty := tn, ctor := none, binders := #[], body := .ofExpr (.call "l2r_unreachable" #[u64] #[]) }
    let body : RR.Expr := match info.shape, arms[0]? with
      | .struct, some a => .block a.body
      | _, _ => .mtch (.var "x") arms
    modify fun s => { s with fns := s.fns.push (.fn name #[("x", .named tn)] u64 (.ofExpr body)) }
  return name

/-- `l2r_ctor_of_word_T(w)`: the value of generated type `tn` that is the
boxed scalar `w` natively: its constructor `w` when that has no fields (a
word past the last constructor selects the last one, as Lean's `switch`
does); otherwise unreachable (natively an object read from a scalar). -/
def ctorOfWordFn (tn : String) (info : TypeInfo) : LowerM String := do
  let name := s!"l2r_ctor_of_word_{tn}"
  unless (← hasFn name) do
    let u64 := RR.Ty.named "u64"
    let t := RR.Ty.named tn
    let ls := info.ctorOrder.filterMap info.ctors.find?
    let nullary (l : CtorLayout) := l.fields.all Option.isNone
    let mk (l : CtorLayout) : RR.Expr := if info.shape == .struct then .ctor tn none #[] else .ctor tn (some l.variant) #[]
    let unreachable := RR.Expr.call "l2r_unreachable" #[t] #[]
    let mut e : RR.Expr := match ls.back? with
      | some l => if nullary l then .block ⟨#[("k", some u64, .atom (toString (ls.size - 1)))],
          .ite (.atom "w >= k") (.ofExpr (mk l)) (.ofExpr unreachable)⟩ else unreachable
      | none => unreachable
    for j in [:ls.size - 1] do
      let i := ls.size - 2 - j
      let some l := ls[i]? | continue
      if !nullary l then continue
      e := .block ⟨#[("k", some u64, .atom (toString i))], .ite (.atom "w == k") (.ofExpr (mk l)) (.ofExpr e)⟩
    modify fun s => { s with fns := s.fns.push (.fn name #[("w", u64)] t (.ofExpr e)) }
  return name

/-- Whether values of Reussir type `t` are heap objects natively, other than
constructors of inductives, when used where Lean expects an object: strings,
arrays, closures, thunks and tasks, references, handles, and the floats
Lean boxes into a cell of their own. -/
def isOtherObject (t : RR.Ty) : LowerM Bool := do
  match t with
  | .named n =>
    if n ∈ ["LStr", "LHandle", "f64", "f32"] then return true
    isRefType t
  | .app n _ => return n == "RVec" || n == "LRef" || n == "LCell"
  | .fn .. => return true
  | _ => return false

/-- The word `lean_unbox` gives natively for value `e` of Reussir type `n`
(`unsafeCast` to a scalar reads it): a `Nat`'s value (`lean_usize_of_nat`;
for a big one, natively an address, its low bits), an `Int`'s 32 bits
(`l2r_int_word`), the index of an enumeration or of a constructor
(`ctorWordFn`: for a constructor with fields, natively an address), a
fixed-width integer's value. Another heap object (a string, an array, a
closure, ...: natively an address) reads as `objectWordBase`, after `e` is
evaluated. `none` for other types. -/
def wordOf (e : RR.Expr) (n : String) : LowerM (Option RR.Expr) := do
  if n == "Nat" then return some (.call "lean_usize_of_nat" #[] #[e])
  if n == "Int" then return some (.call "l2r_int_word" #[] #[e])
  -- `USize` (a boxed scalar natively; `UInt64`, which shares its
  -- representation here, is natively a cell, whose address is read).
  if n == "u64" then return some e
  if let some w ← scalarWord e n then return some w
  if let some info := (← get).typeInfos[n]? then
    if !info.value then return some (.call (← ctorWordFn n info) #[] #[e])
  if ← isOtherObject (.named n) then
    let d ← fresh "ow"
    let z ← fresh "oz"
    return some (.block ⟨#[(d, some (.named n), e), (z, some (.named "u64"), .atom (toString objectWordBase))], .var z⟩)
  return none

/-- The value of Reussir type `n` that natively is the boxed scalar of word
`w : u64` (see `wordOf`): `Nat` `w` (`lean_usize_to_nat`); `Int` the signed
value of its 32 bits
(`lean_scalar_to_int64`); a fixed-width integer, `Bool` (nonzero) or an
enumeration the bits of its width (`lean_unbox` then truncation; an index
past the last constructor gives the last one, as Lean's `switch` does); a
constructor without fields (`ctorOfWordFn`). `none` for other types. -/
def ofWord (w : RR.Expr) (n : String) : LowerM (Option RR.Expr) := do
  let u64 := RR.Ty.named "u64"
  if n == "Nat" then return some (.call "lean_usize_to_nat" #[] #[w])
  if n == "Int" then return some (.call "l2r_int_of_word" #[] #[w])
  if n ∈ ["u8", "u16", "u32"] then return some (.cast w (.named n))
  if n == "bool" then
    let x ← fresh "ix"
    let z ← fresh "iz"
    return some (.block ⟨#[(x, some (.named "u8"), .cast w (.named "u8")), (z, some (.named "u8"), .atom "0")],
      .atom s!"{x} != {z}"⟩)
  if let some info := (← get).typeInfos[n]? then
    if info.shape == .enumLike then
      let size := info.ctorOrder.size
      let mask := if size ≤ 256 then 255 else if size ≤ 65536 then 65535 else 4294967295
      let x ← fresh "ix"
      let m ← fresh "im"
      return some (.block ⟨#[(x, some u64, w), (m, some u64, .atom (toString mask))],
        .call (← enumOfIndexFn n) #[] #[.atom s!"{x} & {m}"]⟩)
    if !info.value && hasNullaryCtor info then return some (.call (← ctorOfWordFn n info) #[] #[w])
  return none

/-- Whether `ofWord` gives values of Reussir type `n`: the types natively
represented by a boxed scalar, and inductives with a constructor without
fields. -/
def isWordTarget (n : String) : LowerM Bool := do
  if n ∈ ["Nat", "Int", "u8", "u16", "u32", "bool"] then return true
  match (← get).typeInfos[n]? with
  | some info => return info.shape == .enumLike || (!info.value && hasNullaryCtor info)
  | none => return false

/-- The types natively represented by a boxed scalar only (never by an
object): `Nat`, `Int` (small values), fixed-width integers, `Bool`,
enumerations. -/
def isPureWord (n : String) : LowerM Bool := do
  if n ∈ ["Nat", "Int", "u8", "u16", "u32", "bool"] then return true
  return ((← get).typeInfos[n]?.map (·.shape == .enumLike)).getD false

/-- Whether a value of Reussir type `sn` read as `dn` converts through its
word (`wordOf`, `ofWord`), as Lean's `lean_unbox` reads it: between boxed
scalars and constructors without fields. With `objects`, also an object (a
constructor with fields, a string, an array, a closure, a `USize`/`UInt64`
or float cell) read as a type that is only ever a boxed scalar: natively its
address, here a deterministic word (`objectWordBase`). That is only done
for a cast the program performs (`castFallback`), never when `tryCoerce`
merely asks whether two representations convert (function values, Box
arms): every function type over a `String` would convert to the same one
over a `Nat`. -/
def wordCastable (sn dn : String) (objects : Bool := false) : LowerM Bool := do
  unless ← isWordTarget dn do return false
  if ← isPureWord sn then return true
  match (← get).typeInfos[sn]? with
  | some info => return !info.value && (hasNullaryCtor info || (objects && (← isPureWord dn)))
  | none => return objects && (sn == "u64" || (← isOtherObject (.named sn))) && (← isPureWord dn)

/-- Which field of constructor `sc` (layout `sl`, of a value's own type) each
field of constructor `dc` (layout `dl`, of the type the value is cast to)
reads, as natively. Lean stores the object fields of a constructor first,
in declaration order, then the `usize` fields, then the other scalars by
decreasing size (ties in declaration order), so fields correspond by their
native slot, not by declaration position: `S₁ {a : UInt8, b : Nat}` read as
`S₂ {x : Nat, y : UInt8}` is `x = b`, `y = a`. For each Lean field of `dc`:
`none` if it has no representation, `some (some k)` if it reads field `k`
of `sc`, `some none` if the field there has no representation here (a
placeholder: the zero). The result is `none` when a field reads data that
the source does not have, or only part of a scalar. Without native layouts,
relevant fields correspond by position. -/
def castFieldMap (sc dc : Name) (sl dl : CtorLayout) : LowerM (Option (Array (Option (Option Nat)))) := do
  let positional : Option (Array (Option (Option Nat))) := Id.run do
    let srcIdx := (List.range sl.fields.size).toArray.filter fun k => (sl.fields[k]?.join).isSome
    let mut out := #[]
    let mut r := 0
    for f in dl.fields do
      match f with
      | some _ =>
        let some k := srcIdx[r]? | return none
        out := out.push (some (some k))
        r := r + 1
      | none => out := out.push none
    return some out
  let (some ss, some ds) := (← nativeSlots sc, ← nativeSlots dc) | return positional
  if ss.size != sl.fields.size || ds.size != dl.fields.size then return positional
  let mut out := #[]
  for h : j in [:dl.fields.size] do
    if dl.fields[j].isNone then
      out := out.push none
      continue
    match ds[j]! with
    -- No data natively (a field relevant only here): a placeholder.
    | none => out := out.push (some none)
    | some slot =>
      match ss.findIdx? (· == some slot) with
      | some k => out := out.push (some (if (sl.fields[k]?.join).isSome then some k else none))
      | none => return none
  return some out

/-- The constructor of generated type `info` that Lean's `cases` selects
for a value whose tag (constructor index, or boxed scalar) is `i`: the
`i`-th, or the last one past the end (Lean's `switch` has the last
alternative as its default). -/
def ctorAtTag (info : TypeInfo) (i : Nat) : Option (Name × CtorLayout) := do
  let n := info.ctorOrder.size
  if n == 0 then none
  let c := info.ctorOrder[min i (n - 1)]!
  let l ← info.ctors.find? c
  return (c, l)

/-- Whether some constructor of generated type `sn` read as `dn` (both
heap objects natively when they have fields) has a native value: by its tag
(`ctorAtTag`), a target constructor without fields, or one with fields that
read the source's (`castFieldMap`). The conversion then goes constructor by
constructor (`structConv`), the others unreachable. -/
def ctorCastable (sn dn : String) : LowerM Bool := do
  unless (← isObjectNominal sn) && (← isObjectNominal dn) do return false
  let some si := (← get).typeInfos[sn]? | return false
  let some di := (← get).typeInfos[dn]? | return false
  for h : i in [:si.ctorOrder.size] do
    let sc := si.ctorOrder[i]
    let some sl := si.ctors.find? sc | continue
    let some (dc, dl) := ctorAtTag di i | continue
    if ← nativeScalarCtor dc dl then return true
    if ← nativeScalarCtor sc sl then continue
    if (← castFieldMap sc dc sl dl).isSome then return true
  return false

/-- See `retypable`; `assumed`: pairs of types under comparison. -/
partial def retypableAux (a b : RR.Ty) (assumed : Array (String × String)) :
    LowerM (Option (Array (String × String))) := do
  if a == b then return some assumed
  match a, b with
  | .named an, .named bn =>
    if assumed.contains (an, bn) then return some assumed
    let infos ← getPart (·.typeInfos)
    let (some ai, some bi) := (infos[an]?, infos[bn]?) | return none
    if ai.value != bi.value || ai.shape != bi.shape || ai.ctorOrder.size != bi.ctorOrder.size then return none
    let mut asm := assumed.push (an, bn)
    for (ca, cb) in ai.ctorOrder.zip bi.ctorOrder do
      let (some la, some lb) := (ai.ctors.find? ca, bi.ctors.find? cb) | return none
      let pa := la.posTys
      let pb := lb.posTys
      if pa.size != pb.size then return none
      -- The fields a conversion pairs are at the same record positions.
      let some fm ← castFieldMap ca cb la lb | return none
      for h : j in [:lb.fields.size] do
        let some (p, _) := lb.fields[j] | continue
        let some (some k) := fm[j]?.join | return none
        if (la.fields[k]?.join.map (·.1)) != some p then return none
      for (x, y) in pa.zip pb do
        let some asm' ← retypableAux x y asm | return none
        asm := asm'
    return some asm
  | _, _ => return none

/-- Whether a value of Reussir type `a` can be used as a value of type `b`
as it is, the same object reinterpreted (`l2r_retype`): both are shared
records with the same layouts: the same constructors whose fields,
position by position, have the same layouts (coinductively, for recursive
types); the conversion between them (`structConv`) would pair exactly
those fields. Isomorphic inductives read through `unsafeCast` (a user list
as `List`: with one type per inductive, both hold `Box` elements) are
then not converted at all: no time, no copy, and the value keeps its
sharing. -/
def retypable (a b : RR.Ty) : LowerM Bool := do
  if a == b then return false
  if !(← isBoundaryTy a) || !(← isBoundaryTy b) then return false
  match a with
  | .named n => if n == boxName || !(← get).typeInfos.contains n then return false
  | _ => return false
  return (← retypableAux a b #[]).isSome

/-- How `structConv` converts one constructor of the source type: the
target constructor's layout (`none`: no native value reads it, so the arm is
unreachable) and, for each relevant field of the target in Lean order, the
source field it reads (record position and type) or `none` (a placeholder,
the zero of its type). -/
structure ConvArm where
  sl : CtorLayout
  dl : Option CtorLayout
  fields : Array (Option (Nat × RR.Ty) × RR.Ty)

instance : Inhabited ConvArm := ⟨{ sl := { variant := "", numParams := 0, fields := #[] }, dl := none, fields := #[] }⟩

/-- The constructors of the conversion from generated type `sn` to `dn`,
two inductives that meet through `unsafeCast` (one inductive has one type,
so there is nothing to convert between its instantiations), in `sn`'s
constructor order, as Lean's `cases` reads the value: by tag
(`ctorAtTag`), a target constructor without fields whatever the source
holds, an object's fields by native slot (`castFieldMap`), and no value for
a boxed scalar read as an object with fields. -/
def convArms (sn dn : String) : LowerM (Array ConvArm) := do
  let some si := (← get).typeInfos[sn]? | throwError "lean2rr: no type {sn}"
  let some di := (← get).typeInfos[dn]? | throwError "lean2rr: no type {dn}"
  let mut out := #[]
  for h : ci in [:si.ctorOrder.size] do
    let ctor := si.ctorOrder[ci]
    let some sl := si.ctors.find? ctor | continue
    match ctorAtTag di ci with
    | none => out := out.push { sl, dl := none, fields := #[] }
    | some (dctor, dl) =>
      let targets := (List.range dl.fields.size).toArray.filterMap fun j => (dl.fields[j]?.join).map fun f => (j, f.2)
      if ← nativeScalarCtor dctor dl then
        out := out.push { sl, dl := some dl, fields := targets.map fun (_, dt) => (none, dt) }
      else if ← nativeScalarCtor ctor sl then
        out := out.push { sl, dl := none, fields := #[] }
      else
        match ← castFieldMap ctor dctor sl dl with
        | none => out := out.push { sl, dl := none, fields := #[] }
        | some fm =>
          out := out.push { sl, dl := some dl, fields := targets.map fun (j, dt) =>
            match fm[j]?.join with
            | some (some k) => (sl.fields[k]?.join, dt)
            | _ => (none, dt) }
  return out

/-- The function `countConversion` calls: a counter of the elements (array
elements, constructor cells) that conversions rebuild, printed to stderr at
exit (`leanrt: conversions N`). -/
def convTickFn : String :=
  "#[ffi(import)]\nfn l2r_conv_tick(n : u64) -> unit [{ { use std::sync::atomic::{AtomicU64, Ordering::Relaxed}; " ++
  "static N: AtomicU64 = AtomicU64::new(0); static R: std::sync::Once = std::sync::Once::new(); " ++
  "extern \"C\" { fn atexit(f: extern \"C\" fn()) -> i32; } " ++
  "extern \"C\" fn report() { eprintln!(\"leanrt: conversions {}\", N.load(Relaxed)); } " ++
  "R.call_once(|| unsafe { atexit(report); }); N.fetch_add(n, Relaxed); } }];\n"

/-- In a test build (`L2R_COUNT_CONVERSIONS` set, tests/runtime/conv-count-check.sh):
the body `b` of a generated conversion function (or of one step of one),
with a call counting the `amount` elements it converts (an expression over
`b`'s bindings) before its result. Otherwise `b`. -/
def countConversion (b : RR.Block) (amount : RR.Expr := .atom "1") : LowerM RR.Block := do
  unless (← IO.getEnv "L2R_COUNT_CONVERSIONS").isSome do return b
  unless ← getPart (·.convTickEmitted) do
    modify fun s => { s with fns := s.fns.push (.raw convTickFn), convTickEmitted := true }
  let one := if amount matches .atom "1" then #[("one", some (RR.Ty.named "u64"), amount)] else #[]
  let arg := if amount matches .atom "1" then RR.Expr.var "one" else amount
  return ⟨b.lets ++ one ++ #[("tick", none, .call "l2r_conv_tick" #[] #[arg])], b.result⟩

mutual
  /-- Convert `e` from representation `src` to `dst`: boxing and unboxing
  (`Box`), function-value wrappers, and the casts Lean's `unsafeCast` makes
  between types it represents alike (words, bits, isomorphic inductives).
  An inductive has one type whatever its arguments (`nominalType`), so a
  value is never rebuilt to change its layout: Lean's mono `cse` merging
  `[] : List Shape` with `[] : List Nat` gives one value of one type. -/
  partial def coerce (e : RR.Expr) (src dst : RR.Ty) : LowerM RR.Expr := do
    -- A cast the program performs between inductives that do not
    -- correspond constructor for constructor: by constructor (see
    -- `castFallback`), not by `tryCoerce`'s words.
    if let (.named sn, .named dn) := (src, dst) then
      if (← nominalHead sn) != (← nominalHead dn) && !(← isomorphic sn dn) && (← ctorCastable sn dn) then
        return ← convCall sn dn e
    match ← tryCoerce e src dst with
    | some r => return r
    | none =>
      if let some r ← castFallback e src dst then return r
      let keyOf (t : RR.Ty) : LowerM String := do
        match t with
        | .named n => return match (← get).typeHeads[n]? with | some k => s!"{n} = {k}" | none => n
        | _ => return t.render
      -- No conversion: only reachable through an `unsafeCast` between
      -- types whose values Lean represents alike but lean2rr does not.
      -- The program is still translated; the cast panics if executed.
      IO.eprintln s!"lean2rr: warning: no representation conversion from {← keyOf src} to {← keyOf dst}; the conversion panics at run time"
      return .call "l2r_internal_panic_at" #[dst] #[.atom "0"]

  partial def tryCoerce (e : RR.Expr) (src dst : RR.Ty) : LowerM (Option RR.Expr) := do
    if src == dst then return some e
    -- A function value is boxed as it is; unboxing it to another
    -- representation wraps it (`l2r_unbox_fn_…`), so a function value that
    -- goes through uniform code and back is not wrapped at all.
    -- A unit boxed is `box(0)`, the word 1 (no allocation per `IO Unit`
    -- result).
    if dst == RR.Ty.box then
      -- A box unboxed and boxed again at once is the box itself
      -- (`boxUnboxed?`).
      if let some b ← boxUnboxed? e src then return some b
      return some (← boxOf e src)
    if src == RR.Ty.box then
      match dst with
      | .fn .. => return some (.call (← unboxFnFn dst) #[] #[e])
      | _ =>
        if let .named tn := dst then
          if (← get).typeInfos.contains tn then
            -- `tn`'s own variant and `box(0)` in line; in a program that
            -- casts (`programCasts`), the other variants through the
            -- generated function, which reads values of types Lean
            -- represents alike (`boxCastable`).
            if !(← read).programCasts then return some (← unboxMatch e dst)
            return some (← unboxMatch e dst (slow := some (← unboxFn tn)))
          if tn ∈ ["Nat", "Int", "u8", "u16", "u32", "bool", "u64", "f64", "f32"] then
            -- The word in line (an immediate is read at `dst`, whatever
            -- word type boxed it, as natively); in a program that casts,
            -- another payload (an object read as a word) through the
            -- generated function.
            if !(← read).programCasts then return some (← unboxMatch e dst)
            return some (← unboxMatch e dst (slow := some (← unboxFn tn)))
        -- An array, a thunk or task, a reference, a string, ...: one
        -- representation each, one variant.
        return some (← unboxMatch e dst)
    match src, dst with
    -- A unit-like value used at another type is an `unsafeCast ()`
    -- placeholder (see `zeroValue`).
    | .named "L2RUnit", _ => return some (← zeroValue dst)
    -- Any value at a unit-like type (an irrelevant position: a proof, a
    -- phantom) carries nothing; it is still evaluated.
    | _, .named "L2RUnit" =>
      let d ← fresh "du"
      return some (.block ⟨#[(d, some src, e)], .unitVal⟩)
    | .fn a1 b1, .fn a2 b2 =>
      -- Another representation of the same function type: wrapped, and
      -- converted at each application. A phantom domain (rule 4) on
      -- either side needs no conversion: its argument is dropped, or the
      -- other side's placeholder given (`genApply`).
      unless a1 == RR.Ty.phantom || a2 == RR.Ty.phantom do
        let some _ ← tryCoerce (.var "l2rcv") a2 a1 | return none
      let some _ ← tryCoerce (.var "l2rcv") b1 b2 | return none
      addFnVariant dst (.wrap src dst)
      return some (.call (← fnConvFn src dst) #[] #[e])
    -- Between a function value and a Reussir closure (prelude callbacks):
    -- a lambda, at the function's run-time type. `e` is bound first, so
    -- that it is evaluated once.
    -- Both cases take the function side's domain and codomain from `.rt`,
    -- where a function type has lost its phantom domains. That is safe only
    -- because prelude closure types never have phantom domains either: they
    -- are built from run-time types (`lowerExternCall`'s `.cls d c` of
    -- `t.rt`, the `raw` variant's, `ctorCallbackExtern`'s `.cls .unit rt`
    -- over an IO result type), so both sides are at run-time types and
    -- a conversion between them does not drop or add a `◾` argument. A
    -- closure type that keeps phantom domains would need the function
    -- side's own domains, as `genApply`'s `.part` arm takes them (test
    -- `RtApplyPhantomParam`).
    | .fn .., .cls a2 b2 =>
      let .fn a1 b1 := src.rt | return none
      let (pre, callee) ← match e with
        | .var _ => pure (#[], e)
        | _ => do
          let v ← fresh "cf"
          pure (#[(v, some src, e)], RR.Expr.var v)
      let x ← fresh "cv"
      let some arg ← tryCoerce (.var x) a2 a1 | return none
      let some res ← tryCoerce (← applyCall callee src #[arg]) b1 b2 | return none
      let lam := RR.Expr.lam x a2 (.ofExpr res)
      return some (if pre.isEmpty then lam else .block ⟨pre, lam⟩)
    | .cls a1 b1, .fn .. =>
      let .fn a2 b2 := dst.rt | return none
      let (pre, callee) ← match e with
        | .var _ => pure (#[], e)
        | _ => do
          let v ← fresh "cf"
          pure (#[(v, some src, e)], RR.Expr.var v)
      let x ← fresh "cv"
      let some arg ← tryCoerce (.var x) a2 a1 | return none
      let some res ← tryCoerce (.apply callee arg) b1 b2 | return none
      let f := rawFnValue dst x (.ofExpr res)
      return some (if pre.isEmpty then f else .block ⟨pre, f⟩)
    | .named sn, .named dn =>
      -- (Through `unsafeCast`) another inductive that Lean represents
      -- alike: the same object if the layouts agree, otherwise constructor
      -- by constructor.
      if let (some _, some _) := (← nominalHead sn, ← nominalHead dn) then
        if ← isomorphic sn dn then
          if ← retypable src dst then return some (.call "l2r_retype" #[src, dst] #[e])
          return some (← convCall sn dn e)
      -- The rest is only reachable through `unsafeCast`, between values that
      -- Lean represents by the same word; the conversions follow Lean's
      -- `lean_box`/`lean_unbox`. `Float` and `UInt64` are both a cell with
      -- an 8-byte scalar area: the bits, copied unchanged (NaN payloads
      -- included; `Float.ofBits`/`toBits` would make every NaN the canonical
      -- one). `Float32` and `UInt32` are not alike natively (a cell and a
      -- tagged scalar: such a cast crashes there); here their bits are
      -- copied the same way (plan §10).
      match sn, dn with
      | "u64", "f64" => return some (.call "l2r_f64_of_raw_bits" #[] #[e])
      | "f64", "u64" => return some (.call "l2r_f64_raw_bits" #[] #[e])
      | "u32", "f32" => return some (.call "l2r_f32_of_raw_bits" #[] #[e])
      | "f32", "u32" => return some (.call "l2r_f32_raw_bits" #[] #[e])
      -- `Nat` and `Int`: the same value (natively the same boxed scalar for
      -- small values, the same big number object otherwise; a `Nat` from
      -- 2^31 to 2^63 is not a valid small `Int` natively).
      | "Nat", "Int" => return some (.call "lean_nat_to_int" #[] #[e])
      | "Int", "Nat" => return some (.call "l2r_int_cast_nat" #[] #[e])
      | _, _ => pure ()
      -- A `[value]` struct is natively its field (Lean erases its
      -- inductive), and a boxed one is its field's box. One that Lean keeps
      -- as an object (`valueStructIsObject`) is read by constructor where
      -- the program casts it to another inductive (`coerce`).
      let infos ← getPart (·.typeInfos)
      if let some si := infos[sn]? then
        if si.value && (← nominalHead sn) != (← nominalHead dn) then
          if let some ft := (si.ctors.find? si.ctorOrder[0]!).bind (·.posTys[0]?) then
            let (pre, v) ← match e with
              | .var _ => pure (#[], e)
              | _ => do
                let x ← fresh "vs"
                pure (#[(x, some src, e)], RR.Expr.var x)
            let some r ← tryCoerce (.field v 0) ft dst | return none
            return some (if pre.isEmpty then r else .block ⟨pre, r⟩)
      if let some di := infos[dn]? then
        if di.value && (← nominalHead sn) != (← nominalHead dn) then
          if let some ft := (di.ctors.find? di.ctorOrder[0]!).bind (·.posTys[0]?) then
            let some v ← tryCoerce e src ft | return none
            return some (.ctor dn none #[v])
      -- Boxed scalars: `Nat`, `Int`, fixed-width integers, `Bool`,
      -- enumerations, constructors without fields; and objects read as
      -- words (natively their address: `wordOf`'s deterministic value).
      if ← wordCastable sn dn then
        if let some w ← wordOf e sn then
          if let some r ← ofWord w dn then return some r
      return none
    | _, _ => return none

  /-- A cast the program performs that `tryCoerce` has no conversion for: an
  object read
  as a word (`wordCastable` with `objects`: natively an address, here a
  deterministic word), or a word read as a `USize` (here `u64`, which
  `UInt64` shares: natively `lean_unbox` for `USize`). `none` otherwise. -/
  partial def castFallback (e : RR.Expr) (src dst : RR.Ty) : LowerM (Option RR.Expr) := do
    let .named dn := dst | return none
    let sn ← match src with
      | .named sn => pure sn
      | _ =>
        unless (← isOtherObject src) && ((← isPureWord dn) || dn == "u64") do return none
        let d ← fresh "ow"
        let z ← fresh "oz"
        let w := RR.Expr.block ⟨#[(d, some src, e), (z, some (.named "u64"), .atom (toString objectWordBase))], .var z⟩
        if dn == "u64" then return some w
        return ← ofWord w dn
    if dn == "u64" then
      unless (← isPureWord sn) || (← wordCastable sn "Nat" (objects := true)) do return none
      return ← wordOf e sn
    unless ← wordCastable sn dn (objects := true) do return none
    let some w ← wordOf e sn | return none
    ofWord w dn

  /-- Whether values of generated type `sn` can be read as values of `dn`
  (through `unsafeCast`, where Lean's representations coincide): the same
  number of constructors, and each field of a constructor of `dn` reads a
  field of the corresponding constructor of `sn` (`castFieldMap`). -/
  partial def isomorphic (sn dn : String) : LowerM Bool := do
    let some si := (← get).typeInfos[sn]? | return false
    let some di := (← get).typeInfos[dn]? | return false
    if si.ctorOrder.size != di.ctorOrder.size then return false
    for (a, b) in si.ctorOrder.zip di.ctorOrder do
      let (some la, some lb) := (si.ctors.find? a, di.ctors.find? b) | return false
      if (← castFieldMap a b la lb).isNone then return false
    return true

  /-- The value of constructor arm `arm` of `sn` converted to `dn`, with the
  source value in `x`: each field converted (`tryCoerce`; a recursive field
  through `structConv` again) or a placeholder. Unreachable when the arm has
  no native value or a field has no conversion. -/
  partial def convBuild (sn dn : String) (arm : ConvArm) (x : RR.Expr) : LowerM RR.Expr := do
    let some si := (← get).typeInfos[sn]? | throwError "lean2rr: no type {sn}"
    let some di := (← get).typeInfos[dn]? | throwError "lean2rr: no type {dn}"
    let unreachable := RR.Expr.call "l2r_unreachable" #[.named dn] #[]
    let some dl := arm.dl | return unreachable
    let srcFields := arm.sl.fields.filterMap id
    let names ← srcFields.mapM fun _ => fresh "cf"
    let nameAt (p : Nat) : Option String := ((names.zip srcFields).find? (·.2.1 == p)).map (·.1)
    let mut vals := #[]
    let mut possible := true
    for h : j in [:arm.fields.size] do
      let (src?, dt) := arm.fields[j]
      match src? with
      | some (p, st) =>
        match nameAt p with
        | some n =>
          match ← tryCoerce (.var n) st dt with
          | some v => vals := vals.push v
          | none => possible := false
        | none => possible := false
      | none => vals := vals.push (← zeroValue dt)
    let value : RR.Expr := if !possible then unreachable else match di.shape with
      | .struct => .ctor dn none (dl.place vals)
      | _ => .ctor dn (some dl.variant) (dl.place vals)
    match si.shape with
    | .struct =>
      return .block ⟨(names.zip srcFields).map (fun (n, (p, t)) => (n, some t, RR.Expr.field x p)), value⟩
    | _ =>
      let mut binders : Array (Option String) := Array.replicate srcFields.size none
      for (n, (p, _)) in names.zip srcFields do binders := binders.set! p (some n)
      return .mtch x #[{ ty := sn, ctor := some arm.sl.variant, binders, body := .ofExpr value },
        { ty := sn, ctor := none, binders := #[], body := .ofExpr unreachable }]

  /-- The generated function converting generated type `sn` to `dn`, two
  inductives that Lean represents alike, read through `unsafeCast`
  (`convArms`), when their layouts differ (otherwise the value is reused:
  `retypable`). Cached. A recursive field is converted by a call of the
  function itself (`convsInProgress` holds the functions being generated, so
  a recursive use gets the name; once the function is emitted it leaves the
  set, and `hasFn` finds it). Such a conversion exists only for a cast the
  program performs: a value of one inductive never changes layout. -/
  partial def structConv (sn dn : String) : LowerM String := do
    let fname := s!"l2r_conv_{sn}_{dn}"
    if (← hasFn fname) || (← get).deadConvs.contains fname then return fname
    if (← get).convsInProgress.contains fname then
      modify fun s => { s with convsCalledEarly := s.convsCalledEarly.insert fname }
      return fname
    modify fun s => { s with convsInProgress := s.convsInProgress.insert fname }
    structConvBody sn dn fname
    modify fun s => { s with convsInProgress := s.convsInProgress.erase fname }
    return fname

  /-- `e : sn` converted to `dn` by `structConv`'s function; a conversion
  that can never return a value (`LowerState.deadConvs`) is
  `l2r_unreachable` in line (`e` still evaluated first), with no function
  (a generated unboxing leaves its arm out: `deadConvExpr?`). -/
  partial def convCall (sn dn : String) (e : RR.Expr) : LowerM RR.Expr := do
    let f ← structConv sn dn
    if (← get).deadConvs.contains f then
      let d ← fresh "dc"
      return .block ⟨#[(d, some (.named sn), e)], .call "l2r_unreachable" #[.named dn] #[]⟩
    return .call f #[] #[e]

  /-- The body of `structConv`'s function `fname`. -/
  partial def structConvBody (sn dn fname : String) : LowerM Unit := do
    let some si := (← get).typeInfos[sn]? | throwError "lean2rr: no type {sn}"
    let mut arms := #[]
    let mut structBody : Option RR.Block := none
    for arm in ← convArms sn dn do
      let e ← convBuild sn dn arm (.var "x")
      match si.shape, e with
      | .struct, _ => structBody := some (match e with | .block b => b | e => .ofExpr e)
      | _, .mtch _ as =>
        if let some a := as[0]? then arms := arms.push a
      | _, e =>
        let nrel := (arm.sl.fields.filterMap id).size
        arms := arms.push { ty := sn, ctor := some arm.sl.variant, binders := Array.replicate nrel none, body := .ofExpr e }
    let body := match structBody with
      | some b => b
      | none => .ofExpr (.mtch (.var "x") arms)
    -- No constructor converts (each value is `l2r_unreachable`): no
    -- function, unless one being generated calls it already; then its body
    -- is the panic alone.
    let unreachable (b : RR.Block) : Bool := b.result matches .call "l2r_unreachable" _ #[]
    let dead := match structBody with
      | some b => unreachable b
      | none => arms.all (unreachable ·.body)
    if dead then
      modify fun s => { s with deadConvs := s.deadConvs.insert fname }
      if (← get).convsCalledEarly.contains fname then
        modify fun s => { s with fns := s.fns.push (.fn fname #[("x", .named sn)] (.named dn)
          (.ofExpr (.call "l2r_unreachable" #[.named dn] #[]))) }
      return
    let body ← countConversion body
    modify fun s => { s with fns := s.fns.push (.fn fname #[("x", .named sn)] (.named dn) body) }
end

/-- Whether `e` is `convCall`'s use of a conversion that can never return
a value (`l2r_unreachable` after evaluating the converted value). -/
def deadConvExpr? (e : RR.Expr) : Bool :=
  e matches .block ⟨#[(_, _, _)], .call "l2r_unreachable" _ #[]⟩

/-- The field type of `[value]` struct `info` (natively the struct is its
field). -/
def valueFieldTy? (info : TypeInfo) : Option RR.Ty := do
  guard info.value
  let c ← info.ctorOrder[0]?
  let l ← info.ctors.find? c
  l.posTys[0]?

/-- The declarations whose source a declaration of the program (an
instance, or code Lean derived from one: `f._redArg`, `f._lam_0`,
`g._at_.f.spec_0`) comes from: its prefixes that are declarations, also
those of the declaration a specialization was made in. A hygienic name
(made by a macro) keeps its macro scopes at the end (`f._lam_0._@.M._hyg.3`
comes from `f._@.M._hyg.3`): the prefixes are those of the name without
them, each also tried with them. The prefixes are built component by
component (`Name.append` panics on a prefix that ends in `_hyg`). -/
def sourceDecls (env : Environment) (n : Name) : Array Name := Id.run do
  let view := extractMacroScopes n
  let comps := view.name.components
  let extend (pre c : Name) : Name := match c with
    | .str _ s => .str pre s
    | .num _ k => .num pre k
    | .anonymous => pre
  let mut out := #[]
  let add (out : Array Name) (p : Name) : Array Name := Id.run do
    let mut out := out
    for q in [p, { view with name := p }.review] do
      if env.contains q && !out.contains q then out := out.push q
    return out
  let mut pre := Name.anonymous
  for c in comps do
    pre := extend pre c
    out := add out pre
  if let some i := comps.idxOf? `_at_ then
    let mut site := Name.anonymous
    for c in comps.drop (i + 1) do
      site := extend site c
      out := add out site
  return out

/-- The C symbols of Lean's library and lean2rr's shim (`isToolchainModule`):
those of their externs and of their `@[export]` definitions. lean2rr calls
a program's `@[export]` definition under such a symbol where the library's
function would run, without comparing types: an extern of the library whose
C symbol it is (`Mono.redirectTarget`), an `IO.Error` builder the runtime
calls (`ioErrorBuilderSyms`, `@[export]`s of `Init`). -/
def librarySymbols (env : Environment) : Std.HashSet String := Id.run do
  let mut s : Std.HashSet String := {}
  for i in [:env.header.moduleNames.size] do
    unless isToolchainModule env.header.moduleNames[i]! do continue
    for (n, _) in externAttr.ext.getModuleEntries env i do
      if let some sym := getExternNameFor env `c n then s := s.insert sym
    for (_, sym) in exportAttr.ext.getModuleEntries env i do
      s := s.insert (sym.toString (escape := false))
  return s

/-- Every declaration exported under each C symbol (`@[export sym]`), of any
module. -/
def exportsBySymbol (env : Environment) : Std.HashMap String (Array Name) := Id.run do
  let mut m : Std.HashMap String (Array Name) := {}
  for i in [:env.header.moduleNames.size] do
    for (d, sym) in exportAttr.ext.getModuleEntries env i do
      let k := sym.toString (escape := false)
      m := m.insert k ((m.getD k #[]).push d)
  return m

/-- The constants of Lean's library whose use rests on compiled code: the
kernel proves `Lean.reduceBool c = b` (`reduceNat`) by running the compiled
code of the constant `c`, which can be the program's, and
`Lean.ofReduceBool` (`ofReduceNat`) turns that into `c = b` (Lean 4.34,
`Init/Core.lean`). With a wrong `implemented_by` in that code, either
proves `False` (tests `RtCastReduceBool`, `RtCastReduceBoolCongr`). -/
def isKernelEvalConst (n : Name) : Bool :=
  n == `Lean.reduceBool || n == `Lean.reduceNat || n == `Lean.ofReduceBool ||
    n == `Lean.ofReduceNat

/-- The constants of the program's modules (not of Lean's library or
lean2rr's shim) whose statement has the shape of a constant replacement,
`@f = @g` (the shape `@[csimp]` accepts, `CSimp.isConstantReplacement?`),
each as `f ↦ g` by itself. Every `@[csimp]` theorem of the program is one:
global, `scoped`, or `local` (a `local` attribute is saved nowhere, and a
module can make a theorem of another module a `local` `@[csimp]`; tests
`RtCastCsimpLocal`, `RtCastCsimpScoped`, `RtCastNativeCrossLocal`). So is
any theorem of that shape without the attribute (the set is larger than
needed, never smaller). `programCasts` takes the targets that are
declarations of the program as roots of its walk; `nativeExempt` looks for
the replaced constants. -/
def programCsimps (env : Environment) : Array CSimp.Entry := Id.run do
  let mut out : Array CSimp.Entry := #[]
  for i in [:env.header.moduleNames.size] do
    if isToolchainModule env.header.moduleNames[i]! then continue
    let some data := env.header.moduleData[i]? | continue
    for ci in data.constants do
      if let some (_, .const f _, .const g _) := ci.type.eq? then
        out := out.push { fromDeclName := f, toDeclName := g, thmName := ci.name }
  return out

/-- The statement `e` of axiom `ci` when it is one that Lean adds for a
proof by native evaluation: `Lean.Meta.nativeEqTrue` (Lean 4.34,
`Lean/Meta/Native.lean`; `native_decide`, `decide +native` and `bv_decide`
call it) compiles `e`, a closed `Bool` term, runs it, and only when it
gives `true` adds the axiom `e = true` (exactly `@Eq.{1} Bool e true`, not
`unsafe`), named `<decl>._native.<tactic>.ax_<i>…` (`mkAuxDeclName`:
`ax_1`, `ax_1_10`; under the module system with `_private.…` in front).
`none` for every other axiom: one the user writes, whatever it states
(`axiom bad : true = false` too, test `RtCastAxiomBoolEq`), and one with
that name and another statement. The name is how Lean names these axioms,
nothing more: an axiom that the user names so, with that statement shape,
passes (`axiom foo._native.native_decide.ax_1 : (!true) = true`). -/
def nativeEvalStatement? (ci : ConstantInfo) : Option Expr := do
  let .axiomInfo ai := ci | none
  guard !ai.isUnsafe
  let .str (.str (.str _ "_native") _) last := ci.name.eraseMacroScopes | none
  let idx := last.splitOn "_"
  guard (idx.head? == some "ax" && idx.length ≥ 2 &&
    idx.tail.all fun s => !s.isEmpty && s.all Char.isDigit)
  let t := ci.type
  guard (t.isAppOfArity ``Eq 3 && t.appFn!.appFn!.appArg!.isConstOf ``Bool &&
    t.appArg!.isConstOf ``Bool.true)
  return t.appFn!.appArg!

/-- The walk of `nativeExempt` over the code that Lean's evaluation of `e`,
the statement of an axiom of native evaluation, may have run: from the
constants of `e` and from `libTargets` (the replacements of library
constants, which compiled code may call where only a library
`@[macro_inline]` body shows them), through the definitions and
`_unsafe_rec` copies of the program's declarations (not into Lean's
library, whose code is trusted as Lean's compiler is), and from each
constant reached to the replacements that the `@[csimp]` candidates give
it (`targets`, `programCsimps`): compiled code runs `g` for `f`. `.error n`:
`n` may compute another value than its definition says, a program
declaration with an `implemented_by` target (checked against the declared
type only: a wrong implementation of a `Bool` makes `native_decide` prove
`False`, as Lean's `implemented_by` doc says; test `RtCastNativeImplBy`),
an extern (natively its C), or a constant that an `initialize` or
`builtin_initialize` action sets (`getInitFnNameFor?`): the action runs
when a module imports the constant's, so its value can differ between the
builds of two modules (an environment variable), and two axioms about it,
each true in its own build, prove `False` (test `RtCastNativeInit`); or a
constant of kernel evaluation (`isKernelEvalConst`). `.ok s`: the constants reached, the program's
declarations and the library constants that they and `e` mention. -/
def nativeEvalWalk (env : Environment) (library : Name → Bool) (targets : NameMap (Array Name))
    (libTargets : Array Name) (e : Expr) : Except Name NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut work : Array Name := e.foldConsts libTargets fun k acc => acc.push k
  while h : work.size > 0 do
    let n := work[work.size - 1]
    work := work.pop
    if seen.contains n then continue
    seen := seen.insert n
    if isKernelEvalConst n then return .error n
    work := work ++ targets.getD n #[]
    if library n then continue
    if (Compiler.getImplementedBy? env n).isSome || isExtern env n ||
        (getInitFnNameFor? env n).isSome then
      return .error n
    let unsafeRec := Compiler.mkUnsafeRecName n
    if env.contains unsafeRec then work := work.push unsafeRec
    if let some v := (env.find? n).bind (·.value? (allowOpaque := true)) then
      work := v.foldConsts work fun k acc => if seen.contains k then acc else acc.push k
  return .ok seen

/-- The axioms that the proof of `thm` rests on, as `#print axioms` collects
them (the constants of values and types, transitively), but through the
declarations of the program only: Lean's library is trusted. `none` when
one of them can be false whatever the program's code is: `sorryAx`, an
axiom of the program that is not one of native evaluation, or a constant of
kernel evaluation (`isKernelEvalConst`). Otherwise the axioms of native
evaluation among them (`nativeEvalStatement?`), which `nativeExempt`
judges. Lean's standard axioms (`propext`, `Quot.sound`,
`Classical.choice`) are the library's: a theorem that uses only them is
true. -/
def proofAxioms (env : Environment) (library : Name → Bool) (thm : Name) : Option NameSet := Id.run do
  let mut natives : NameSet := {}
  let mut seen : NameSet := {}
  let mut work := #[thm]
  while h : work.size > 0 do
    let n := work[work.size - 1]
    work := work.pop
    if seen.contains n then continue
    seen := seen.insert n
    if n == ``sorryAx || isKernelEvalConst n then return none
    if library n then continue
    let some ci := env.find? n | continue
    if ci matches .axiomInfo _ then
      unless (nativeEvalStatement? ci).isSome do return none
      natives := natives.insert n
      continue
    work := ci.type.foldConsts work fun k acc => if seen.contains k then acc else acc.push k
    if let some v := ci.value? (allowOpaque := true) then
      work := v.foldConsts work fun k acc => if seen.contains k then acc else acc.push k
  return some natives

/-- The declaration whose elaboration added the axiom of native evaluation
`ax` (`T` for `T._native.<tactic>.ax_<i>…`). -/
def nativeAxiomDecl? (ax : Name) : Option Name :=
  match ax.eraseMacroScopes with
  | .str (.str (.str d "_native") _) _ => some d
  | _ => none

/-- The axioms of native evaluation of the program (`nativeEvalStatement?`)
that do not make it cast: those whose evaluation ran the code of the
definitions, so that the axiom is true. An axiom `A : e = true` is exempt
when
- the walk over what its evaluation ran (`nativeEvalWalk`) meets no
  program declaration with an `implemented_by` target, no extern, no
  constant that an `initialize` action sets and no constant of kernel
  evaluation; and
- no dangerous `@[csimp]` candidate (`programCsimps`) acts on it. A
  candidate `T : @f = @g` acts on `A` when the walk reached `f`, or `f` is
  a library constant, unless `T` comes after `A`: `A` is `T`'s own axiom
  (`nativeAxiomDecl?`: Lean adds it while it elaborates `T`), or `T`'s
  proof uses `A`. A candidate is dangerous when its proof can be false
  (`proofAxioms`): it uses `sorryAx`, an axiom of the program that is not
  exempt, or kernel evaluation. A true theorem `@f = @g` makes `f` and `g`
  compute alike (and the walk goes into `g` anyway).
A candidate proved with an axiom of native evaluation is dangerous until
that axiom is exempt, and that axiom's exemption may depend on candidates:
this is the least fixed point. It starts with no axiom exempt and every
candidate whose proof uses an axiom dangerous, and grows the exempt set
until it is stable, so that axioms and candidates that only justify each
other stay out. The usual idiom `theorem T : tableOk = true := by
native_decide` has the shape `@f = @g`, but is `A`'s own theorem (test
`RtCastNativeEqIdiom`); a candidate proved by `sorry` acts on every later
axiom whose evaluation reaches its `f`, in any module (tests
`RtCastNativeCsimp`, `RtCastNativePrefix`, `RtCastNativeCrossLocal`). -/
def nativeExempt (env : Environment) (library : Name → Bool) (csimps : Array CSimp.Entry) :
    NameSet := Id.run do
  let mut axioms : Array (Name × Expr) := #[]
  for i in [:env.header.moduleNames.size] do
    if isToolchainModule env.header.moduleNames[i]! then continue
    let some data := env.header.moduleData[i]? | continue
    for ci in data.constants do
      if let some e := nativeEvalStatement? ci then axioms := axioms.push (ci.name, e)
  if axioms.isEmpty then return {}
  let targets : NameMap (Array Name) := csimps.foldl (init := {}) fun m c =>
    m.insert c.fromDeclName ((m.getD c.fromDeclName #[]).push c.toDeclName)
  let libTargets := csimps.filterMap fun c =>
    if library c.fromDeclName && !library c.toDeclName then some c.toDeclName else none
  -- What each evaluation ran (`none`: maybe other code than the definitions').
  let reached : Array (Name × Option NameSet) := axioms.map fun (a, e) =>
    (a, match nativeEvalWalk env library targets libTargets e with
      | .ok s => some s
      | .error _ => none)
  -- The candidates that could act on some axiom, with their proofs' axioms.
  let acting := csimps.filter fun c =>
    library c.fromDeclName || reached.any fun (_, s?) => s?.any (·.contains c.fromDeclName)
  let proofs : Array (CSimp.Entry × Option NameSet) :=
    acting.map fun c => (c, proofAxioms env library c.thmName)
  let mut exempt : NameSet := {}
  repeat
    let dangerous := proofs.filter fun (_, ax?) => match ax? with
      | none => true
      | some ax => ax.toList.any fun a => !exempt.contains a
    let next : NameSet := reached.foldl (init := {}) fun acc (a, s?) => match s? with
      | none => acc
      | some s =>
        let acts := dangerous.any fun (c, ax?) =>
          (library c.fromDeclName || s.contains c.fromDeclName) &&
            !(nativeAxiomDecl? a == some c.thmName || ax?.any (·.contains a))
        if acts then acc else acc.insert a
    -- The set only grows (each round, more axioms exempt and fewer
    -- candidates dangerous).
    if next.size == exempt.size then return next
    exempt := next
  return exempt

/-- Whether the program can read a value as another type than its own
(`LowerCtx.programCasts`), and the declaration that shows it: some
declaration it reaches, outside Lean's own library (`Init`, `Std`, `Lean`,
`Lake`) and lean2rr's shim (`L2RShim`), is `unsafe` (its code may
`unsafeCast`, build a `TypeName` for `Dynamic`, or be the `implemented_by`
target of another type's code; the `_unsafe_rec` code Lean (4.33, 4.34) generates
for a `partial def` is not `unsafe`), is an axiom (but see below), uses
`sorry` (a cast through an equality proved by either), is implemented by an `unsafe`
declaration (`implemented_by` is type-checked, but an `unsafe`
implementation, even one of the library's, can be applied to any type), or
is an `@[export]` definition under a C symbol of the library or one that
starts with `l2r_` (`librarySymbols`; `l2r_override_…` replaces a
function, `Mono.redirectTarget`): lean2rr calls such a definition in place
of another declaration without comparing their types.

An axiom that Lean adds for a proof by native evaluation, `e = true` for
a closed `Bool` term `e` that Lean ran and saw `true`
(`nativeEvalStatement?`: `native_decide`'s, `bv_decide`'s; lean-zip has
them), does not count by itself when the code that ran was the code of
the definitions (`nativeExempt`: no `implemented_by`, extern or kernel
evaluation on its way, and no `@[csimp]` theorem that may be false acting
on it). Then the axiom is true of the definitions, and proves no equation
between two types that the program could not prove without it (test
`RtCastNativeAxiom`). The walk goes on into the constants of `e`. Every
other axiom counts: an axiom the user writes can be false, `axiom bad :
true = false` proves `False` and so `Array UInt64 = Array Float` (test
`RtCastAxiomBoolEq`; before 2026-10-09 the compact arrays let every axiom
that states a `Bool` equation pass, and the other users of this fact let
none pass). So does kernel evaluation (`isKernelEvalConst`: `reduceBool`,
`reduceNat`, `ofReduceBool`, `ofReduceNat`), in a value or a type: its
truth rests on the compiled code of the program's constant that the
kernel ran (tests `RtCastReduceBool`, `RtCastReduceBoolCongr`).

An extern of the program does not count by itself: lean2rr runs Lean code
for it, which the walk reaches, or nothing (translation plan §5.8,
`Mono.computeExternRoute`): its `implemented_by` target; the `@[export]`
definition of its C symbol, bound only when the extern's type is an
instance of the definition's and their compiled signatures agree
(`Mono.bindingFailure?`), so that neither reads a value at another type
(the walk takes every definition exported under the symbol); its own
definition (its value, or the `_unsafe_rec` copy); or, refused, nothing
(the program is rejected, or with `L2R_ALLOW_MISSING_EXTERNS` does not
build). An extern of the program is never bound to Lean's runtime, and
the externs of Lean's library are the library's. Before the Lean-only
rule, an extern of the program could be linked C (which can read any
memory) and was bound to an `@[export]` definition unchecked (review
RV6T-01, test `RtCastExtern`), so every extern and `@[export]` counted.

The declarations reached are those the program's declarations come from
(`sourceDecls`), and, transitively: the constants their definitions mention
(inlined code no longer appears in the program); their `implemented_by`
targets; their `_unsafe_rec` copies, the code Lean compiles for a recursive
definition (for a `partial def`, whose value is only an inhabitant of its
type, the only place where its code shows: test `RtCastPartial`); and the
`@[export]` definitions of an extern's C symbol. Every `@[csimp]`
replacement that is a declaration of the program is a root, whether or not
the walk reaches the constant it replaces (`programCsimps`, also
`local` and `scoped` ones): compiled code calls the replacement, whose code
may be inlined (test `RtCastCsimp`), and the replaced constant may show
only in compiled code, where a `@[macro_inline]` definition of the library,
whose value the walk does not enter, puts it (`ite` becomes
`Decidable.casesOn`; test `RtCastCsimpMacroInline`).
Lean's library casts only where lean2rr's representations agree: an
`Array α` read as an `Array NonScalar` (`Box` elements) and back,
`unsafeCast ()` placeholders, `Subtype` (`attach`), the world token,
`Dynamic` values read at the type their `TypeName` names. -/
def programCasts (env : Environment) (keys : NameMap InstKey) (decls : Array (Decl .pure)) :
    Option Name := Id.run do
  let library (n : Name) : Bool := match env.getModuleIdxFor? n with
    | some i => (env.header.moduleNames[i.toNat]?.map isToolchainModule).getD false
    | none => false
  let csimps := programCsimps env
  -- Built on first use (most programs have no axiom of native evaluation).
  let mut exempt : Option NameSet := none
  -- Built on first use (most programs have no `@[export]` or extern).
  let mut libSyms : Option (Std.HashSet String) := none
  let mut exports : Option (Std.HashMap String (Array Name)) := none
  -- The roots: the program's `@[csimp]` replacements (a replacement that
  -- is a library declaration is not walked), and the sources of its
  -- declarations.
  let mut work : Array Name := csimps.filterMap fun c =>
    if library c.toDeclName then none else some c.toDeclName
  for d in decls do
    work := work ++ sourceDecls env ((keys.find? d.name).map (·.decl) |>.getD d.name)
  let mut seen : NameSet := {}
  while h : work.size > 0 do
    let n := work[work.size - 1]
    work := work.pop
    -- Kernel evaluation: true only if the compiled code of the program's
    -- constant that the kernel ran computes what its definition says.
    if isKernelEvalConst n then return some n
    if seen.contains n || library n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    if ci matches .axiomInfo _ then
      let ex := exempt.getD (nativeExempt env library csimps)
      exempt := some ex
      unless ex.contains n do return some n
      if let some e := nativeEvalStatement? ci then
        work := e.foldConsts work fun k acc => if seen.contains k then acc else acc.push k
    -- (A statement can use kernel evaluation, `reduceBool c = b`, whose
    -- proof `rfl` does not show it.)
    if ci.type.foldConsts false (fun k b => b || isKernelEvalConst k) then return some n
    if ci.isUnsafe then return some n
    if let some sym := getExportNameFor? env n then
      let sym := sym.toString (escape := false)
      let lib := libSyms.getD (librarySymbols env)
      libSyms := some lib
      if sym.startsWith "l2r_" || lib.contains sym then return some n
    if isExtern env n then
      if let some sym := getExternNameFor env `c n then
        let m := exports.getD (exportsBySymbol env)
        exports := some m
        for g in m.getD sym #[] do
          unless seen.contains g do work := work.push g
    let unsafeRec := Compiler.mkUnsafeRecName n
    if env.contains unsafeRec && !seen.contains unsafeRec then work := work.push unsafeRec
    if let some impl := Compiler.getImplementedBy? env n then
      -- An `unsafe` implementation counts even from the library: Lean only
      -- compares the declared types (`TypeName.mk` gives two types the same
      -- `TypeName`, so `Dynamic.get?` reads one as the other).
      if (env.find? impl).any (·.isUnsafe) then return some n
      work := work.push impl
    if let some v := ci.value? (allowOpaque := true) then
      if v.foldConsts false (fun k b => b || k == ``sorryAx) then return some n
      work := v.foldConsts work fun k acc => if seen.contains k then acc else acc.push k
  return none

/-- Whether a `Box` holding a value of type `vt` may be read at type `t`,
so that the unboxing function to `t` (generated at the end, `Finish`)
matches `vt`'s variant and converts it as `tryCoerce` does. Besides `t`
itself and its other representations (handled there), these are the types
that an `unsafeCast` reads as Lean represents them (plan §5.1):
- a `[value]` struct is natively its field;
- `UInt64`/`Float` and `UInt32`/`Float32` by their bits;
- words: `Nat`, `Int`, `UInt8/16/32`, `Bool`, enumerations and inductives
  with a constructor without fields (`isWordTarget`) read any of those, any
  other inductive and any other heap object (natively an address; here
  `objectWordBase`, see `wordOf`);
- another inductive whose constructors correspond to the value's
  (`isomorphic`): constructor by constructor (`structConv`), or the same
  object when the layouts agree (`retypable`).
A word or a scalar read as an object with fields (natively a number used as
an address) has no native value and stays unreachable. So does an inductive
read as one whose constructors do not all correspond (another number of
constructors): typed code converts such casts (`castFallback`), but every
unboxing function would then convert from every other inductive that
shares a constructor shape (programs over monad transformers grew by 3 to
5 %), for casts that hardly ever occur. None of these unless the program
can cast at all (`programCasts`).

The arm's conversion is `tryCoerce`, else `castFallback` (`genUnbox`). A
conversion that needs a function value at another representation (a
wrapper, §5.3) registers the wrapper and the conversion of function values
it needs, as any other conversion does, so whether a cast converts depends
only on the two types. (It used to be kept only when every wrapper it
needed was registered already, which made the result depend on the order
in which helpers were generated and, with `conv-liveness`, on which helpers
were live: review CLR-01, tests `RtCastFnWrapDead`, `RtCastFnWrapLive`,
`RtCastFnWrapOrder`.) This terminates: a wrapper is a variant `w<S>` of a
function type `T`, `S` and `T` being function types the program already has
(a conversion adds no function type), so there are at most F² wrappers and
conversions `l2r_fconv_S_T` for F function types, and a conversion's body is
generated again only when its source gains a variant (`finishFnValues`; with
`conv-liveness`, a variant that live code makes), which happens at most F
times per source. A pair this function accepts either converts or fails
before it registers a function-value helper (no pair here is two function
types), so a failed arm leaves nothing to undo. -/
partial def boxCastable (vt t : RR.Ty) : LowerM Bool := do
  if vt == t then return true
  unless (← read).programCasts do return false
  match vt, t with
  | .named a, .named b =>
    if [("u64", "f64"), ("f64", "u64"), ("u32", "f32"), ("f32", "u32")].contains (a, b) then return true
    let infos ← getPart (·.typeInfos)
    if let some ft := infos[a]?.bind valueFieldTy? then return ← boxCastable ft t
    if let some ft := infos[b]?.bind valueFieldTy? then return ← boxCastable vt ft
    if ← wordCastable a b (objects := true) then return true
    if b == "u64" && ((← isPureWord a) || (← wordCastable a "Nat" (objects := true))) then return true
    if infos.contains a && infos.contains b then return ← isomorphic a b
    return false
  | _, .named b => return (← isOtherObject vt) && ((← isPureWord b) || b == "u64")
  | _, _ => return false

end LeanToReussir
