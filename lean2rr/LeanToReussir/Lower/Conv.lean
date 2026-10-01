import LeanToReussir.Lower.LazyForce

/-! # Conversions -/

namespace LeanToReussir
open Lean Compiler LCNF

/-- Head constant of the Lean type a generated nominal type represents. -/
def nominalHead (n : String) : LowerM (Option Name) := do
  match (← get).typeKeys[n]? with
  | some k => return k.getAppFn.constName?
  | none => return none

/-- Whether a value of type `t` may contain a task (in fields, array
elements, a task's value). Types already being examined count as not
containing one (the least fixed point, for recursive types). Thunks,
function values and `Box` are not looked into. -/
partial def mayHoldTask (t : RR.Ty) (seen : List RR.Ty := []) : LowerM Bool := do
  if seen.contains t then return false
  let seen := t :: seen
  match t with
  | .app "LCell" _ =>
    match ← lazyOf? t with
    | some (_, true, _) => return true
    | _ => return false
  | .app "RVec" #[st] => mayHoldTask st seen
  | .named n =>
    if let some info := (← get).typeInfos[n]? then
      for c in info.ctorOrder do
        let some l := info.ctors.find? c | continue
        for ft in l.posTys do
          if ← mayHoldTask ft seen then return true
      return false
    match (← get).tupleTypes.toList.find? (·.2 == n) with
    | some (k, _) =>
      let fields := if k.size == 2 && k[1]! == .named "__elem_box" then #[k[0]!] else k
      for ft in fields do
        if ← mayHoldTask ft seen then return true
      return false
    | none => return false
  | _ => return false

/-- `l2r_persist_T(v)`, for a type that may contain tasks: waits for (runs)
every task in `v`, and the tasks in their values. Native Lean calls
`lean_mark_persistent` on a closed term when it is first evaluated
(`lean_obj_once_cold`), and that waits for each task it reaches
(`lean_task_get`): a `Task.spawn` extracted as a closed term has finished
once the term has been evaluated. `none` if `t` holds no task. -/
partial def taskPersistFn (t : RR.Ty) : LowerM (Option String) := do
  unless ← mayHoldTask t do return none
  let name := s!"l2r_persist_{t.enc}"
  let u64 := RR.Ty.named "u64"
  let zero : RR.Block := ⟨#[("z", some u64, .atom "0")], .var "z"⟩
  -- Persist each of the variables `xs`, then 0.
  let each (xs : Array (String × RR.Ty)) : LowerM RR.Block := do
    let mut lets := #[]
    for (x, xt) in xs do
      if let some f ← taskPersistFn xt then
        lets := lets.push (← fresh "pp", some u64, RR.Expr.call f #[] #[.var x])
    return ⟨lets, .atom "0"⟩
  let name ← lazyFn name do
    let body : RR.Block ← match t with
      | .app "LCell" _ =>
        let some (z, _, vt) ← lazyOf? t | pure zero
        let get ← lazyGetFn z
        let rest ← each #[("x", vt)]
        pure ⟨#[("x", some vt, .call get #[] #[.var "v"])] ++ rest.lets, rest.result⟩
      | .app "RVec" #[_] =>
        let some r ← arrayRepr? t | pure zero
        let go := name ++ "_go"
        let rest ← each #[("x", r.value)]
        let loop : RR.Block := .ofExpr <| .ite (.atom "i < n")
          ⟨#[("x", some r.value, r.load (r.call "get" #[.var "v", .var "i"]))] ++ rest.lets ++
            #[("one", some u64, .atom "1")], .call go #[] #[.var "v", .atom "i + one", .var "n"]⟩ zero
        modify fun s => { s with fns := s.fns.push (.fn go #[("v", t), ("i", u64), ("n", u64)] u64 loop) }
        pure ⟨#[("n", some u64, r.call "size" #[.var "v"]), ("i0", some u64, .atom "0")],
          .call go #[] #[.var "v", .var "i0", .var "n"]⟩
      | .named n =>
        if let some info := (← get).typeInfos[n]? then
          if info.shape == .struct then
            let some l := info.ctors.find? info.ctorOrder[0]! | pure zero
            let tys := l.posTys
            let xs := (List.range tys.size).toArray.map fun i => (s!"f{i}", tys[i]!)
            let rest ← each xs
            pure ⟨xs.mapIdx (fun i (x, xt) => (x, some xt, RR.Expr.field (.var "v") i)) ++ rest.lets, rest.result⟩
          else
            let mut arms : Array RR.Arm := #[]
            for c in info.ctorOrder do
              let some l := info.ctors.find? c | continue
              let tys := l.posTys
              let xs := (List.range tys.size).toArray.map fun i => (s!"f{i}", tys[i]!)
              arms := arms.push { ty := n, ctor := some l.variant, binders := xs.map (some ·.1), body := ← each xs }
            pure (.ofExpr (.mtch (.var "v") arms))
        else
          match (← get).tupleTypes.toList.find? (·.2 == n) with
          | some (k, _) =>
            let fields := if k.size == 2 && k[1]! == .named "__elem_box" then #[k[0]!] else k
            let xs := (List.range fields.size).toArray.map fun i => (s!"f{i}", fields[i]!)
            let rest ← each xs
            pure ⟨xs.mapIdx (fun i (x, xt) => (x, some xt, RR.Expr.field (.var "v") i)) ++ rest.lets, rest.result⟩
          | none => pure zero
      | _ => pure zero
    return #[.fn name #[("v", t)] u64 body]
  return some name

/-- The accessor of a constant (a declaration without parameters): its value
is computed once, by `<name>_init`, and kept in a runtime once-cell for the
rest of the run, like native Lean's CAFs and closed terms (translation plan
§5.12). The cell stores a boundary type; other values are boxed. A value
that may contain tasks first waits for them (`taskPersistFn`). -/
def cafAccessor (name : String) (ret : RR.Ty) : LowerM RR.Item := do
  let slot := (← get).cafSlots
  modify fun s => { s with cafSlots := slot + 1 }
  let (st, boxed) ← arrayElemTy ret
  let wrap (e : RR.Expr) : RR.Expr := match st with
    | .named bn => if boxed then .ctor bn none #[e] else e
    | _ => e
  let unwrap (e : RR.Expr) : RR.Expr := if boxed then .field e 0 else e
  let k := RR.Expr.atom (toString slot)
  let init := RR.Expr.call (name ++ "_init") #[] #[]
  let init := match ← taskPersistFn ret with
    | some f => RR.Expr.block ⟨#[("v", some ret, init), ("p", some (.named "u64"), .call f #[] #[.var "v"])], .var "v"⟩
    | none => init
  let body : RR.Block := .ofExpr (.ite (.call "l2r_once_has" #[] #[k])
    (.ofExpr (unwrap (.call "l2r_once_get" #[st] #[k])))
    (.ofExpr (unwrap (.call "l2r_once_set" #[st] #[k, wrap init]))))
  return .fn name #[] ret body

/-- A placeholder of Reussir type `t`. Lean passes `box(0)` for values that
are never inspected: erased arguments (`◾`) at relevant types, and the
`unsafeCast ()` its library stores into array slots so that the element
being updated stays unshared (`Array.modifyMUnsafe`, `Array.mapMUnsafe`).
lean2rr materializes `box(0)` at the expected type as that type's zero:
`0`, `false`, the first constructor whose fields have zeros, a closure
returning a zero, an empty array (for `Nat`, `Bool` and enumerations this is
exactly what `box(0)` denotes in Lean). Only a type without a finite value
gets `l2r_unreachable`. Each placeholder is a generated function
`l2r_zero_N`. A placeholder that would allocate (a string, an array, a
record, a closure, a boxed unit) is built once and kept in a once-cell like
a constant (`cafAccessor`): `Array.modify` stores one per update, and it is
never inspected, so a shared value does as well as a fresh one. -/
partial def zeroValue (t : RR.Ty) : LowerM RR.Expr := do
  if t == .unit then return .unitVal
  if let some f := (← get).zeroFns[t]? then return .call f #[] #[]
  let f ← fresh "l2r_zero_"
  modify fun s => { s with zeroFns := s.zeroFns.insert t f, zeroBusy := s.zeroBusy.insert t }
  let lit (text : String) : RR.Block := ⟨#[("z", some t, .atom text)], .var "z"⟩
  let unreachable : RR.Block := .ofExpr (.call "l2r_unreachable" #[t] #[])
  let body : RR.Block ← match t with
    | .named n =>
      if n ∈ ["u8", "u16", "u32", "u64", "i8", "i16", "i32", "i64"] then pure (lit "0")
      else if n ∈ ["f32", "f64"] then pure (lit "0.0")
      else if n == "bool" then pure (.ofExpr (.atom "false"))
      else if n == "Nat" then
        pure ⟨#[("z", some (.named "u64"), .atom "0")], .ctor "Nat" (some "Small") #[.var "z"]⟩
      else if n == "Int" then
        pure ⟨#[("z", some (.named "i64"), .atom "0")], .ctor "Int" (some "Small") #[.var "z"]⟩
      else if n == "LStr" then pure (.ofExpr (← strLit ""))
      else if n == "LNatArr" then pure (.ofExpr (.call "l2r_natarr_empty" #[] #[]))
      else if n == "LIntArr" then pure (.ofExpr (.call "l2r_intarr_empty" #[] #[]))
      else if n == boxName then
        pure (.ofExpr (.ctor boxName (some (← boxVariant .unit)) #[.unitVal]))
      else if let some (e, k) := (← get).refInfos[n]? then
        -- A reference (never used: any cell will do).
        if (← get).zeroBusy.contains e then pure unreachable
        else pure (.ofExpr (refNew t e k (← zeroValue e)))
      else if let some info := (← get).typeInfos[n]? then
        -- The first constructor none of whose fields is a type whose
        -- placeholder is being built (so the value is finite).
        let busy := (← get).zeroBusy
        let ok (tys : Array RR.Ty) := tys.all fun ft => !busy.contains ft
        let fieldsOf (layout : CtorLayout) := layout.posTys
        let cands := info.ctorOrder.filterMap info.ctors.find?
        match cands.find? (fieldsOf · |>.isEmpty) <|> cands.find? (ok ∘ fieldsOf) with
        | some layout =>
          let vals ← (fieldsOf layout).mapM zeroValue
          pure <| .ofExpr <| match info.shape with
            | .struct => .ctor n none vals
            | _ => .ctor n (some layout.variant) vals
        | none => pure unreachable
      else
        -- Generated positional structs (`Tuple…`, `ElemBox…`).
        match (← get).tupleTypes.toList.find? (·.2 == n) with
        | some (k, _) =>
          let fields := if k.size == 2 && k[1]! == .named "__elem_box" then #[k[0]!] else k
          if fields.any (← get).zeroBusy.contains then pure unreachable
          else pure (.ofExpr (.ctor n none (← fields.mapM zeroValue)))
        | none => pure unreachable
    | .app "RVec" #[e] => pure (.ofExpr (.call "l2r_array_empty" #[e] #[]))
    | .app "LCell" _ =>
      match ← lazyOf? t with
      | some (z, _, vt) =>
        if (← get).zeroBusy.contains vt then pure unreachable
        else pure (.ofExpr (lazyDone z (← zeroValue vt)))
      | none => pure unreachable
    -- A function value that is never applied (applying it gives a zero).
    | .fn .. => pure (.ofExpr (.ctor (RR.fnTypeName t) (some "z") #[]))
    | _ => pure unreachable
  modify fun s => { s with zeroBusy := s.zeroBusy.erase t }
  -- Heap values are shared (a nullary constructor of a shared enum does not
  -- allocate).
  let heap ← match t with
    | .named n =>
      if n ∈ ["LStr", "LNatArr", "LIntArr", boxName] || (← get).refInfos.contains n then pure true
      else match (← get).typeInfos[n]? with
        | some info => pure (info.shape != .enumLike && !info.value)
        | none => pure ((← storageElem t).2)
    | .app "RVec" _ | .fn .. => pure true
    | _ => pure false
  let nullary := match body with
    | ⟨#[], .ctor _ _ #[]⟩ => true
    | _ => false
  if heap && !nullary && (← read).cachePlaceholders then
    let acc ← cafAccessor f t
    modify fun s => { s with fns := s.fns.push (.fn (f ++ "_init") #[] t body) |>.push acc }
  else
    modify fun s => { s with fns := s.fns.push (.fn f #[] t body) }
  return .call f #[] #[]

/-- The index of a value of an enumeration type (a generated `[value]`
enum without fields), as `u64`: a generated `match`. -/
def enumIndexFn (tn : String) : LowerM String := do
  let name := s!"l2r_enum_index_{tn}"
  unless (← get).fns.any (fun | .fn n .. => n == name | _ => false) do
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
  unless (← get).fns.any (fun | .fn n .. => n == name | _ => false) do
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

/-- Unwrap a `Box` whose variant for Reussir type `t` is fixed by the Lean
types: the variant's payload, or, for a boxed unit, the placeholder of `t`
(a boxed unit used at another type is Lean's `box(0)`, see `zeroValue`); any
other variant is unreachable. -/
def unboxMatch (e : RR.Expr) (t : RR.Ty) (slow : Option String := none) : LowerM RR.Expr := do
  let v ← boxVariant t
  let u ← boxVariant .unit
  let x ← fresh "ub"
  let mut arms : Array RR.Arm :=
    #[{ ty := boxName, ctor := some v, binders := #[some x], body := .ofExpr (.var x) }]
  if u != v then
    arms := arms.push { ty := boxName, ctor := some u, binders := #[none], body := .ofExpr (← zeroValue t) }
  -- Other variants: unreachable, or the generated unboxing function `slow`
  -- (values of other types read through `unsafeCast`).
  let (e, pre) ← match slow, e with
    | none, _ | some _, .var _ => pure (e, #[])
    | some _, _ => do
      let b ← fresh "ubx"
      pure (RR.Expr.var b, #[(b, some RR.Ty.box, e)])
  let other : RR.Expr := match slow with
    | some f => .call f #[] #[e]
    | none => .call "l2r_unreachable" #[t] #[]
  let m := RR.Expr.mtch e (arms.push { ty := boxName, ctor := none, binders := #[], body := .ofExpr other })
  return if pre.isEmpty then m else .block ⟨pre, m⟩

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

/-- A generated type whose values are heap objects natively when they have
fields: a shared struct or enum (not a `[value]` type, not an enumeration). -/
def isObjectNominal (n : String) : LowerM Bool := do
  match (← get).typeInfos[n]? with
  | some info => return !info.value && info.shape != .enumLike
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
  unless (← get).fns.any (fun | .fn n .. => n == name | _ => false) do
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
  unless (← get).fns.any (fun | .fn n .. => n == name | _ => false) do
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
    if n ∈ ["LStr", "LNatArr", "LIntArr", "LHandle", "f64", "f32"] then return true
    return (← get).refInfos.contains n
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
`w : u64` (see `wordOf`): `Nat` `w`; `Int` the signed value of its 32 bits
(`lean_scalar_to_int64`); a fixed-width integer, `Bool` (nonzero) or an
enumeration the bits of its width (`lean_unbox` then truncation; an index
past the last constructor gives the last one, as Lean's `switch` does); a
constructor without fields (`ctorOfWordFn`). `none` for other types. -/
def ofWord (w : RR.Expr) (n : String) : LowerM (Option RR.Expr) := do
  let u64 := RR.Ty.named "u64"
  if n == "Nat" then return some (.ctor "Nat" (some "Small") #[w])
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
    let infos := (← get).typeInfos
    let (some ai, some bi) := (infos[an]?, infos[bn]?) | return none
    if ai.value != bi.value || ai.shape != bi.shape || ai.ctorOrder.size != bi.ctorOrder.size then return none
    let sameHead := (← nominalHead an) == (← nominalHead bn)
    let mut asm := assumed.push (an, bn)
    for (ca, cb) in ai.ctorOrder.zip bi.ctorOrder do
      let (some la, some lb) := (ai.ctors.find? ca, bi.ctors.find? cb) | return none
      let pa := la.posTys
      let pb := lb.posTys
      if pa.size != pb.size then return none
      -- The fields a conversion pairs are at the same record positions.
      if sameHead then
        if la.fields.map (·.map (·.1)) != lb.fields.map (·.map (·.1)) then return none
      else
        let some fm ← castFieldMap ca cb la lb | return none
        for h : j in [:lb.fields.size] do
          let some (p, _) := lb.fields[j] | continue
          let some (some k) := fm[j]?.join | return none
          if (la.fields[k]?.join.map (·.1)) != some p then return none
      for (x, y) in pa.zip pb do
        let some asm' ← retypableAux x y asm | return none
        asm := asm'
    return some asm
  | .app "RVec" #[x], .app "RVec" #[y] =>
    -- Element storage: the same wrapping, wrapped values retypable.
    let (ex, bx) ← storageElem x
    let (ey, by_) ← storageElem y
    if bx != by_ then return none
    retypableAux (if bx then ex else x) (if bx then ey else y) assumed
  | _, _ => return none

/-- Whether a value of Reussir type `a` can be used as a value of type `b`
as it is, the same object reinterpreted (`l2r_retype`): both cross the FFI
boundary (shared records, arrays), and their layouts are the same: records
with the same constructors whose fields, position by position, have the
same layouts (coinductively, for recursive types), arrays of such
elements; the conversion between them (`structConv`, `vecConv`) would pair
exactly those fields. Instantiations of an inductive that differ only in
phantom positions, and isomorphic inductives read through `unsafeCast` (a
user list as `List`), are then not converted at all: no time, no copy, and
the value keeps its identity. -/
def retypable (a b : RR.Ty) : LowerM Bool := do
  if a == b then return false
  if !(← isBoundaryTy a) || !(← isBoundaryTy b) then return false
  match a with
  | .named n => if n == boxName || !(← get).typeInfos.contains n then return false
  | .app "RVec" _ => pure ()
  | _ => return false
  return (← retypableAux a b #[]).isSome

/-- A number naming Reussir type `t` at run time (FNV-1a of its text), for
`l2r_origin_back`. -/
def typeCode (t : RR.Ty) : Nat := Id.run do
  let mut h : UInt64 := 14695981039346656037
  for c in t.render.toList do
    h := (h ^^^ c.toNat.toUInt64) * 1099511628211
  return h.toNat

/-- The body of a structural conversion's entry function from `src` to
`dst` (parameter `x`), around the conversion proper `worker`: a value
converted from a `dst` (and unchanged since: the record holds it, so an
update copies) is converted back to that very value; otherwise the new
value records its origin (`leanrt::origin`). Natively there is one object:
so `ptrAddrUnsafe` of the converted value is the original's, and a value
that goes into uniform code and back is the same object (plan §9). -/
def originWrap (src dst : RR.Ty) (worker x : String) : RR.Block :=
  let v := RR.Expr.var x
  .ofExpr (.ite (.call "l2r_origin_back" #[src] #[v, .atom (toString (typeCode dst))])
    (.ofExpr (.call "l2r_origin_take" #[src, dst] #[v]))
    (.ofExpr (.call "l2r_origin_note" #[src, dst] #[v, .call worker #[] #[v], .atom (toString (typeCode src))])))

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
in `sn`'s constructor order: by name for instantiations of one inductive (a
field relevant in the target but not in the source, a proof-like type such
as `PLift p` in one of the instantiations, was never inspected: its
placeholder); for another inductive read through `unsafeCast`, as Lean's
`cases` reads the value: by tag (`ctorAtTag`), a target constructor without
fields whatever the source holds, an object's fields by native slot
(`castFieldMap`), and no value for a boxed scalar read as an object with
fields. -/
def convArms (sn dn : String) : LowerM (Array ConvArm) := do
  let some si := (← get).typeInfos[sn]? | throwError "lean2rr: no type {sn}"
  let some di := (← get).typeInfos[dn]? | throwError "lean2rr: no type {dn}"
  let sameHead := (← nominalHead sn) == (← nominalHead dn)
  let mut out := #[]
  for h : ci in [:si.ctorOrder.size] do
    let ctor := si.ctorOrder[ci]
    let some sl := si.ctors.find? ctor | continue
    let target? := if sameHead then (di.ctors.find? ctor).map (ctor, ·) else ctorAtTag di ci
    match target? with
    | none =>
      unless sameHead do out := out.push { sl, dl := none, fields := #[] }
    | some (dctor, dl) =>
      let targets := (List.range dl.fields.size).toArray.filterMap fun j => (dl.fields[j]?.join).map fun f => (j, f.2)
      if sameHead then
        out := out.push { sl, dl := some dl, fields := targets.map fun (j, dt) => (sl.fields[j]?.join, dt) }
      else if ← nativeScalarCtor dctor dl then
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

/-- A recursive field of a constructor in a conversion group (see
`convMachine`): its index among the arm's fields, record position, source
and target types, whether it is an array whose elements are converted, and
the group member converting it (or its elements). -/
structure ConvSlot where
  idx : Nat
  pos : Nat
  st : RR.Ty
  dt : RR.Ty
  arr : Bool
  q : Nat
  deriving Inhabited

mutual
  /-- Convert `e` from representation `src` to `dst`. Besides `Box`
  conversions and closure wrappers, two instantiations of the same inductive
  are converted structurally: Lean's mono `cse` compares erased types, so it
  may merge e.g. `[] : List Shape` with `[] : List Nat`; such a merged value
  carries no data at the differing type parameter, so rebuilding it at the
  target type is always possible (an arm that would need an impossible
  element conversion is unreachable). -/
  partial def coerce (e : RR.Expr) (src dst : RR.Ty) : LowerM RR.Expr := do
    -- A cast the program performs between inductives that do not
    -- correspond constructor for constructor: by constructor (see
    -- `castFallback`), not by `tryCoerce`'s words.
    if let (.named sn, .named dn) := (src, dst) then
      if (← nominalHead sn) != (← nominalHead dn) && !(← isomorphic sn dn) && (← ctorCastable sn dn) then
        return .call (← structConv sn dn) #[] #[e]
    match ← tryCoerce e src dst with
    | some r => return r
    | none =>
      if let some r ← castFallback e src dst then return r
      let keyOf (t : RR.Ty) : LowerM String := do
        match t with
        | .named n => return match (← get).typeKeys[n]? with | some k => s!"{n} = {k}" | none => n
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
    if dst == RR.Ty.box then
      return some (.ctor boxName (some (← boxVariant src)) #[e])
    if src == RR.Ty.box then
      match dst with
      | .fn .. => return some (.call (← unboxFnFn dst) #[] #[e])
      | _ =>
        if let .named tn := dst then
          if (← get).typeInfos.contains tn then
            -- Any instantiation of the same inductive may have been boxed,
            -- and (through `unsafeCast`) values of types Lean represents
            -- alike (`boxCastCompatible`).
            return some (.call (← unboxFn tn) #[] #[e])
          if tn ∈ ["Nat", "Int", "u8", "u16", "u32", "bool", "u64", "f64", "f32"] then
            -- The variant of `dst` in line; others (another word type read
            -- through `unsafeCast`) through the generated function.
            return some (← unboxMatch e dst (slow := some (← unboxFn tn)))
        if (← arrayRepr? dst).isSome || dst matches .app "LCell" _ then
          -- Any representation of the same array (or thunk, task) type may
          -- have been boxed.
          return some (.call (← unboxArrFn dst) #[] #[e])
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
      -- converted at each application.
      let some _ ← tryCoerce (.var "l2rcv") a2 a1 | return none
      let some _ ← tryCoerce (.var "l2rcv") b1 b2 | return none
      addFnVariant dst (.wrap src)
      return some (.call (← fnConvFn src dst) #[] #[e])
    -- Between a function value and a Reussir closure (prelude callbacks):
    -- a lambda. `e` is bound first, so that it is evaluated once.
    | .fn a1 b1, .cls a2 b2 =>
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
    | .cls a1 b1, .fn a2 b2 =>
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
      -- Instantiations of one inductive, or (through `unsafeCast`) another
      -- inductive that Lean represents alike: constructor by constructor.
      if let (some sh, some dh) := (← nominalHead sn, ← nominalHead dn) then
        if sh == dh || (← isomorphic sn dn) then
          if ← retypable src dst then return some (.call "l2r_retype" #[src, dst] #[e])
          return some (.call (← structConv sn dn) #[] #[e])
      -- The rest is only reachable through `unsafeCast`, between values that
      -- Lean represents by the same word; the conversions follow Lean's
      -- `lean_box`/`lean_unbox`. Scalars of the same size in a constructor's
      -- scalar area: the bits.
      match sn, dn with
      | "u64", "f64" => return some (.call "lean_float_of_bits" #[] #[e])
      | "f64", "u64" => return some (.call "lean_float_to_bits" #[] #[e])
      | "u32", "f32" => return some (.call "lean_float32_of_bits" #[] #[e])
      | "f32", "u32" => return some (.call "lean_float32_to_bits" #[] #[e])
      -- `Nat` and `Int`: the same value (natively the same boxed scalar for
      -- small values, the same big number object otherwise; a `Nat` from
      -- 2^31 to 2^63 is not a valid small `Int` natively).
      | "Nat", "Int" => return some (.call "lean_nat_to_int" #[] #[e])
      | "Int", "Nat" => return some (.call "l2r_int_cast_nat" #[] #[e])
      | _, _ => pure ()
      -- A `[value]` struct is natively its field.
      let infos := (← get).typeInfos
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
      vecCoerce e src dst
    | .app "LCell" #[.named sz], .app "LCell" #[.named dz] =>
      match ← lazyConv sz dz with
      | some f => return some (.call f #[] #[e])
      | none => return none
    | _, _ => vecCoerce e src dst

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

  /-- Arrays whose element types differ (an array reinterpreted by Lean's
  uniform-representation code, e.g. `Array α` as `Array NonScalar`): rebuilt
  element by element. -/
  partial def vecCoerce (e : RR.Expr) (src dst : RR.Ty) : LowerM (Option RR.Expr) := do
    let some sr ← arrayRepr? src | return none
    let some dr ← arrayRepr? dst | return none
    if ← retypable src dst then return some (.call "l2r_retype" #[src, dst] #[e])
    match ← vecConv src dst sr dr with
    | some f => return some (.call f #[] #[e])
    | none => return none

  /-- The generated function converting an array with element storage `se`
  to one with element storage `de` (cached), recording the origin of the
  new array (`originWrap`). -/
  partial def vecConv (src dst : RR.Ty) (sr dr : ArrayRepr) : LowerM (Option String) := do
    let nested := (← get).convNested
    if let some f := (← get).vecConvs[(src, dst)]? then return some (if nested then f ++ "_w" else f)
    let f ← fresh "l2r_vconv_"
    modify fun s => { s with vecConvs := s.vecConvs.insert (src, dst) f }
    let x := sr.load (sr.call "get" #[.var "src", .var "i"])
    -- Elements that cannot be converted (`Array Nat` to `Array Int`) mean
    -- that the array is empty whenever this runs: an empty array that `cse`
    -- shared between two element types, or the array `Array.map` returns
    -- when it had nothing to map (Stage 3).
    modify fun s => { s with convNested := true }
    let y ← match ← tryCoerce x sr.value dr.value with
      | some y => pure y
      | none => pure (.call "l2r_unreachable" #[dr.value] #[])
    modify fun s => { s with convNested := nested }
    let go := f ++ "_go"
    let u64 := RR.Ty.named "u64"
    let loop : RR.Block := .ofExpr <| .ite (.atom "i < n")
      ⟨#[("one", some u64, .atom "1"), ("y", some dr.storage, dr.store y)],
        .call go #[] #[.var "src", .atom "i + one", .var "n", dr.call "push" #[.var "acc", .var "y"]]⟩
      (.ofExpr (.var "acc"))
    let entry : RR.Block :=
      ⟨#[("n", some u64, sr.call "size" #[.var "src"]), ("zero", some u64, .atom "0")],
        .call go #[] #[.var "src", .var "zero", .var "n", dr.call "empty" #[]]⟩
    modify fun s => { s with fns := s.fns ++ #[
      .fn go #[("src", src), ("i", u64), ("n", u64), ("acc", dst)] dst loop,
      .fn (f ++ "_w") #[("src", src)] dst entry,
      .fn f #[("src", src)] dst (originWrap src dst (f ++ "_w") "src")] }
    return some (if nested then f ++ "_w" else f)

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

  /-- The generated function converting a thunk or task with state type `sz`
  to one with state type `dz` (same kind, value types differing only in
  representation, as for `structConv`). The result is a new cell that
  records the cell it was converted from, boxed, and that cell's address:
  converting it back gives that very cell (a thunk crossing between typed
  and uniform code in a loop does not build a chain of cells), its identity
  is the original's (`ptrAddrUnsafe`, see `addrOf`; for a task also the
  runtime's, `l2r_task_addr_S`), and keeping the original keeps that
  address from being reused. A computed value is converted now (state
  `convdone`). Otherwise the new cell is in state `conv`: its computation
  forces the original and converts the value (so the original's
  computation still runs at most once). A cell converted from a converted
  one records the first original. `none` if the values are not
  convertible. -/
  partial def lazyConv (sz dz : String) : LowerM (Option String) := do
    let some (sk, st) := (← get).lazyInfos[sz]? | return none
    let some (dk, dt) := (← get).lazyInfos[dz]? | return none
    if sk != dk then return none
    let name := s!"l2r_lazyconv_{sz}_{dz}"
    if (← get).lazyFnNames.contains name then return some name
    modify fun s => { s with lazyFnNames := s.lazyFnNames.insert name }
    let fail : LowerM (Option String) := do
      modify fun s => { s with lazyFnNames := s.lazyFnNames.erase name }
      return none
    let some now ← tryCoerce (.var "v") st dt | fail
    let get ← lazyGetFn sz
    let some later ← tryCoerce (.call get #[] #[.var "c"]) st dt | fail
    let srcCell := RR.Ty.app "LCell" #[.named sz]
    let dstCell := RR.Ty.app "LCell" #[.named dz]
    let srcBox ← boxVariant srcCell
    let dstBox ← boxVariant dstCell
    let u ← fresh "u"
    let mkConv (o a : RR.Expr) : RR.Expr := .call "l2r_lcell_new" #[.named dz]
      #[.ctor dz (some "conv") #[rawFnValue (.fn .unit dt) u (.ofExpr later), o, a]]
    let ident : RR.Expr := .call "l2r_lcell_addr" #[.named sz] #[.var "c"]
    let fresh' : RR.Block := ⟨#[("o", some RR.Ty.box, .ctor boxName (some srcBox) #[.var "c"]),
      ("a", some (.named "u64"), ident)], mkConv (.var "o") (.var "a")⟩
    let doneConv : RR.Block := ⟨#[("w", some dt, now), ("o", some RR.Ty.box, .ctor boxName (some srcBox) #[.var "c"]),
      ("a", some (.named "u64"), ident)],
      .call "l2r_lcell_new" #[.named dz] #[.ctor dz (some "convdone") #[.var "w", .var "o", .var "a"]]⟩
    -- From a converted cell: its original if that has the target type,
    -- otherwise the original converted directly (through the `Box`
    -- converter, which knows every representation), so chains through
    -- several representations stay one level deep.
    let back : RR.Expr := .mtch (.var "o") #[
      { ty := boxName, ctor := some dstBox, binders := #[some "x"], body := .ofExpr (.var "x") },
      { ty := boxName, ctor := none, binders := #[], body := .ofExpr (.call (← unboxArrFn dstCell) #[] #[.var "o"]) }]
    let busy : RR.Block := ⟨#[("o", some RR.Ty.box, .ctor boxName (some srcBox) #[.var "c"])], mkConv (.var "o") (.var "a")⟩
    let body : RR.Block := .ofExpr (.mtch (.call "l2r_lcell_get" #[.named sz] #[.var "c"]) #[
      lazyArm sz "done" #[some "v"] doneConv,
      lazyArm sz "conv" #[none, some "o", some "a"] (.ofExpr back),
      lazyArm sz "convdone" #[none, some "o", some "a"] (.ofExpr back),
      lazyArm sz "busyconv" #[some "a"] busy,
      { ty := sz, ctor := none, binders := #[], body := fresh' }])
    modify fun s => { s with fns := s.fns.push (.fn name #[("c", srcCell)] dstCell body) }
    return some name

  /-- The pair of generated nominal types that `tryCoerce` converts from
  `st` to `dt` with `structConv` (instantiations of one inductive,
  isomorphic inductives), unless the value is reused as it is
  (`retypable`). -/
  partial def structPair? (st dt : RR.Ty) : LowerM (Option (String × String)) := do
    if st == dt then return none
    let (.named a, .named b) := (st, dt) | return none
    if a == boxName || b == boxName then return none
    let infos := (← get).typeInfos
    unless infos.contains a && infos.contains b do return none
    let (some sh, some dh) := (← nominalHead a, ← nominalHead b) | return none
    unless sh == dh || (← isomorphic a b) do return none
    if ← retypable st dt then return none
    return some (a, b)

  /-- A field conversion `st → dt` that converts values of a pair of
  nominal types with `structConv`: the field itself (`false`) or the
  elements of an array field (`true`, as `vecConv` does). -/
  partial def slotPair? (st dt : RR.Ty) : LowerM (Option (Bool × (String × String))) := do
    if let some p ← structPair? st dt then return some (false, p)
    if st == dt then return none
    let (some sr, some dr) := (← arrayRepr? st, ← arrayRepr? dt) | return none
    if ← retypable st dt then return none
    match ← structPair? sr.value dr.value with
    | some p => return some (true, p)
    | none => return none

  /-- The conversion group of pair `root`: the pairs its fields convert
  (directly or as array elements), transitively, that convert `root`
  again. `root` comes first. -/
  partial def convGroup (root : String × String) : LowerM (Array (String × String)) := do
    let mut nodes : Array (String × String) := #[root]
    let mut edges : Array (Array Nat) := #[]
    let mut i := 0
    while i < nodes.size do
      let (a, b) := nodes[i]!
      let mut out := #[]
      for arm in ← convArms a b do
        if arm.dl.isNone then continue
        for (src?, dt) in arm.fields do
          let some (_, st) := src? | continue
          if let some (_, p) ← slotPair? st dt then
            match nodes.idxOf? p with
            | some k => out := out.push k
            | none =>
              nodes := nodes.push p
              out := out.push (nodes.size - 1)
      edges := edges.push out
      i := i + 1
    let mut reach := (Array.replicate nodes.size false).set! 0 true
    let mut changed := true
    while changed do
      changed := false
      for k in [:nodes.size] do
        if !reach[k]! && (edges[k]!.any fun t => reach[t]!) then
          reach := reach.set! k true
          changed := true
    return (List.range nodes.size).toArray.filterMap fun k => if reach[k]! then some nodes[k]! else none

  /-- The recursive fields of each constructor of each member of `group`
  (see `ConvSlot`), with the constructors (`convArms`). -/
  partial def convSlots (group : Array (String × String)) :
      LowerM (Array (Array (ConvArm × Array ConvSlot))) := do
    let mut plans := #[]
    for (a, b) in group do
      let mut ps := #[]
      for arm in ← convArms a b do
        let mut slots := #[]
        if arm.dl.isSome then
          for h : j in [:arm.fields.size] do
            let (src?, dt) := arm.fields[j]
            let some (p, st) := src? | continue
            if let some (isArr, pr) ← slotPair? st dt then
              if let some q := group.idxOf? pr then
                slots := slots.push { idx := j, pos := p, st, dt, arr := isArr, q }
        ps := ps.push (arm, slots)
      plans := plans.push ps
    return plans

  /-- The value of constructor arm `arm` of `sn` converted to `dn`, with the
  source value in `x` and the converted values of some fields given
  (`given`: arm field index ↦ expression); the other fields are converted
  here (`tryCoerce`) or placeholders. Unreachable when the arm has no
  native value or a field has no conversion. -/
  partial def convBuild (sn dn : String) (arm : ConvArm) (x : RR.Expr)
      (given : Array (Nat × RR.Expr)) : LowerM RR.Expr := do
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
      if let some (_, e) := given.find? (·.1 == j) then
        vals := vals.push e
        continue
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

  /-- `structConv` for a pair whose conversion recurses through several
  fields of a constructor, through other pairs (mutual and nested
  inductives: a rose tree's `List` of trees) or through array elements:
  an explicit-stack loop instead of recursion, so that the depth of the
  value does not use stack (plan §5.1). `fname(x)` runs a self tail-calling
  function `fname_m(mode, k)` (a loop): `mode` is a source value of a member
  of `group` to convert (`d<a>`) or a converted value to return (`u<a>`),
  and `k` the stack of pending constructors: `k<a>_<b>_<i>` holds a source
  value of member `a`, constructor `b`, whose recursive fields before the
  `i`-th are converted (their values), the `i`-th being converted (for an
  array field, also the source array, the index, the size and the elements
  converted so far). The other fields are converted when the constructor is
  built (`fname_b<a>_<b>`), by `tryCoerce`. -/
  partial def convMachine (fname : String) (group : Array (String × String))
      (plans : Array (Array (ConvArm × Array ConvSlot))) : LowerM Unit := do
    let u64 := RR.Ty.named "u64"
    let kName ← fresh "L2RConvK"
    let mName ← fresh "L2RConvM"
    let kTy := RR.Ty.named kName
    let mTy := RR.Ty.named mName
    let srcTy (a : Nat) : RR.Ty := .named group[a]!.1
    let dstTy (a : Nat) : RR.Ty := .named group[a]!.2
    let rootTy := dstTy 0
    let go := fname ++ "_m"
    let buildName (a b : Nat) : String := s!"{fname}_b{a}_{b}"
    let kVariant (a b i : Nat) : String := s!"k{a}_{b}_{i}"
    let unreachable := RR.Expr.call "l2r_unreachable" #[rootTy] #[]
    -- The frame types.
    let mut kVariants : Array (String × Array RR.Ty) := #[("kdone", #[])]
    for h : a in [:plans.size] do
      for h2 : b in [:plans[a].size] do
        let (_, slots) := plans[a][b]
        for h3 : i in [:slots.size] do
          let sl := slots[i]
          let before := (slots.extract 0 i).map (·.dt)
          let arrTys := if sl.arr then #[sl.st, u64, u64, sl.dt] else #[]
          kVariants := kVariants.push (kVariant a b i, #[srcTy a] ++ before ++ arrTys ++ #[kTy])
    let mVariants := ((List.range group.size).toArray.map fun a => (s!"d{a}", #[srcTy a])) ++
      ((List.range group.size).toArray.map fun a => (s!"u{a}", #[dstTy a]))
    modify fun s => { s with typeItems := s.typeItems.push (.enum kName false kVariants) |>.push (.enum mName false mVariants) }
    let goCall (m : RR.Expr) (k : RR.Expr) : RR.Expr := .call go #[] #[m, k]
    let down (q : Nat) (v : RR.Expr) : RR.Expr := .ctor mName (some s!"d{q}") #[v]
    let up (a : Nat) (v : RR.Expr) : RR.Expr := .ctor mName (some s!"u{a}") #[v]
    -- Field at record position `p` of `x`, a value of member `a`'s source
    -- type known to be constructor `arm`.
    let fieldOf (a : Nat) (arm : ConvArm) (x : RR.Expr) (p : Nat) (t : RR.Ty) : LowerM RR.Expr := do
      let some si := (← get).typeInfos[group[a]!.1]? | throwError "lean2rr: no type"
      if si.shape == .struct then return .field x p
      let n ← fresh "fo"
      let nrel := (arm.sl.fields.filterMap id).size
      let binders := (Array.replicate nrel (none : Option String)).set! p (some n)
      return .mtch x #[{ ty := group[a]!.1, ctor := some arm.sl.variant, binders, body := .ofExpr (.var n) },
        { ty := group[a]!.1, ctor := none, binders := #[], body := .ofExpr (.call "l2r_unreachable" #[t] #[]) }]
    -- The build functions.
    for h : a in [:plans.size] do
      for h2 : b in [:plans[a].size] do
        let (arm, slots) := plans[a][b]
        if arm.dl.isNone then continue
        let rs := (List.range slots.size).toArray.map fun i => s!"r{i}"
        let given := (slots.zip rs).map fun (sl, r) => (sl.idx, RR.Expr.var r)
        let body ← convBuild group[a]!.1 group[a]!.2 arm (.var "x") given
        modify fun s => { s with fns := s.fns.push (.fn (buildName a b) (#[("x", srcTy a)] ++ (rs.zip (slots.map (·.dt)))) (dstTy a) (.ofExpr body)) }
    -- Start converting recursive field `i` of constructor `b` of member
    -- `a` (value `x`, earlier fields converted to `rs`, frames below `k`),
    -- or build the constructor when all are.
    let rec start (fuel : Nat) (a b i : Nat) (x : RR.Expr) (rs : Array RR.Expr) (k : RR.Expr) : LowerM RR.Expr := do
      let (arm, slots) := plans[a]![b]!
      match fuel, slots[i]? with
      | _, none => return goCall (up a (.call (buildName a b) #[] (#[x] ++ rs))) k
      | 0, _ => return unreachable
      | fuel + 1, some sl =>
        let frame (extra : Array RR.Expr) : RR.Expr := .ctor kName (some (kVariant a b i)) (#[x] ++ rs ++ extra ++ #[k])
        let fv ← fieldOf a arm x sl.pos sl.st
        if !sl.arr then return goCall (down sl.q fv) (frame #[])
        let some sr ← arrayRepr? sl.st | throwError "lean2rr: bad array type"
        let some dr ← arrayRepr? sl.dt | throwError "lean2rr: bad array type"
        let src ← fresh "cs"
        let n ← fresh "cn"
        let z ← fresh "cz"
        let srcV := RR.Expr.var src
        let first := sr.load (sr.call "get" #[srcV, .var z])
        let empty := dr.call "empty" #[]
        let rest ← start fuel a b (i + 1) x (rs.push empty) k
        return .block ⟨#[(src, some sl.st, fv), (n, some u64, sr.call "size" #[srcV]), (z, some u64, .atom "0")],
          .ite (.atom s!"{z} < {n}")
            (.ofExpr (goCall (down sl.q first) (.ctor kName (some (kVariant a b i)) (#[x] ++ rs ++ #[srcV, .var z, .var n, empty, k]))))
            (.ofExpr rest)⟩
    let fuel := plans.foldl (fun n ps => ps.foldl (fun n (_, sl) => n + sl.size) n) 1
    -- `go`'s arms: convert a source value of member `a`.
    let mut goArms : Array RR.Arm := #[]
    for h : a in [:plans.size] do
      let some si := (← get).typeInfos[group[a]!.1]? | throwError "lean2rr: no type"
      let mut xArms : Array RR.Arm := #[]
      let mut structE : Option RR.Expr := none
      for h2 : b in [:plans[a].size] do
        let (arm, _) := plans[a][b]
        let e ← if arm.dl.isNone then pure unreachable else start fuel a b 0 (.var "x") #[] (.var "k")
        if si.shape == .struct then structE := some e
        else
          let nrel := (arm.sl.fields.filterMap id).size
          xArms := xArms.push { ty := group[a]!.1, ctor := some arm.sl.variant, binders := Array.replicate nrel none, body := .ofExpr e }
      let body : RR.Expr := match structE with
        | some e => e
        | none => .mtch (.var "x") xArms
      goArms := goArms.push { ty := mName, ctor := some s!"d{a}", binders := #[some "x"], body := .ofExpr body }
    -- `go`'s arms: return converted value `d` of member `q` to the frame
    -- below.
    for q in [:group.size] do
      let mut kArms : Array RR.Arm := #[]
      let mut covered := 0
      kArms := kArms.push { ty := kName, ctor := some "kdone", binders := #[],
                            body := .ofExpr (if q == 0 then .var "d" else unreachable) }
      covered := covered + 1
      for h : a in [:plans.size] do
        for h2 : b in [:plans[a].size] do
          let (_, slots) := plans[a][b]
          for h3 : i in [:slots.size] do
            let sl := slots[i]
            if sl.q != q then continue
            covered := covered + 1
            let rs := (List.range i).toArray.map fun j => s!"r{j}"
            let rsE := rs.map RR.Expr.var
            if !sl.arr then
              let e ← start fuel a b (i + 1) (.var "x") (rsE.push (.var "d")) (.var "k2")
              kArms := kArms.push { ty := kName, ctor := some (kVariant a b i),
                                    binders := #[some "x"] ++ rs.map some ++ #[some "k2"], body := .ofExpr e }
            else
              let some sr ← arrayRepr? sl.st | throwError "lean2rr: bad array type"
              let some dr ← arrayRepr? sl.dt | throwError "lean2rr: bad array type"
              let acc2 ← fresh "ca"
              let one ← fresh "c1"
              let i2 ← fresh "ci"
              let next := sr.load (sr.call "get" #[.var "src", .var i2])
              let again := goCall (down sl.q next)
                (.ctor kName (some (kVariant a b i)) (#[.var "x"] ++ rsE ++ #[.var "src", .var i2, .var "n", .var acc2, .var "k2"]))
              let done ← start fuel a b (i + 1) (.var "x") (rsE.push (.var acc2)) (.var "k2")
              let e : RR.Expr := .block ⟨#[(acc2, some sl.dt, dr.call "push" #[.var "acc", dr.store (.var "d")]),
                  (one, some u64, .atom "1"), (i2, some u64, .atom s!"idx + {one}")],
                .ite (.atom s!"{i2} < n") (.ofExpr again) (.ofExpr done)⟩
              kArms := kArms.push { ty := kName, ctor := some (kVariant a b i),
                                    binders := #[some "x"] ++ rs.map some ++ #[some "src", some "idx", some "n", some "acc", some "k2"],
                                    body := .ofExpr e }
      if covered < kVariants.size then
        kArms := kArms.push { ty := kName, ctor := none, binders := #[], body := .ofExpr unreachable }
      goArms := goArms.push { ty := mName, ctor := some s!"u{q}", binders := #[some "d"], body := .ofExpr (.mtch (.var "k") kArms) }
    modify fun s => { s with fns := s.fns.push (.fn go #[("m", mTy), ("k", kTy)] rootTy (.ofExpr (.mtch (.var "m") goArms))) }
    modify fun s => { s with fns := s.fns.push (.fn fname #[("x", srcTy 0)] rootTy
      (.ofExpr (goCall (down 0 (.var "x")) (.ctor kName (some "kdone") #[])))) }

  /-- The generated function converting generated type `sn` to `dn`: two
  instantiations of one inductive, or (through `unsafeCast`) two inductives
  that Lean represents alike (`convArms`). Cached. A conversion that
  recurses only through one field of each constructor (a list's tail) is a
  directly recursive function, which Reussir runs as a loop (tail recursion
  modulo constructors); any other recursion is an explicit-stack loop
  (`convMachine`). -/
  partial def structConv (sn dn : String) : LowerM String := do
    let entry := s!"l2r_conv_{sn}_{dn}"
    -- Shared records have an identity: the entry records the origin.
    let noted := (← isBoundaryTy (.named sn)) && (← isBoundaryTy (.named dn))
    let fname := if noted then entry ++ "_w" else entry
    let nested := (← get).convNested
    let result := if nested then fname else entry
    if (← get).fns.any (fun | .fn n .. => n == fname | _ => false) ||
       (← get).convsInProgress.contains fname then return result
    modify fun s => { s with convsInProgress := s.convsInProgress.insert fname, convNested := true }
    if noted then
      modify fun s => { s with fns := s.fns.push (.fn entry #[("x", .named sn)] (.named dn)
        (originWrap (.named sn) (.named dn) fname "x")) }
    let r ← structConvBody sn dn fname
    modify fun s => { s with convNested := nested }
    return if r then result else result

  /-- The body of `structConv`'s function `fname`; `true`. -/
  partial def structConvBody (sn dn fname : String) : LowerM Bool := do
    let some si := (← get).typeInfos[sn]? | throwError "lean2rr: no type {sn}"
    let group ← convGroup (sn, dn)
    let plans ← convSlots group
    let selfOnly := group.size == 1 && (plans[0]!.all fun (_, slots) =>
      slots.size ≤ 1 && slots.all fun sl => !sl.arr)
    if !selfOnly then
      convMachine fname group plans
      return true
    let mut arms := #[]
    let mut structBody : Option RR.Block := none
    for (arm, _) in plans[0]! do
      let e ← convBuild sn dn arm (.var "x") #[]
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
    modify fun s => { s with fns := s.fns.push (.fn fname #[("x", .named sn)] (.named dn) body) }
    return true
end

/-- The field type of `[value]` struct `info` (natively the struct is its
field). -/
def valueFieldTy? (info : TypeInfo) : Option RR.Ty := do
  guard info.value
  let c ← info.ctorOrder[0]?
  let l ← info.ctors.find? c
  l.posTys[0]?

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
5 %), for casts that hardly ever occur. -/
partial def boxCastable (vt t : RR.Ty) : LowerM Bool := do
  if vt == t then return true
  match vt, t with
  | .named a, .named b =>
    if [("u64", "f64"), ("f64", "u64"), ("u32", "f32"), ("f32", "u32")].contains (a, b) then return true
    let infos := (← get).typeInfos
    if let some ft := infos[a]?.bind valueFieldTy? then return ← boxCastable ft t
    if let some ft := infos[b]?.bind valueFieldTy? then return ← boxCastable vt ft
    if ← wordCastable a b (objects := true) then return true
    if b == "u64" && ((← isPureWord a) || (← wordCastable a "Nat" (objects := true))) then return true
    if infos.contains a && infos.contains b then return ← isomorphic a b
    return false
  | _, .named b => return (← isOtherObject vt) && ((← isPureWord b) || b == "u64")
  | _, _ => return false

/-- The conversion of a `Box` variant holding a value of type `vt` that
`boxCastable` accepts for an `unsafeCast` to `t` (an arm of `t`'s unboxing
function): `tryCoerce`, unless converting needs a function value at another
representation (a wrapper, §5.3). Every unboxing function would then match
every other type with function fields at the same native slots (the
dictionaries of uniform code), each wrapper adding arms to the application
functions of its type: the generated program grew by a fifth on monad
transformer towers. Such a cast stays unreachable (plan §10); the probe's
generated functions are dropped with it. -/
def boxCastConv (x : RR.Expr) (vt t : RR.Ty) : LowerM (Option RR.Expr) := do
  let saved ← get
  let nfn (st : LowerState) : Nat := st.fnVariants.fold (fun n _ vs => n + vs.size) 0
  let r ← match ← tryCoerce x vt t with
    | some r => pure (some r)
    | none => castFallback x vt t
  let after ← get
  if nfn after != nfn saved || after.fnConvs.size != saved.fnConvs.size ||
     after.fnUnboxTargets.size != saved.fnUnboxTargets.size then
    set saved
    return none
  return r

end LeanToReussir
