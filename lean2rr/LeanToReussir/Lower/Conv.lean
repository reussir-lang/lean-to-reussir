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

/-- `l2r_ctor_word_T(x)`: the index of a constructor without fields of
generated type `tn`, which natively is the boxed scalar of its index; a
value with fields is an object (its "word" an address): unreachable. -/
def ctorWordFn (tn : String) (info : TypeInfo) : LowerM String := do
  let name := s!"l2r_ctor_word_{tn}"
  unless (← get).fns.any (fun | .fn n .. => n == name | _ => false) do
    let u64 := RR.Ty.named "u64"
    let mut arms : Array RR.Arm := #[]
    for h : i in [:info.ctorOrder.size] do
      let some l := info.ctors.find? info.ctorOrder[i] | continue
      if l.fields.all Option.isNone then
        arms := arms.push { ty := tn, ctor := some l.variant, binders := #[], body := ⟨#[("i", some u64, .atom (toString i))], .var "i"⟩ }
    arms := arms.push { ty := tn, ctor := none, binders := #[], body := .ofExpr (.call "l2r_unreachable" #[u64] #[]) }
    modify fun s => { s with fns := s.fns.push (.fn name #[("x", .named tn)] u64 (.ofExpr (.mtch (.var "x") arms))) }
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

/-- The word `lean_unbox` gives natively for value `e` of Reussir type `n`
(`unsafeCast` to a scalar reads it): a `Nat`'s value (`lean_usize_of_nat`;
for a big one, natively an address, its low bits), an `Int`'s 32 bits
(`l2r_int_word`), the index of an enumeration or of a constructor without
fields, a fixed-width integer's value. `none` for other types. -/
def wordOf (e : RR.Expr) (n : String) : LowerM (Option RR.Expr) := do
  if n == "Nat" then return some (.call "lean_usize_of_nat" #[] #[e])
  if n == "Int" then return some (.call "l2r_int_word" #[] #[e])
  if let some w ← scalarWord e n then return some w
  if let some info := (← get).typeInfos[n]? then
    if !info.value && hasNullaryCtor info then return some (.call (← ctorWordFn n info) #[] #[e])
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

mutual
  /-- Convert `e` from representation `src` to `dst`. Besides `Box`
  conversions and closure wrappers, two instantiations of the same inductive
  are converted structurally: Lean's mono `cse` compares erased types, so it
  may merge e.g. `[] : List Shape` with `[] : List Nat`; such a merged value
  carries no data at the differing type parameter, so rebuilding it at the
  target type is always possible (an arm that would need an impossible
  element conversion is unreachable). -/
  partial def coerce (e : RR.Expr) (src dst : RR.Ty) : LowerM RR.Expr := do
    match ← tryCoerce e src dst with
    | some r => return r
    | none =>
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
      -- inductive that Lean represents alike: structurally.
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
      -- enumerations, constructors without fields.
      if let some w ← wordOf e sn then
        if let some r ← ofWord w dn then return some r
      vecCoerce e src dst
    | .app "LCell" #[.named sz], .app "LCell" #[.named dz] =>
      match ← lazyConv sz dz with
      | some f => return some (.call f #[] #[e])
      | none => return none
    | _, _ => vecCoerce e src dst

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
  to one with element storage `de` (cached). -/
  partial def vecConv (src dst : RR.Ty) (sr dr : ArrayRepr) : LowerM (Option String) := do
    if let some f := (← get).vecConvs[(src, dst)]? then return some f
    let f ← fresh "l2r_vconv_"
    modify fun s => { s with vecConvs := s.vecConvs.insert (src, dst) f }
    let x := sr.load (sr.call "get" #[.var "src", .var "i"])
    -- Elements that cannot be converted (`Array Nat` to `Array Int`) mean
    -- that the array is empty whenever this runs: an empty array that `cse`
    -- shared between two element types, or the array `Array.map` returns
    -- when it had nothing to map (Stage 3).
    let y ← match ← tryCoerce x sr.value dr.value with
      | some y => pure y
      | none => pure (.call "l2r_unreachable" #[dr.value] #[])
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
      .fn f #[("src", src)] dst entry] }
    return some f

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

  /-- The generated function converting instantiation `sn` to `dn` of the
  same inductive (cached). -/
  partial def structConv (sn dn : String) : LowerM String := do
    let fname := s!"l2r_conv_{sn}_{dn}"
    if (← get).fns.any (fun | .fn n .. => n == fname | _ => false) ||
       (← get).convsInProgress.contains fname then return fname
    modify fun s => { s with convsInProgress := s.convsInProgress.insert fname }
    let some si := (← get).typeInfos[sn]? | throwError "lean2rr: no type {sn}"
    let some di := (← get).typeInfos[dn]? | throwError "lean2rr: no type {dn}"
    let mut arms := #[]
    let mut structBody : Option RR.Block := none
    -- Constructors correspond by name (instantiations of one inductive) or
    -- by position (isomorphic inductives, through `unsafeCast`).
    let sameHead := (← nominalHead sn) == (← nominalHead dn)
    for h : ci in [:si.ctorOrder.size] do
      let ctor := si.ctorOrder[ci]
      let some sl := si.ctors.find? ctor | continue
      let dctor := if sameHead then ctor else di.ctorOrder[ci]?.getD ctor
      let some dl := di.ctors.find? dctor | continue
      let srcFields := sl.fields.filterMap id
      let dstFields := dl.fields.filterMap id
      let names ← srcFields.mapM fun _ => fresh "cf"
      let mut vals := #[]
      let mut possible := true
      if sameHead then
        -- Fields by Lean index. A field relevant in the target but not in
        -- the source (a proof-like type such as `PLift p` in one of the
        -- instantiations) was never inspected: its placeholder.
        let srcIdx := (List.range sl.fields.size).toArray.filter fun j => (sl.fields[j]?.join).isSome
        for h : j in [:dl.fields.size] do
          let some (_, dt) := dl.fields[j] | continue
          match sl.fields[j]?.join, srcIdx.idxOf? j with
          | some (_, st), some k =>
            match ← tryCoerce (.var names[k]!) st dt with
            | some v => vals := vals.push v
            | none => possible := false
          | _, _ => vals := vals.push (← zeroValue dt)
      else
        -- Another inductive (through `unsafeCast`): fields by native
        -- layout slot (`castFieldMap`).
        let srcIdx := (List.range sl.fields.size).toArray.filter fun j => (sl.fields[j]?.join).isSome
        match ← castFieldMap ctor dctor sl dl with
        | none => possible := false
        | some fm =>
          for h : j in [:dl.fields.size] do
            let some (_, dt) := dl.fields[j] | continue
            match fm[j]?.join with
            | some (some k) =>
              let some (_, st) := sl.fields[k]?.join | possible := false
              let some r := srcIdx.idxOf? k | possible := false
              match ← tryCoerce (.var names[r]!) st dt with
              | some v => vals := vals.push v
              | none => possible := false
            | _ => vals := vals.push (← zeroValue dt)
      -- Fields are bound from and placed at their record positions.
      let placedVals := dl.place vals
      let body : RR.Block := if possible then
          .ofExpr (match di.shape with
            | .struct => .ctor dn none placedVals
            | _ => .ctor dn (some dl.variant) placedVals)
        else .ofExpr (.call "l2r_unreachable" #[.named dn] #[])
      match si.shape with
      | .struct =>
        structBody := some ⟨(names.zip srcFields).map (fun (n, (p, t)) => (n, some t, RR.Expr.field (.var "x") p)), body.result⟩
      | _ =>
        let mut binders : Array (Option String) := Array.replicate srcFields.size none
        for (n, (p, _)) in names.zip srcFields do binders := binders.set! p (some n)
        arms := arms.push { ty := sn, ctor := some sl.variant, binders, body }
    let body := match structBody with
      | some b => b
      | none => .ofExpr (.mtch (.var "x") arms)
    modify fun s => { s with fns := s.fns.push (.fn fname #[("x", .named sn)] (.named dn) body) }
    return fname
end

end LeanToReussir
