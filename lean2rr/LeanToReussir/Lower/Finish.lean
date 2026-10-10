import LeanToReussir.Lower.Code

/-!
# Generated at the end

Functions whose bodies depend on everything the program lowered: the
`Box` → nominal, word and function-type converters (`finishUnboxFns`), the
application and conversion functions of function values
(`finishFnValues`), and the enums of function types (`fnTypeItems`).
-/

namespace LeanToReussir
open Lean Compiler LCNF

/-- Can Reussir types `a` and `b` represent the same Lean type? `Box` stands
for any type; function types compare their parts; any other type stands
only for itself (one type per inductive, one per builtin generic type). -/
partial def reprCompatible (a b : RR.Ty) : LowerM Bool := do
  if a == b || a == RR.Ty.box || b == RR.Ty.box then return true
  match a, b with
  | .fn a1 b1, .fn a2 b2 =>
    -- A phantom domain (rule 4) is an erased Lean domain, as a unit one;
    -- `Box` stands for any type.
    let unitLike (d : RR.Ty) : Bool := d == RR.Ty.phantom || d == .unit || d == RR.Ty.box
    if a1 == RR.Ty.phantom || a2 == RR.Ty.phantom then
      return (unitLike a1 && unitLike a2) && (← reprCompatible b1 b2)
    return (← reprCompatible a1 a2) && (← reprCompatible b1 b2)
  | _, _ => return false

/-- Generate the body of the `Box → t` converter `fname` (the box API's
`boxDispatch`). It matches the pointer payloads that can hold a value of
the target's Lean type (with `conv-liveness`, that live code builds) and
converts them: for a nominal or word type, its own payload only; for a
function type, any representation of it (wrapped). In a program that
casts (`programCasts`), also the payloads of types Lean represents alike
(`boxCastable`). An immediate is read at `t` as the inline unboxing of a
program that casts reads it (`boxUnbox` with `native`: a word as native
Lean reads it, an index, `box(0)` as `t`'s zero; such a function exists
only in a program that casts, `unboxFn`); at a
function type it is `box(0)` or a function payload's nullary variant by
index (`l2r_any_of_fn`), converted. Other payloads are unreachable. -/
def genUnbox (fname : String) (t : RR.Ty) : LowerM Unit := do
  let u64 := RR.Ty.named "u64"
  let mut arms : Array BoxArm := #[]
  -- The function payloads accepted at a function type, for their typed
  -- immediates.
  let mut fnPayloads : Array (Nat × RR.Ty) := #[]
  for (vt, vname) in ← boxPayloads do
    if ← liveSkipBox vname then continue
    let some (n, _, _) ← boxPointer? vt | continue
    let accept ← match vt with
      | .fn .. =>
        -- A function value of any compatible representation (wrapped).
        pure (t matches .fn .. && (← reprCompatible vt t))
      | _ => pure (vt == t)
    let cast := !accept && (← boxCastable vt t)
    if !accept && !cast then continue
    let x ← fresh "bx"
    -- A cast that `tryCoerce` does not convert: `castFallback` (an object
    -- read as a word); a payload neither converts gets no arm.
    let body ← match ← tryCoerce (.var x) vt t with
      | some b => pure (some b)
      | none => if cast then castFallback (.var x) vt t else pure none
    -- A cast whose conversion never returns a value (`convCall`): no arm
    -- (the unreachable arm panics alike).
    let body := body.filter (!deadConvExpr? ·)
    if let some body := body then
      arms := arms.push { payload := vt, binder := some x, body := .ofExpr body }
      if accept && vt matches .fn .. then fnPayloads := fnPayloads.push (n, vt)
  let unreach (bx : RR.Expr) : LowerM RR.Block := return ⟨#[boxSink bx], .call "l2r_unreachable" #[t] #[]⟩
  let imm : String → RR.Expr → LowerM RR.Block := fun w bx => do
    match t with
    | .fn .. =>
      let v ← fresh "fv"
      let z ← fresh "fz"
      let n ← fresh "fn"
      let i ← fresh "fi"
      let sh ← fresh "fs"
      let mask ← fresh "fk"
      let mut fnArms : Array RR.Arm := #[]
      for (num, st) in fnPayloads do
        let s ← fresh "fsv"
        let conv ← coerce (.var s) st t
        fnArms := fnArms.push (RR.Arm.lit num
          ⟨#[(s, some st, .call (← boxFnOfIndex st) #[] #[.var i])], conv⟩)
      fnArms := fnArms.push { ty := "", ctor := none, binders := #[], body := .ofExpr (.call "l2r_unreachable" #[t] #[]) }
      let typed : RR.Block := ⟨#[(sh, some u64, .atom "32"), (n, some u64, .atom s!"{v} >> {sh}"),
          (mask, some u64, .atom "4294967295"), (i, some u64, .atom s!"{v} & {mask}")],
        .mtch (.var n) fnArms⟩
      return ⟨#[(v, some u64, .call "l2r_any_raw_imm" #[] #[.var w]), (z, some u64, .atom "0")],
        .ite (.atom s!"{v} == {z}") (.ofExpr (← zeroValue t)) typed⟩
    -- An immediate is read as natively (`boxUnbox`'s `native`): this
    -- function exists only in a program that casts.
    | _ => return .ofExpr (← unboxMatch bx t (native := true))
  let m ← boxDispatch (.var "b") arms imm unreach
  let item := RR.Item.fn fname #[("b", RR.Ty.box)] t (.ofExpr m)
  replaceFn fname item

/-- Generate the bodies of all `Box → nominal` (or word) and `Box →
function` converters (`genUnbox`). Generating a conversion may add `Box`
variants (for fields), so this iterates until the variant set is stable. -/
partial def finishUnboxFns : LowerM Unit := do
  let mut done : Std.HashMap String Nat := {}
  repeat
    let nvars ← getPart (·.boxVariants.size)
    let nominal ← getPart (·.unboxTargets.map fun t => (s!"l2r_unbox_{t}", RR.Ty.named t))
    let fns ← getPart (·.fnUnboxTargets.map fun t => (s!"l2r_unbox_fn_{t.enc}", t))
    let pending := (nominal ++ fns).filter fun (f, _) => done.getD f 0 != nvars + 1
    if pending.isEmpty then break
    for (fname, t) in pending do
      genUnbox fname t
      -- Record the variant count this body was generated against; a later
      -- growth of the variant set makes it pending again.
      done := done.insert fname (nvars + 1)

/-- Target `tg` called with all the arguments it takes (`args`, rule 4a).
An extern, constructor or stream primitive is called with Lean's
arguments, placeholders where it takes none (as for `◾` in a direct call:
`lowerExternCall` drops them, or passes them where a parameter declared at
a type variable is instantiated with an erased type). -/
def targetCall (tg : FnTarget) (args : Array RR.Expr) : LowerM RR.Expr := do
  let full : Array RR.Expr := Id.run do
    if tg.keep.isEmpty then return args
    let mut out := #[]
    let mut k := 0
    for i in [:tg.params.size] do
      if tg.takes i then
        out := out.push (args[k]?.getD .unitVal)
        k := k + 1
      else out := out.push .unitVal
    return out
  match tg.call with
  | .code fn => return .call fn #[] args
  | .extern orig typeArgs params ret => lowerExternCall orig typeArgs params ret full
  | .ctor c fullRt => ctorBuild c fullRt full
  | .stream fd i streamTy => streamFieldCall fd i streamTy full

/-- The number of leading phantom domains of function type `t`. -/
def leadPhantoms : RR.Ty → Nat
  | .fn d c => if d == RR.Ty.phantom then leadPhantoms c + 1 else 0
  | _ => 0

/-- Function type `t` without its leading phantom domains. -/
def stripLeadPhantoms : RR.Ty → RR.Ty
  | t@(.fn d c) => if d == RR.Ty.phantom then stripLeadPhantoms c else t
  | t => t

/-- Whether function type `t` has a domain that is not phantom in its first
`k` Lean positions. -/
def runtimeDomWithin : RR.Ty → Nat → Bool
  | _, 0 => false
  | .fn d c, k + 1 => d != RR.Ty.phantom || runtimeDomWithin c k
  | _, _ => false

/-- Generate `l2r_ap<j>_T`, applying a function value of type `t` (a
run-time type, `RR.Ty.rt`) to `j` arguments (see "Function values"): a
match on the variant (with `conv-liveness`, on the variants live code
builds, besides `z` and `raw`).

Rule 4: the arms match the arguments with the variant's Lean positions.
A partial application `p<j>` walks its target's type from Lean position
`j`: an argument at a parameter the target does not take is dropped (a
unit the type keeps for other values), a phantom domain takes no argument
(the target gets a placeholder if it takes that parameter). A wrapped
value `w<S>` takes its own type's Lean positions: `◾` at its phantom
domains. -/
def genApply (t : RR.Ty) (j : Nat) : LowerM Unit := do
  let t := t.rt
  let (doms, _) := fnChain t
  let resJ := fnResult t j
  let tn := RR.fnTypeName t
  let as := (List.range j).toArray.map fun i => s!"l2ra{i}"
  let argsFrom (k : Nat) : Array (RR.Expr × RR.Ty) :=
    (List.range (j - k)).toArray.map fun i => (RR.Expr.var as[k + i]!, doms[k + i]!)
  -- The value `e` of the first `k` arguments (at `fnResult t k`), applied to
  -- the others.
  -- `rest` (and so the `raw` arm) and the sink arms below take the arguments
  -- at `doms`, the run-time types. That is correct only because they never
  -- convert an argument: each one is at its own parameter type here, so
  -- `applyExprs`'s conversions are the identity and `l2r_sink` releases at
  -- the declared type. Do not add a conversion from `doms[i]` there: a
  -- function type in `doms` has lost its phantom domains (see the `.part`
  -- arm). The `.part` and `.wrap` arms take each argument at the variant's
  -- own domain.
  let rest (e : RR.Expr) (k : Nat) : LowerM RR.Expr := do
    let (r, rt) ← applyExprs e (fnResult t k) (argsFrom k)
    coerce r rt resJ
  let mut arms : Array RR.Arm :=
    #[{ ty := tn, ctor := some "z", binders := #[], body := .ofExpr (← zeroValue resJ) }]
  let rawBody ← rest (.apply (.var "l2rc") (.var as[0]!)) 1
  arms := arms.push { ty := tn, ctor := some "raw", binders := #[some "l2rc"], body := .ofExpr rawBody }
  let mut skipped := false
  for v in (← getPart (·.fnVariants)).getD t #[] do
    if ← liveSkipFn t v then
      skipped := true
      continue
    let (binders, body) ← match v with
      | .wrap src dst =>
        -- The Lean arguments of `dst`'s positions up to the last argument:
        -- `◾` at its phantom domains.
        let mut largs : Array LArg := #[]
        let mut dt := dst
        let mut r := 0
        while r < j do
          let .fn d c := dt | break
          if d == RR.Ty.phantom then largs := largs.push .erased
          else
            -- At `dst`'s own domain `d`, not at `doms[r]` (`d.rt`, the
            -- same Reussir type): a function type in `d` keeps its phantom
            -- domains, which a conversion compares (see the `.part` arm).
            largs := largs.push (.val (.var as[r]!) d)
            r := r + 1
          dt := c
        -- `g` takes the Lean arguments of its own chain (`src`'s domains,
        -- up to a `Box` result); the value is then converted to `dst` at
        -- that position (the type that names its phantom domains), and
        -- applied to the other arguments at `dst`'s type.
        let k := min (fnChain src).1.size largs.size
        let (e, et) ← applyLean (.var "l2rg") src (largs.extract 0 k)
        let rk := ((largs.extract 0 k).filter (· matches .val ..)).size
        let e ← coerce e et (fnResult dst k)
        pure (#[some "l2rg"], ← if rk < j then rest e rk else pure e)
      | .part id pj =>
        let some tg := (← get).fnTargets[id]? | throwError "lean2rr: unknown function target {id}"
        let n := tg.params.size
        let m := tg.captures pj
        let captured := (List.range m).toArray.map fun i => RR.Expr.var s!"l2rx{i}"
        -- The target's Lean positions from `pj`, along its type.
        let mut ty := partTy tg pj
        let mut k := pj
        let mut r := 0
        let mut cargs := #[]
        while k < n do
          -- Out of arguments where the target still has a domain that is
          -- not phantom before its last: a partial application.
          if r == j && runtimeDomWithin ty (n - k) then break
          let .fn d c := ty | break
          if d == RR.Ty.phantom then
            if tg.takes k then cargs := cargs.push (← zeroValue tg.params[k]!)
          else
            if r == j then break
            -- The argument is a value of the target's domain `d` (the type
            -- of this partial application at Lean position `k`), held at
            -- `doms[r]`, which is `d.rt`: the same Reussir type, but a
            -- function type there has lost its phantom domains, and
            -- converting from it would wrap the value as one whose `◾` is
            -- an argument (a `(α : Type) → α → α` parameter got `box(0)`
            -- for its value: test `RtApplyPhantomParam`).
            if tg.takes k then cargs := cargs.push (← coerce (.var as[r]!) d tg.params[k]!)
            r := r + 1
          ty := c
          k := k + 1
        let body ← if k < n then do
            -- Fewer arguments than the target needs: a partial application
            -- (its type's run-time type is `resJ`).
            let (pv, _) ← partValue tg k (captured ++ cargs)
            pure pv
          else do
            let call ← targetCall tg (captured ++ cargs)
            -- The other arguments to the result, at its run-time type.
            let e ← coerce call tg.ret ty
            if r < j then rest e r else pure e
        pure ((List.range m).toArray.map fun i => some s!"l2rx{i}", body)
    arms := arms.push { ty := tn, ctor := some (fnVariantName v), binders, body := .ofExpr body }
  -- `conv-liveness`: the variants no live code builds are unreachable. rrc
  -- copies the wildcard into each of them, so the arguments are released
  -- out of line (`l2r_sink`, as `sinkWildcardHeld`), not each in line, a
  -- match over its type's variants, in every copy.
  if skipped then
    let mut sinks := #[]
    for (a, aty) in as.zip doms do
      if aty matches .named "u8" | .named "u16" | .named "u32" | .named "u64" | .named "i8" | .named "i16"
          | .named "i32" | .named "i64" | .named "f32" | .named "f64" | .named "bool" | .named "L2RUnit" then continue
      sinks := sinks.push (s!"us{a}", some (RR.Ty.named "u64"), RR.Expr.call "l2r_sink" #[aty] #[.var a])
    arms := arms.push { ty := tn, ctor := none, binders := #[], body := ⟨sinks, .call "l2r_unreachable" #[resJ] #[]⟩ }
  let name := applyFnName t j
  let params := #[("l2rf", t)] ++ as.zip (doms.extract 0 j)
  let item := RR.Item.fn name params resJ (.ofExpr (.mtch (.var "l2rf") arms))
  replaceFn name item

/-- Generate `l2r_fconv_S_T` (see `fnConvFn`). A value that is a wrapped
value `g` of a representation `R` (`w<R>(g)`) is converted from `R`
directly: `g` itself when `R` is `T`, otherwise `l2r_fconv_R_T(g)` (generated
on demand). So a function value that travels through several
representations (a reference read at `Nat → Nat`, `Nat → Box` and
`Box → Box` in a loop) stays one wrapper deep, and coming back to its own
representation gives the value itself. Other values are wrapped
(`w<S>`). -/
def genFnConv (src dst : RR.Ty) : LowerM Unit := do
  -- `g`, wrapped from `r` as a value of `d'`, at `dst`: `d'` and `src` are
  -- one Lean type but for leading phantom domains (`◾`s applied already,
  -- or to come); those `◾`s are no arguments at run time when `r` (or
  -- `dst`) has phantom domains there too. Otherwise `none` (wrapped).
  let unwrapAs (r d' : RR.Ty) : LowerM (Option RR.Expr) := do
    if d' == src then return ← tryCoerce (.var "l2rg") r dst
    if stripLeadPhantoms d' != stripLeadPhantoms src then return none
    let a := leadPhantoms d'
    let b := leadPhantoms src
    if a ≥ b then
      if leadPhantoms r < a - b then return none
      tryCoerce (.var "l2rg") (fnResult r (a - b)) dst
    else
      if leadPhantoms dst < b - a then return none
      tryCoerce (.var "l2rg") r (fnResult dst (b - a))
  let name := s!"l2r_fconv_{src.enc}_{dst.enc}"
  let wrapped := RR.Expr.ctor (RR.fnTypeName dst) (some (fnVariantName (.wrap src dst))) #[.var "l2rf"]
  let mut arms : Array RR.Arm := #[]
  for v in (← getPart (·.fnVariants)).getD src.rt #[] do
    -- A value wrapped as a value of `src`, or of a type that differs from
    -- `src` only in leading phantom domains (the enum is shared by the
    -- types with the same run-time type; an application function returns
    -- a value at its type after the arguments, before the phantom domains
    -- that follow, `genApply`).
    let .wrap r d' := v | continue
    if ← liveSkipFn src v then continue
    let some e ← unwrapAs r d' | continue
    arms := arms.push { ty := RR.fnTypeName src, ctor := some (fnVariantName v), binders := #[some "l2rg"], body := .ofExpr e }
  let body : RR.Expr := if arms.isEmpty then wrapped
    else .mtch (.var "l2rf") (arms.push { ty := RR.fnTypeName src, ctor := none, binders := #[], body := .ofExpr wrapped })
  let item := RR.Item.fn name #[("l2rf", src)] dst (.ofExpr body)
  replaceFn name item

/-- Generate the application functions requested so far, again for those
whose type gained variants. Whether anything was generated. -/
partial def finishFnValues : LowerM Bool := do
  let mut any := false
  repeat
    let mut progress := false
    for (src, dst) in (← getPart (·.fnConvs)) do
      let nv := ((← get).fnVariants.getD src.rt #[]).size
      if (← get).fnConvDone[(src, dst)]? == some nv then continue
      genFnConv src dst
      modify fun s => { s with fnConvDone := s.fnConvDone.insert (src, dst) nv }
      progress := true
    for (t, j) in (← getPart (·.fnApplies)) do
      let nv := ((← get).fnVariants.getD t #[]).size
      if (← get).fnApplyDone[(t, j)]? == some nv then continue
      genApply t j
      modify fun s => { s with fnApplyDone := s.fnApplyDone.insert (t, j) nv }
      progress := true
    if !progress then break
    any := true
  return any

/-- `finishUnboxFns` and `finishFnValues` with `conv-liveness`: the helpers
live code reaches, with arms for the variants live code builds, generated
until liveness (`liveFollow`) finds nothing new for them: a helper whose
variants grew since its body was generated (`liveVersion`) is generated
again, and the bodies generated are looked at by the next scan. -/
partial def finishLive : LowerM Unit := do
  repeat
    liveFollow
    let mut gen := false
    for (name, h) in ← getPart (·.live.helpers) do
      let ver ← liveVersion h
      if (← getPart (·.live.done[name]?)) == some ver then continue
      match h with
      | .unbox t => genUnbox name t
      | .apply t j => genApply t j
      | .fconv src dst => genFnConv src dst
      modify fun s => { s with live := { s.live with done := s.live.done.insert name ver } }
      gen := true
    if !gen then break

/-- The generated functions that rrc's MLIR inliner is to leave out of
line (`#[transform_anchor]`, see `Emit/Program`): the conversions between
representations of a function type (`l2r_fconv_S_T`), the unboxing
functions (`l2r_unbox_…`: to a nominal or word type, a function type),
the application functions of a function type with wrapped values of other
representations (their `w<S>` arms apply the wrapped value at `S`), and
the application functions of the function types of uniform code (types
that mention `Box`), whose arms call the targets of the uniform code.

These functions call each other: an unboxing function to a function type
converts what a `Box` holds from every representation of that type (in a
program that casts, an unboxing function converts the types a cast reads
too), a conversion of a
function value converts from the wrapped representation, and the
application of a wrapped value applies it at its own representation.
Polymorphic recursion through monad transformers makes hundreds of
representations of a few Lean types, and with them a call graph of small
mutually recursive functions. With them inlinable, rrc's build time and
memory grow far faster than the program (superlinearly in the number of
representations; the mechanism inside rrc is not narrowed down, and the
growth was not measured as exponential: an 8-line `StateT` tower used at
`IO` did not build within 30 minutes or 15 GB;
reussir-bugs/20-statet-tower.md); with the application functions of uniform
types inlinable, four towers in one program (`Cn3PolyScalar`) still took
4.5 GB, 2 GB without. Out of line, they cost a call each (LLVM, which runs
after Reussir's passes, still inlines them where it pays): the unboxing of
statically unknown values and the conversions are slow paths anyway, and
wrapped applications and function values of uniform types are rare outside
such programs. -/
def anchoredFns : LowerM (Std.HashSet String) := do
  let st ← get
  let wraps (t : RR.Ty) : Bool := (st.fnVariants.getD t.rt #[]).any (· matches .wrap ..)
  let mut out : Std.HashSet String := {}
  for (src, dst) in st.fnConvs do out := out.insert s!"l2r_fconv_{src.enc}_{dst.enc}"
  for t in st.fnUnboxTargets do out := out.insert s!"l2r_unbox_fn_{t.enc}"
  for t in st.unboxTargets do out := out.insert s!"l2r_unbox_{t}"
  -- A once-cell's computation runs once (`cafAccessor`), and so does the
  -- literal cache's slow path for each literal (`strLitCached`).
  for f in st.cafInits do out := out.insert f
  out := out.insert "l2r_str_lit_fill"
  for (t, j) in st.fnApplies do
    if wraps t || (t.subterms).contains RR.Ty.box then out := out.insert (applyFnName t j)
  return out

/-- Whether a value of type `t` can hold a task, with the final variants
of function types and `Box` (`typeHoldsTask`). -/
def holdsTask (t : RR.Ty) : LowerM Bool := typeHoldsTask t (final := true)

/-- The work list of the walks of constants for tasks (`genPersist`). -/
def persistListName : String := "L2RPersistW"

/-- Whether values of type `t` are cells that a walk for tasks marks
persistent (`l2r_persist_mark`): records, arrays, thunks and tasks,
function values, references, promises (shared, with an address and a
count). Other values (`[value]` structs, `Tuple`s) are looked into each
time they are reached; a `Box` is looked into where it is met, and its
payload is marked at the payload's own type, or, when that type cannot
hold a task, through the box (`l2r_persist_box`). -/
def persistCell (t : RR.Ty) : LowerM Bool := do
  match t with
  | .app "LCell" _ | .app "RVec" _ | .fn .. => return true
  | .named n =>
    if n == boxName then return false
    if n == "LPromise" then return true
    if let some info := (← get).typeInfos[n]? then return info.shape != .enumLike && !info.value
    if ← isRefType t then return true
    -- An `ElemBox` is a shared struct, a `Tuple` a `[value]` one.
    return (← elemBoxOf? t).isSome
  | _ => return false

/-- The walk of a constant's value for tasks (`persistCall`), as native
`lean_mark_persistent`: a loop (`l2r_persist_walk(w)`) over a work list
`w` (`L2RPersistW`) of the values still to look at. It marks each cell it
visits persistent (`l2r_persist_mark`, `leanrt::persist`: the cell's count
goes up by 2^30), and does not look into a cell that is persistent already,
marked by this walk or an earlier one, as native's walk skips an object
whose count is 0. So a value deep through any of its fields is walked at a
bounded depth, and a value whose cells are shared (a DAG) in time linear in
its number of cells; and a later walk does not read again what a reference,
a thunk, a task or a promise that an earlier walk reached holds now. The
work list has a variant `w<T>(value, rest)` per type that can hold a task
(not `Box`), and `a<T>(array, index, rest)` per such array type (its
elements below `index` still to look at). `genPersist t` generates the
expansion of a value of type `t`, `l2r_persist_x_T(v, rest)`, which returns
the work list with what `v` holds pushed on `rest` (a task: waits for it,
then its value; a promise: its task; a reference: its value; a thunk: its
computation or its value, not forcing it), and those of the types it
reaches; it returns `t`'s variant, `none` for a type that cannot hold a
task (its values are not looked at). A `Box` is never pushed: where one is
met, `l2r_persist_x_LAny(b, rest)` pushes its payload at the payload's type
if that type can hold a task; otherwise it marks the payload persistent
without looking into it (`l2r_persist_box`: a persistent cell keeps all it
holds, a file handle stays open); an immediate is nothing. The last value
pushed is visited next: when it has `t`'s own type (a list's tail), the
expansion calls itself on it instead (a loop), and an array of boxes is
walked in a loop that pushes only the payloads that can hold a task, so a
`List Nat` or `Array Nat` makes no work-list cell. The order of the walk is
native's: Lean pushes an object's fields (a closure's captured values, an
array's elements) in order on its stack and pops the last one first, so
the fields are pushed in Lean's order, the last on top, and an array is
looked at from its last element down. A cell is marked when it is reached,
before the walk waits for it or looks into it, as natively (a payload that
cannot hold a task is marked where its box is met). One pass: natively
waiting only blocks, and the workers run the term's tasks in queue order;
lean-runtime's `wait` does the same. `gen` collects the variants, the
walk's arms and the expansions generated. -/
structure PersistGen where
  variants : Array (String × Array RR.Ty) := #[]
  arms : Array RR.Arm := #[]
  done : Std.HashSet String := {}

/-- The expansion of a value of type `t` by the walk for tasks
(`genPersist`). -/
def persistExpName (t : RR.Ty) : String := s!"l2r_persist_x_{t.enc}"

partial def genPersist (t : RR.Ty) (gen : IO.Ref PersistGen) : LowerM (Option String) := do
  unless ← holdsTask t do return none
  let wv := s!"w{t.enc}"
  let name := persistExpName t
  if (← gen.get).done.contains name then return some wv
  gen.modify fun g => { g with done := g.done.insert name }
  let isBox := t == RR.Ty.box
  let u64 := RR.Ty.named "u64"
  let wTy := RR.Ty.named persistListName
  unless isBox do
    let walkArm : RR.Arm := {
      ty := persistListName, ctor := some wv, binders := #[some "v", some "k"]
      body := .ofExpr (.call "l2r_persist_walk" #[] #[.call name #[] #[.var "v", .var "k"]]) }
    gen.modify fun g => { g with variants := g.variants.push (wv, #[t, wTy]), arms := g.arms.push walkArm }
  -- Nothing pushed: the work list as it is.
  let unchanged : RR.Block := .ofExpr (.var "k")
  -- Push `x : xt` on the work list `e`, if `xt` can hold a task: a box is
  -- looked into at once (`l2r_persist_x_LAny`), anything else pushed.
  let push (x : String) (xt : RR.Ty) (e : RR.Expr) : LowerM (Option RR.Expr) := do
    let some v ← genPersist xt gen | return none
    if xt == RR.Ty.box then return some (.call (persistExpName xt) #[] #[.var x, e])
    return some (.ctor persistListName (some v) #[.var x, e])
  -- Push each of the variables `xs` (those whose type can hold a task) on
  -- the work list `k`, in order: the last on top. (A value on the work list
  -- is held by it; once visited, a cell is persistent, never freed.) The
  -- last one, visited next, is not pushed when it has `t`'s own type: the
  -- expansion calls itself on it, a tail call (a loop).
  let each (xs : Array (String × RR.Ty)) (k : RR.Expr := .var "k") : LowerM RR.Block := do
    let pushed ← xs.filterM fun (_, xt) => holdsTask xt
    let mut e := k
    for i in [:pushed.size] do
      let (x, xt) := pushed[i]!
      if i + 1 == pushed.size && xt == t && !isBox then
        e := .call name #[] #[.var x, e]
      else if let some e' ← push x xt e then
        e := e'
    return .ofExpr e
  -- An arm binding `xs` (at record positions) and pushing them, in the
  -- order `order` if given (Lean's field order).
  let arm (ty : String) (ctor : String) (xs : Array (Option (String × RR.Ty)))
      (order : Option (Array (String × RR.Ty)) := none) : LowerM RR.Arm := do
    let body ← each (order.getD (xs.filterMap id))
    return { ty, ctor := some ctor, binders := xs.map (·.map (·.1)), body }
  -- A constructor's relevant fields in Lean's order, named by record
  -- position (`f<i>`).
  let leanOrder (l : CtorLayout) : Array (String × RR.Ty) :=
    l.fields.filterMap fun f => f.map fun (i, ft) => (s!"f{i}", ft)
  -- A cell persistent already is not looked into again; otherwise it is
  -- marked now, then looked into.
  let marked (body : RR.Block) : RR.Block :=
    .ofExpr (.ite (.call "l2r_persist_mark" #[t] #[.var "v"]) unchanged body)
  -- A box `b` met by the walk: an arm per payload type that can hold a
  -- task (`onTask` with the payload bound to `x`), and for an immediate
  -- and any other payload `onDone` after the payload is marked persistent
  -- (`l2r_persist_box`; nothing for an immediate).
  let boxCases (b : RR.Expr) (onTask : RR.Ty → LowerM RR.Block) (onDone : RR.Block) : LowerM RR.Expr := do
    let mut arms : Array BoxArm := #[]
    for (vt, _) in ← boxPayloads do
      if (← boxPointer? vt).isNone then continue
      unless ← holdsTask vt do continue
      arms := arms.push { payload := vt, binder := some "x", body := ← onTask vt }
    let imm (_ : String) (bx : RR.Expr) : LowerM RR.Block := return ⟨#[boxSink bx] ++ onDone.lets, onDone.result⟩
    let other (bx : RR.Expr) : LowerM RR.Block :=
      return ⟨#[("pb", some u64, .call "l2r_persist_box" #[] #[bx])] ++ onDone.lets, onDone.result⟩
    boxDispatch b arms imm other
  let body : RR.Block ← match t with
    | .app "LCell" #[.named z] =>
      let some (_, task) ← lazyOf? t | pure unchanged
      let vt := RR.Ty.box
      if task then
        -- A task: wait for it, then its value.
        let get ← lazyGetFn z
        let rest ← each #[("x", vt)]
        let wait : RR.Block := ⟨#[("x", some vt, .call get #[] #[.var "v"])] ++ rest.lets, rest.result⟩
        -- A placeholder's never-forced cell (`pending` with the function
        -- value `z`, `zeroTry`) is not a task: natively it is `box(0)`,
        -- which the walk skips (and does not mark). (A promise's cell is
        -- `pending` with a closure of its own.)
        let zt := RR.Ty.named z
        let ft := RR.fnTypeName (.fn .unit vt)
        let ph := s!"l2r_persist_ph_{t.enc}"
        let falseB : RR.Block := .ofExpr (.atom "false")
        let phItem := RR.Item.fn ph #[("c", t)] .bool (.ofExpr (.mtch (.call "l2r_lcell_get" #[zt] #[.var "c"]) #[
          { ty := z, ctor := some "pending", binders := #[some "f"],
            body := .ofExpr (.mtch (.var "f") #[
              { ty := ft, ctor := some "z", binders := #[], body := .ofExpr (.atom "true") },
              { ty := ft, ctor := none, binders := #[], body := falseB }]) },
          { ty := z, ctor := none, binders := #[], body := falseB }]))
        modify fun s => { s with fns := s.fns.push phItem }
        pure (.ofExpr (.ite (.call ph #[] #[.var "v"]) unchanged (marked wait)))
      else
        -- A thunk: its computation or its value, without forcing it.
        let ft := RR.Ty.fn .unit vt
        let arms := #[
          ← arm z "pending" #[some ("f", ft)],
          ← arm z "done" #[some ("x", vt)],
          { ty := z, ctor := none, binders := #[], body := unchanged }]
        pure (marked (.ofExpr (.mtch (.call "l2r_lcell_get" #[.named z] #[.var "v"]) arms)))
    | .app "RVec" #[_] =>
      let some ae := arrayElem? t | pure unchanged
      -- `a<T>(v, i, k)`: the elements below `i`, from the last one down.
      let avar := s!"a{t.enc}"
      let step := s!"l2r_persist_a_{t.enc}"
      let stepArm : RR.Arm := {
        ty := persistListName, ctor := some avar, binders := #[some "v", some "i", some "k"]
        body := .ofExpr (.call "l2r_persist_walk" #[] #[
          .call step #[] #[.var "v", .var "i", .var "k"]]) }
      gen.modify fun g => { g with variants := g.variants.push (avar, #[t, u64, wTy]), arms := g.arms.push stepArm }
      let below : RR.Expr := .ctor persistListName (some avar) #[.var "v", .var "j", .var "k"]
      let next : RR.Block ← if ae == RR.Ty.box then
          -- Boxes: an element whose payload can hold a task is pushed on
          -- the elements below it; any other is marked or skipped, and the
          -- loop goes on with the element below (a tail call).
          let again : RR.Block := .ofExpr (.call step #[] #[.var "v", .var "j", .var "k"])
          let onTask (vt : RR.Ty) : LowerM RR.Block := do
            let some w ← genPersist vt gen | return again
            return .ofExpr (.ctor persistListName (some w) #[.var "x", below])
          let dispatch ← boxCases (.var "x") onTask again
          pure ⟨#[("one", some u64, .atom "1"), ("j", some u64, .atom "i - one"),
            ("x", some ae, arrayCall ae "get" #[.var "v", .var "j"])], dispatch⟩
        else
          let rest ← each #[("x", ae)] (.var "k2")
          pure ⟨#[("one", some u64, .atom "1"), ("j", some u64, .atom "i - one"),
            ("x", some ae, arrayCall ae "get" #[.var "v", .var "j"]),
            ("k2", some wTy, below)] ++ rest.lets, rest.result⟩
      let stepItem := RR.Item.fn step #[("v", t), ("i", u64), ("k", wTy)] wTy
        ⟨#[("z", some u64, .atom "0")], .ite (.atom "z < i") next unchanged⟩
      modify fun s => { s with fns := s.fns.push stepItem }
      pure (marked ⟨#[("n", some u64, arrayCall ae "size" #[.var "v"])],
        .call step #[] #[.var "v", .var "n", .var "k"]⟩)
    | .fn .. =>
      -- A function value: the values it captures (a Reussir closure's
      -- cannot be looked at).
      let tn := RR.fnTypeName t
      let mut arms : Array RR.Arm := #[]
      for v in (← getPart (·.fnVariants)).getD t.rt #[] do
        let fs ← fnVariantFields v
        arms := arms.push (← arm tn (fnVariantName v) ((List.range fs.size).toArray.map fun i => some (s!"c{i}", fs[i]!)))
      arms := arms.push { ty := tn, ctor := none, binders := #[], body := unchanged }
      pure (marked (.ofExpr (.mtch (.var "v") arms)))
    | .named n =>
      if isBox then
        -- A box: its payload, pushed at its type when that can hold a task;
        -- any other payload marked persistent (it keeps all it holds); an
        -- immediate holds nothing.
        let onTask (vt : RR.Ty) : LowerM RR.Block := do
          let some w ← genPersist vt gen | return unchanged
          return .ofExpr (.ctor persistListName (some w) #[.var "x", .var "k"])
        pure (.ofExpr (← boxCases (.var "v") onTask unchanged))
      else if n == "LPromise" then
        -- A promise: its task (`Promise.result?`, `l2r_promise_cell`), as
        -- native Lean pushes the promise's `m_result`. The task's arm
        -- waits for it, until the promise is resolved, then walks its
        -- value (an `Option`).
        let z ← lazyState true
        let ct := RR.Ty.app "LCell" #[.named z]
        let rest ← each #[("c", ct)]
        pure (marked ⟨#[("c", some ct, .call "l2r_promise_cell" #[.named z] #[.var "v"])] ++ rest.lets, rest.result⟩)
      else if let some info := (← get).typeInfos[n]? then
        if info.shape == .struct then
          let some l := info.ctors.find? info.ctorOrder[0]! | pure unchanged
          let tys := l.posTys
          let xs := (List.range tys.size).toArray.map fun i => (s!"f{i}", tys[i]!)
          let rest ← each (leanOrder l)
          let b : RR.Block := ⟨xs.mapIdx (fun i (x, xt) => (x, some xt, RR.Expr.field (.var "v") i)) ++ rest.lets, rest.result⟩
          pure (if ← persistCell t then marked b else b)
        else
          let mut arms : Array RR.Arm := #[]
          for c in info.ctorOrder do
            let some l := info.ctors.find? c | continue
            let tys := l.posTys
            arms := arms.push (← arm n l.variant ((List.range tys.size).toArray.map fun i => some (s!"f{i}", tys[i]!))
              (order := some (leanOrder l)))
          let b : RR.Block := .ofExpr (.mtch (.var "v") arms)
          pure (if ← persistCell t then marked b else b)
      else if ← isRefType t then
        -- A reference: its value (as native Lean, which pushes `m_value`).
        let get ← refCellOpPlain "get" (.var "v") none
        let rest ← each #[("x", RR.Ty.box)]
        pure (marked ⟨#[("x", some RR.Ty.box, get)] ++ rest.lets, rest.result⟩)
      else
        match ← tupleFields? n with
        | some fields =>
          let xs := (List.range fields.size).toArray.map fun i => (s!"f{i}", fields[i]!)
          let rest ← each xs
          let b : RR.Block := ⟨xs.mapIdx (fun i (x, xt) => (x, some xt, RR.Expr.field (.var "v") i)) ++ rest.lets, rest.result⟩
          pure (if ← persistCell t then marked b else b)
        | none => pure unchanged
    | _ => pure unchanged
  modify fun s => { s with fns := s.fns.push (.fn name #[("v", t), ("k", wTy)] wTy body) }
  return some wv

/-- The number of variants of function types and of `Box`: the traversals
of `persistCall` depend on them. -/
def variantCount : LowerM (Nat × Nat) := do
  let st ← get
  return (st.fnVariants.fold (fun acc _ vs => acc + vs.size) 0, st.boxVariants.size)

/-- Generate the walks `persistCall` requested (again, replacing the
earlier ones, when variants were added since): `l2r_persist_T(v)` walks `v`
(`genPersist`), marking what it visits persistent. A type that cannot hold
a task gets a walk that does nothing. Whether anything was generated. -/
def finishPersistFns : LowerM Bool := do
  let reqs ← getPart (·.persistReqs)
  if reqs.isEmpty then return false
  let vc ← variantCount
  if (← get).persistDone == some (reqs.size, vc.1 + vc.2 * 1000003) then return false
  dropFns (·.startsWith "l2r_persist_")
  modify fun s => { s with
    typeItems := s.typeItems.filter fun | .enum n .. => n != persistListName | _ => true }
  let gen ← IO.mkRef ({} : PersistGen)
  let u64 := RR.Ty.named "u64"
  let wTy := RR.Ty.named persistListName
  let zero : RR.Block := ⟨#[("z", some u64, .atom "0")], .var "z"⟩
  let mut any := false
  for t in reqs do
    let body ← match ← genPersist t gen with
      | none => pure zero
      | some _ =>
        any := true
        let start : RR.Expr := .call (persistExpName t) #[] #[.var "v", .ctor persistListName (some "wnil") #[]]
        pure (.ofExpr (.call "l2r_persist_walk" #[] #[start]))
    modify fun s => { s with fns := s.fns.push (.fn (persistFnName t) #[("v", t)] u64 body) }
  let g ← gen.get
  if any then
    let arms := #[{ ty := persistListName, ctor := some "wnil", binders := #[], body := zero : RR.Arm }] ++ g.arms
    modify fun s => { s with
      typeItems := s.typeItems.push (.enum persistListName false (#[("wnil", #[])] ++ g.variants))
      fns := s.fns.push (.fn "l2r_persist_walk" #[("w", wTy)] u64 (.ofExpr (.mtch (.var "w") arms))) }
  let vc ← variantCount
  let n ← getPart (·.persistReqs.size)
  modify fun s => { s with persistDone := some (n, vc.1 + vc.2 * 1000003) }
  return true

/-- The program's side of the box (the box API, emitted last, when every
payload type and every variant of a function type is known):

- its release of each payload type: `fn l2r_any_rel_<n>(x : T) -> unit { }`
  (Reussir drops `x` at its type), exported to leanrt as
  `l2r_any_rel_<n>_c(cell)` by a trampoline;
- the table of those releases by payload number: the texture
  `l2r_any_releases`, which installs it in leanrt (`leanrt::any::install`),
  called through the trampoline `l2r_any_init_c` once before `main`
  (`leanrt::any::init_releases`); `leanrt::any::release_last` then defers
  the last reference of a payload as its cell with that release;
- the functions that build a function type's nullary variant from its
  index (`boxFnOfIndex`, for the typed immediates of `l2r_any_of_fn`). -/
def boxTypeItems : LowerM RR.Item := do
  let u64 := RR.Ty.named "u64"
  let mut seen : Std.HashSet Nat := {}
  let mut text := ""
  let mut decls := ""
  let mut rels := ""
  let mut count := 0
  for (t, _) in ← boxPayloads do
    if let .prog n st .. ← boxKind t then
      unless seen.contains n do
        seen := seen.insert n
        count := count + 1
        text := text ++ s!"fn l2r_any_rel_{n}(x : {st.render}) -> unit \{ }\n" ++
          s!"extern \"C\" trampoline \"l2r_any_rel_{n}_c\" = l2r_any_rel_{n};\n"
        decls := decls ++ s!"        fn l2r_any_rel_{n}_c(cell: *mut u8);\n"
        rels := rels ++ s!"        leanrt::any::Rel({n}, l2r_any_rel_{n}_c),\n"
  if count > 0 then
    text := text ++ "#[ffi(import)]\nfn l2r_any_releases() -> u64 [{ {\n" ++
      "    extern \"C\" {\n" ++ decls ++ "    }\n" ++
      s!"    static RELEASES: [leanrt::any::Rel; {count}] = [\n" ++ rels ++ "    ];\n" ++
      "    leanrt::any::install(&RELEASES)\n} }];\n" ++
      "fn l2r_any_init() -> u64 { l2r_any_releases() }\n" ++
      "extern \"C\" trampoline \"l2r_any_init_c\" = l2r_any_init;\n"
  for t in ← getPart (·.fnIndexReqs) do
    let tn := RR.fnTypeName t
    let mut iarms : Array RR.Arm := #[RR.Arm.lit 0 (.ofExpr (.ctor tn (some "z") #[]))]
    -- The variants of the enum of `t`'s run-time type (types that differ
    -- only in phantom domains share it, rule 4), at their positions in it
    -- (`fnTypeItems`: `z`, `raw`, then these); a variant without fields is
    -- an immediate (a partial application that captures nothing: also
    -- `p<j>` of a target that takes none of its first `j` parameters).
    let vs := (← getPart (·.fnVariants)).getD t.rt #[]
    for h : k in [:vs.size] do
      if (← fnVariantFields vs[k]).isEmpty then
        iarms := iarms.push (RR.Arm.lit (k + 2) (.ofExpr (.ctor tn (some (fnVariantName vs[k])) #[])))
    iarms := iarms.push { ty := "", ctor := none, binders := #[], body := .ofExpr (.call "l2r_unreachable" #[t] #[]) }
    let f := RR.Item.fn s!"l2r_fn_of_index_{t.enc}" #[("i", u64)] t (.ofExpr (.mtch (.var "i") iarms))
    text := text ++ f.render ++ "\n"
  return .raw text

/-- The enums of all function types the generated program mentions. The
enum of a function type boxed with `boxWideBit` (`boxIsWide`, given before
its variants were all known) has at most `boxWideMaxCtors` constructors, or
the translation stops: its cell must keep the wide header. -/
def fnTypeItems : LowerM (Array RR.Item) := do
  let st ← get
  -- The run-time types of the function types whose box numbers are wide.
  let wideFns : Std.HashSet RR.Ty := st.boxNums.fold (init := {}) fun acc t n =>
    if t matches .fn .. && n &&& boxWideBit != 0 && n &&& boxLeafBit == 0 then acc.insert t.rt else acc
  let mut work : Array RR.Ty := #[]
  for it in st.fns ++ st.typeItems do
    for t in it.tys do work := t.subterms work
  for (t, _) in st.boxVariants do work := t.subterms work
  for (k, _) in st.tupleTypes.toList do
    for t in k do work := t.subterms work
  let mut seen : Std.HashSet RR.Ty := {}
  let mut items := #[]
  while !work.isEmpty do
    let t := work.back!
    work := work.pop
    unless t matches .fn .. do continue
    -- One enum per run-time type (`RR.Ty.rt`).
    let t := t.rt
    let .fn d c := t | continue
    if seen.contains t then continue
    seen := seen.insert t
    let mut variants : Array (String × Array RR.Ty) := #[("z", #[]), ("raw", #[.cls d c])]
    work := (RR.Ty.cls d c).subterms work
    for v in (← getPart (·.fnVariants)).getD t #[] do
      let fs ← fnVariantFields v
      for f in fs do work := f.subterms work
      variants := variants.push (fnVariantName v, fs)
    if wideFns.contains t && variants.size > boxWideMaxCtors then
      throwError "lean2rr: the boxed function type {RR.fnTypeName t} has {variants.size} variants, \
        more than a cell with a wide header holds ({boxWideMaxCtors}; boxIsWide, internal error)"
    items := items.push (RR.Item.enum (RR.fnTypeName t) false variants)
  return items

end LeanToReussir
