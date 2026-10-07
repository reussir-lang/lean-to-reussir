import LeanToReussir.Lower.Decls
import LeanToReussir.Lower.Live

/-! # Externs -/

namespace LeanToReussir
open Lean Compiler LCNF

/-- For each parameter of `c`'s declared type, the type parameter (index
among the type-former parameters) that its value has in the mono phase, if
any; and the same for the result type. A parameter declared at `α` has
type `α`, and so has one declared at a trivial structure over `α` (such as
`[Inhabited α]`, which mono represents by its `default` field). -/
def typeVarUses (c : Name) : CoreM (Array (Option Nat) × Option Nat) := do
  let some ci := (← getEnv).find? c | return (#[], none)
  let mut ty := ci.type
  let mut tyParams : Array FVarId := #[]
  let mut uses := #[]
  repeat
    match ty with
    | .forallE _ d b _ =>
      uses := uses.push (← varOf tyParams d 8)
      let x ← mkFreshFVarId
      if isTypeFormerType d then tyParams := tyParams.push x
      ty := b.instantiate1 (.fvar x)
    | _ => break
  return (uses, ← varOf tyParams ty 8)
where
  varOf (tyParams : Array FVarId) (d : Expr) (fuel : Nat) : CoreM (Option Nat) := do
    let d := d.cleanupAnnotations
    if let .fvar x := d then return tyParams.idxOf? x
    let .const s _ := d.getAppFn | return none
    let some info ← hasTrivialStructure? s | return none
    let fuel' + 1 := fuel | return none
    let some (.ctorInfo ctor) := (← getEnv).find? info.ctorName | return none
    let mut fty ← instantiateForall ctor.type d.getAppArgs[:ctor.numParams]
    for _ in [:info.fieldIdx] do
      let .forallE _ _ b _ := fty | return none
      fty := b.instantiate1 (.fvar (← mkFreshFVarId))
    let .forallE _ fd _ _ := fty | return none
    varOf tyParams fd fuel'

/-- For each type parameter of `c`'s declared type (in order, as
`typeVarUses` numbers them), whether the declaration stores its values as
array elements: its signature (a parameter's type or the result type) has
an occurrence `Array α` of that parameter `α`. -/
def typeVarsInArrays (c : Name) : CoreM (Array Bool) := do
  let some ci := (← getEnv).find? c | return #[]
  let mut ty := ci.type
  let mut tyParams : Array FVarId := #[]
  let mut parts : Array Expr := #[]
  repeat
    match ty with
    | .forallE _ d b _ =>
      parts := parts.push d
      let x ← mkFreshFVarId
      if isTypeFormerType d then tyParams := tyParams.push x
      ty := b.instantiate1 (.fvar x)
    | _ => break
  parts := parts.push ty
  return tyParams.map fun x => parts.any fun e =>
    (e.find? fun s => s.isAppOfArity ``Array 1 && s.appArg!.cleanupAnnotations == .fvar x).isSome

/-- The C symbol Lean uses for an extern (the prelude implements functions
under the same names). -/
def externSymbol (orig : Name) : LowerM String := do
  match getExternNameFor (← getEnv) `c orig with
  | some s => return s
  | none => return "l2r_extern_" ++ fnName orig

/-- Whether a parameter of an extern is passed to the C function: erased
parameters and the IO world are not (`paramsWithoutErased`/`paramsWithoutVoid`). -/
def externParamPassed (t : Expr) : Bool :=
  let t := t.consumeMData
  !(t.isErased || t == mkConst ``lcVoid || t.isSort)

/-- Is `t` a proposition (an application of a `Prop`-valued inductive)?
Its values are proofs, which externs do not receive. -/
def isPropTy (t : Expr) : CoreM Bool := do
  let .const n _ := t.consumeMData.getAppFn | return false
  match (← getEnv).find? n with
  | some (.inductInfo iv) => return iv.type.getForallBody.isProp
  | _ => return false

/-- The type of the field of an IO result type that holds the payload
(`EST.Out.ok`'s or `ST.Out`'s value): a `Box`, the payload's type being a
parameter (one type per inductive, `nominalType`). -/
def ioPayloadFieldTy (resTy : RR.Ty) : LowerM RR.Ty := do
  let .named tn := resTy | return RR.Ty.unit
  let some info := (← get).typeInfos[tn]? | return RR.Ty.unit
  let layout := match info.shape with
    | .struct => info.ctors.find? info.ctorOrder[0]!
    | _ => info.ctors.find? ``EST.Out.ok
  match layout.bind (·.fields[0]?) with
  | some (some (_, t)) => return t
  | _ => return RR.Ty.unit

/-- Wrap a value `v : vt` as the successful result of an IO action:
`EST.Out.ok v` for `EST.Out`-typed results, `ST.Out` (a one-field struct
once the world field is dropped) for `BaseIO` results; `v` converted to the
result's field (`ioPayloadFieldTy`, a `Box`). -/
def wrapIOResult (resTy : RR.Ty) (v : RR.Expr) (vt : RR.Ty) : LowerM RR.Expr := do
  let .named tn := resTy | throwError "lean2rr: IO result of type {resTy.render}"
  let some info := (← get).typeInfos[tn]? | throwError "lean2rr: IO result of type {tn}"
  let v ← coerce v vt (← ioPayloadFieldTy resTy)
  match info.shape with
  | .struct => return .ctor tn none #[v]
  | _ =>
    let some ok := info.ctors.find? ``EST.Out.ok | throwError "lean2rr: IO result type {tn} has no ok"
    return .ctor tn (some ok.variant) #[v]

/-- The payload of IO result type `ret` (`α` of `EST.Out ε σ α` or
`ST.Out σ α`, after the parameters of a function type), as a mono type. -/
def ioPayloadExpr? (ret : Expr) : Option Expr := Id.run do
  let mut r := ret.consumeMData
  for _ in [:64] do
    match r with
    | .forallE _ _ b _ => r := (b.instantiate1 anyExpr).consumeMData
    | _ => break
  if r.isAppOfArity ``EST.Out 3 || r.isAppOfArity ``ST.Out 2 then return some r.appArg!.consumeMData
  return none

/-- The Reussir type of the payload of IO result type `ret` (`ioPayloadExpr?`;
`Box` if `ret` is not one): the payload's own type, which the glue builds
and reads before it is put into or taken out of the result's `Box` field. -/
def ioPayloadType (ret : Expr) : LowerM RR.Ty := do
  match ioPayloadExpr? ret with
  | some a => lowerType a
  | none => return RR.Ty.box

/-- The Reussir type of Lean's `IO.Error`. -/
def ioErrorTy : LowerM RR.Ty := lowerType (mkConst ``IO.Error)

/-- A value of generated type `ty` built with constructor `ctor` from its
relevant fields. -/
def ctorValue (ty : RR.Ty) (ctor : Name) (fields : Array RR.Expr) : LowerM RR.Expr := do
  let .named tn := ty | throwError "lean2rr: constructor {ctor} at type {ty.render}"
  if tn == "bool" then return .atom (if ctor == ``Bool.true then "true" else "false")
  let some info := (← get).typeInfos[tn]? | throwError "lean2rr: constructor {ctor} of non-nominal type {tn}"
  let some layout := info.ctors.find? ctor | throwError "lean2rr: constructor {ctor} not in type {tn}"
  let fields := layout.place fields
  return match info.shape with
    | .struct => .ctor tn none fields
    | _ => .ctor tn (some layout.variant) fields

/-- The types of the relevant fields of constructor `ctor` of generated type `ty`. -/
def ctorFieldTys (ty : RR.Ty) (ctor : Name) : LowerM (Array RR.Ty) := do
  let .named tn := ty | return #[]
  let some info := (← get).typeInfos[tn]? | return #[]
  let some layout := info.ctors.find? ctor | return #[]
  return layout.fields.filterMap (·.map (·.2))

/-- `IO.FS.Metadata` from the runtime's `[atime s, ns, mtime s, ns, size,
file type, links]`. -/
def metadataOf (mt : RR.Ty) (v : RR.Expr) : LowerM RR.Expr := do
  let fs ← ctorFieldTys mt ``IO.FS.Metadata.mk
  let some stTy := fs[0]? | throwError "lean2rr: bad IO.FS.Metadata type"
  let some (RR.Ty.named ftn) := fs[3]? | throwError "lean2rr: bad IO.FS.Metadata type"
  let get (i : Nat) : RR.Expr := .call "l2r_array_get" #[.named "u64"] #[.var "m", .atom (toString i)]
  let time (i : Nat) : LowerM RR.Expr := ctorValue stTy ``IO.FS.SystemTime.mk
    #[.call "lean_int64_to_int_sint" #[] #[get i], .cast (get (i + 1)) (.named "u32")]
  let md ← ctorValue mt ``IO.FS.Metadata.mk
    #[← time 0, ← time 2, get 4, .call (← enumOfIndexFn ftn) #[] #[get 5], get 6]
  return .block ⟨#[("m", some (.app "RVec" #[.named "u64"]), v)], md⟩

/-- `Array IO.FS.DirEntry` (an array of `Box`es, each holding a
`DirEntry`) from a directory and the runtime's entry names. -/
def dirEntriesOf (arrTy : RR.Ty) (root names : RR.Expr) : LowerM RR.Expr := do
  let some ae := arrayElem? arrTy | throwError "lean2rr: bad directory entry array {arrTy.render}"
  let entryTy ← lowerType (mkConst ``IO.FS.DirEntry)
  let .named en := entryTy | throwError "lean2rr: bad directory entry type"
  let name := s!"l2r_dir_entries_{en}"
  unless (← hasFn name) do
    let u64 := RR.Ty.named "u64"
    let entry ← ctorValue entryTy ``IO.FS.DirEntry.mk
      #[.var "root", .call "l2r_array_get" #[.named "LStr"] #[.var "names", .var "i"]]
    let body : RR.Block := .ofExpr <| .ite (.atom "i < n")
      ⟨#[("one", some u64, .atom "1"), ("e", some ae, ← coerce entry entryTy ae)],
        .call (name ++ "_go") #[] #[.var "root", .var "names", .atom "i + one", .var "n",
          arrayCall ae "push" #[.var "acc", .var "e"]]⟩
      (.ofExpr (.var "acc"))
    let strs := RR.Ty.app "RVec" #[.named "LStr"]
    let entry' : RR.Block := ⟨#[("n", some u64, .call "l2r_array_size" #[.named "LStr"] #[.var "names"]),
        ("zero", some u64, .atom "0")],
      .call (name ++ "_go") #[] #[.var "root", .var "names", .var "zero", .var "n", arrayCall ae "empty" #[]]⟩
    modify fun s => { s with fns := s.fns ++ #[
      .fn (name ++ "_go") #[("root", .named "LStr"), ("names", strs), ("i", u64), ("n", u64), ("acc", arrTy)] arrTy body,
      .fn name #[("root", .named "LStr"), ("names", strs)] arrTy entry'] }
  return .call name #[] #[root, names]

/-- The runtime primitive implementing fallible IO extern `sym`. -/
def fallibleIOPrim (sym : String) : String :=
  if sym == "lean_io_prim_handle_mk" then "l2r_fs_open"
  else if sym.startsWith "lean_io_prim_handle_" then "l2r_fs_" ++ (sym.drop 20).toString
  else if sym == "lean_io_realpath" then "l2r_fs_real_path"
  else if sym == "lean_io_symlink_metadata" then "l2r_fs_metadata"
  else if sym == "lean_chmod" then "l2r_fs_set_access_rights"
  else "l2r_fs_" ++ (sym.drop 8).toString

/-- The generated IO result type `resTy`'s error constructor and the type of
its error field (a `Box`, which holds the `IO.Error`). -/
def ioErrorCtor (resTy : RR.Ty) : LowerM (String × CtorLayout × RR.Ty) := do
  let .named rn := resTy | throwError "lean2rr: IO result of type {resTy.render}"
  let some info := (← get).typeInfos[rn]? | throwError "lean2rr: IO result of type {rn}"
  let some errL := info.ctors.find? ``EST.Out.error | throwError "lean2rr: IO result {rn} cannot fail"
  match errL.fields[0]? with
  | some (some (_, t)) => return (rn, errL, t)
  | _ => throwError "lean2rr: IO result {rn} has no error field"

/-- The error callback of `l2r_io_finish` for IO result `resTy`:
`|kind| |errno| |fname| |details| EST.Out.error e`, with `e` built by Lean's
own `IO.Error` builder for the error kind the runtime reports (as Lean's
`decode_io_error`). -/
def ioErrorFn (resTy : RR.Ty) : LowerM RR.Expr := do
  let (rn, errL, errTy) ← ioErrorCtor resTy
  let ioErr ← ioErrorTy
  let (k, errno, fname, details) := ("ek", "ee", "ef", "ed")
  let mut mk : RR.Expr := .call "l2r_unreachable" #[ioErr] #[]
  for i in [:(← read).ioErrorBuilders.size] do
    let j := (← read).ioErrorBuilders.size - 1 - i
    let some inst := (← read).ioErrorBuilders[j]! | continue
    let callee ← calleeOf inst
    let .code fn ps .. := callee | continue
    let call := if ps.size == 3 then RR.Expr.call fn #[] #[.var fname, .var errno, .var details]
      else if ps.size == 2 then RR.Expr.call fn #[] #[.var errno, .var details]
      else RR.Expr.call fn #[] #[.var details]
    let kj ← fresh "kj"
    mk := .block ⟨#[(kj, some (.named "u32"), .atom (toString j))],
      .ite (.atom s!"{k} == {kj}") (.ofExpr call) (.ofExpr mk)⟩
  let errVal := RR.Expr.ctor rn (some errL.variant) #[← coerce mk ioErr errTy]
  return RR.Expr.lam k (.named "u32") <| .ofExpr <| .lam errno (.named "u32") <| .ofExpr <|
    .lam fname (.named "LStr") <| .ofExpr <| .lam details (.named "LStr") (.ofExpr errVal)

/-- `l2r_io_finish(v, ok, err)`: the outcome of a fallible runtime primitive
(result `v : primRet`) as the IO result `resTy`: `EST.Out.ok (okOf x)`
(`okOf` gives the payload at type `payTy`), or `EST.Out.error e` with `e`
built by Lean's own `IO.Error` builder for the error kind the runtime
reports (as Lean's `decode_io_error`). -/
def ioFinish (v : RR.Expr) (primRet resTy payTy : RR.Ty) (okOf : RR.Expr → LowerM RR.Expr) : LowerM RR.Expr := do
  let x ← fresh "fx"
  let okFn := RR.Expr.lam x primRet (.ofExpr (← wrapIOResult resTy (← okOf (.var x)) payTy))
  return .call "l2r_io_finish" #[primRet, resTy] #[v, okFn, ← ioErrorFn resTy]

/-- `if l2r_io_ok() { ok } else { EST.Out.error e }`: the outcome of the
fallible primitive just called (its result already bound), as `ioFinish`,
but with the continuation `ok : resTy` in line instead of in a callback. A
handle that the continuation uses is then released at its last use there,
not when a callback that captured it is freed. -/
def ioCheck (resTy : RR.Ty) (ok : RR.Block) : LowerM RR.Expr := do
  return .ite (.call "l2r_io_ok" #[] #[]) ok
    (.ofExpr (.call "l2r_io_error_with" #[resTy] #[← ioErrorFn resTy]))

/-- `EST.Out.error (IO.userError msg)` as IO result `resTy` (Lean's exported
builder `lean_mk_io_user_error`). -/
def ioUserError (resTy : RR.Ty) (msg : String) : LowerM RR.Expr := do
  let (rn, errL, errTy) ← ioErrorCtor resTy
  let ioErr ← ioErrorTy
  let kind := ioErrorBuilderSyms.idxOf "lean_mk_io_user_error"
  let e ← match (← read).ioErrorBuilders[kind]?.join with
    | some inst => match ← calleeOf inst with
      | .code fn .. => pure (RR.Expr.call fn #[] #[← strLit msg])
      | _ => pure (RR.Expr.call "l2r_unreachable" #[ioErr] #[])
    | none => pure (RR.Expr.call "l2r_unreachable" #[ioErr] #[])
  return .ctor rn (some errL.variant) #[← coerce e ioErr errTy]

/-- Glue for a fallible IO extern: call the runtime primitive, then
`l2r_io_finish` turns its outcome into `EST.Out.ok payload` or into
`EST.Out.error e`, where `e` is built by Lean's own `IO.Error` builder for
the error kind the runtime reports (as Lean's `decode_io_error`). -/
def fallibleIOGlue (prim : String) (primRet : RR.Ty) (argTys : Array RR.Ty) (args : Array RR.Expr)
    (ret : Expr) (follow : Bool := true) : LowerM RR.Expr := do
  let resTy ← lowerType ret
  let payload ← ioPayloadType ret
  -- Arguments: enumerations (`IO.FS.Mode`) are passed as their index.
  let mut lets : Array (String × Option RR.Ty × RR.Expr) := #[]
  let mut vals := #[]
  for (a, t) in args.zip argTys do
    let x ← fresh "fa"
    let e ← match t with
      | .named tn =>
        -- A handle is `lcAny` in mono code, so it arrives boxed.
        if tn == boxName then coerce a t (.named "LHandle") else
        match (← get).typeInfos[tn]? with
        | some ti => if ti.shape == .enumLike then
            pure (.cast (RR.Expr.call (← enumIndexFn tn) #[] #[a]) (.named "u8")) else pure a
        | none => pure a
      | _ => pure a
    lets := lets.push (x, none, e)
    vals := vals.push (RR.Expr.var x)
  let v ← fresh "fv"
  -- `metadata` and `symlinkMetadata` differ in following symbolic links.
  if prim == "l2r_fs_metadata" then vals := vals.push (.atom (toString follow))
  lets := lets.push (v, some primRet, .call prim #[] vals)
  let finish ← ioFinish (.var v) primRet resTy payload fun x => do
    if payload == RR.Ty.unit then pure RR.Expr.unitVal
    else if prim == "l2r_fs_metadata" then metadataOf payload x
    else if prim == "l2r_fs_read_dir" then dirEntriesOf payload vals[0]! x
    else if prim == "l2r_fs_create_tempfile" then
      -- `(handle, path)`: the path of the file just created.
      let tys ← ctorFieldTys payload ``Prod.mk
      ctorValue payload ``Prod.mk #[← coerce x primRet (tys[0]?.getD primRet),
        ← coerce (.call "l2r_fs_temp_file_path" #[] #[]) (.named "LStr") (tys[1]?.getD (.named "LStr"))]
    else coerce x primRet payload
  return .block ⟨lets, finish⟩

/-- Field `i` of the standard stream record type `streamTy`: its name, the
parameters of its curried function type and its IO result type. -/
def streamField (streamTy : RR.Ty) (i : Nat) : LowerM (Option (Name × Array RR.Ty × RR.Ty)) := do
  let .named sn := streamTy | return none
  let some info := (← get).typeInfos[sn]? | return none
  let some layout := info.ctors.find? info.ctorOrder[0]! | return none
  let fieldNames := getStructureFields (← getEnv) ``IO.FS.Stream
  let some fname := fieldNames[i]? | return none
  let some (some (_, fty)) := layout.fields[i]? | return none
  let (ps, t) := fnChain fty.rt
  return some (fname, ps, t)

/-- The payload type of the IO action of field `i` of `IO.FS.Stream` (from
the field's Lean type: the result's field is a `Box`). -/
def streamPayloadTy (i : Nat) : LowerM RR.Ty := do
  let mut ty ← getOtherDeclBaseType ``IO.FS.Stream.mk []
  for _ in [:i] do
    match ty.consumeMData with
    | .forallE _ _ b _ => ty := b.instantiate1 anyExpr
    | _ => return RR.Ty.box
  let .forallE _ d _ _ := ty.consumeMData | return RR.Ty.box
  ioPayloadType (← toMonoTypeKeep d)

/-- Stream field `i` on file descriptor `fd` applied to `args`: the runtime
primitive `l2r_stream_<field>`. Erased and world parameters are not passed
to the primitive. -/
def streamFieldCall (fd : Nat) (i : Nat) (streamTy : RR.Ty) (args : Array RR.Expr) : LowerM RR.Expr := do
  let some (fname, ps, t) ← streamField streamTy i | throwError "lean2rr: bad stream field"
  let passed := (args.zip ps).filterMap fun (a, pt) => if pt == .unit then none else some a
  let prim := s!"l2r_stream_{fname}"
  let call := RR.Expr.call prim #[] (#[.atom (toString fd)] ++ passed)
  let payload ← streamPayloadTy i
  match (← read).preludeRets[prim]? with
  -- Fallible operations report errors (broken pipe, closed stream, wrong
  -- direction) through the runtime's last-error protocol.
  | some primRet =>
    if fname == `isTty then wrapIOResult t call primRet
    else ioFinish call primRet t payload fun x =>
      if payload == RR.Ty.unit then pure .unitVal else coerce x primRet payload
  | none =>
    -- Primitives with no result return `u64` (Reussir's `unit` is not a value).
    let v ← if payload == RR.Ty.unit then do
        let r ← fresh "r"
        pure (RR.Expr.block ⟨#[(r, some (.named "u64"), call)], .unitVal⟩)
      else pure call
    wrapIOResult t v payload

/-- A standard stream (`IO.getStdout` & co.) as a Lean `IO.FS.Stream` value:
each field is a function value whose target is `streamFieldCall` (a
nullary variant, so the record is the only allocation). -/
def streamValue (fd : Nat) (streamTy : RR.Ty) : LowerM RR.Expr := do
  let .named sn := streamTy | throwError "lean2rr: bad stream type"
  let fieldNames := getStructureFields (← getEnv) ``IO.FS.Stream
  let mut vals := #[]
  for i in [:fieldNames.size] do
    let some (_, ps, t) ← streamField streamTy i | continue
    let (v, _) ← partValue { id := s!"s{fd}f{i}{sn}", params := ps, ret := t, call := .stream fd i streamTy } 0 #[]
    vals := vals.push v
  return .ctor sn none vals

/-- `l2r_get_std_<fd>()` and `l2r_set_std_<fd>(s)`: the current standard
stream `fd` is kept in a cell slot (built on first use, like Lean's
thread-local streams), which `IO.setStdout` & co. replace, returning the
previous stream. -/
def stdStreamFns (fd : Nat) (streamTy : RR.Ty) : LowerM (String × String) := do
  let getFn := s!"l2r_get_std_{fd}"
  let setFn := s!"l2r_set_std_{fd}"
  if (← hasFn getFn) then return (getFn, setFn)
  let base ← match (← get).stdSlots with
    | some b => pure b
    | none => do
      let b ← getPart (·.cafSlots)
      modify fun s => { s with cafSlots := b + 3, stdSlots := some b, stdStreamTy := some streamTy }
      pure b
  let slot := RR.Expr.atom (toString (base + fd))
  let getBody : RR.Block := .ofExpr (.ite (.call "l2r_once_has" #[] #[slot])
    (.ofExpr (.call "l2r_once_get" #[streamTy] #[slot]))
    (.ofExpr (.call "l2r_once_set" #[streamTy] #[slot, ← streamValue fd streamTy])))
  let setBody : RR.Block :=
    ⟨#[("cur", some streamTy, .call getFn #[] #[])], .call "l2r_cell_swap" #[streamTy] #[slot, .var "s"]⟩
  let items := #[RR.Item.fn getFn #[] streamTy getBody, .fn setFn #[("s", streamTy)] streamTy setBody]
  modify fun s => { s with fns := s.fns ++ items }
  return (getFn, setFn)

/-- `l2r_std_enter()` / `l2r_std_leave()`: natively every thread has its
own current standard streams, starting as the process's (`IO.setStdout` &
co. replace the current thread's). A task runs, natively, on a worker thread,
and `main` on a thread of its own, apart from the module initializers: so a
task starts with empty stream cells (rebuilt as the process's streams on
first use) and the caller's are put back when it ends, releasing the task's
(`leanrt::once::push_context`); `main` starts with empty cells too when it
runs on a thread of its own (not with `LEAN_MAIN_USE_THREAD=0`, see
`lowerEntry`). Without any use of the standard streams they do nothing. -/
def stdContextFns : LowerM (Array RR.Item) := do
  let u64 := RR.Ty.named "u64"
  let zero (x : String) : RR.Block := ⟨#[(x, some u64, .atom "0")], .var x⟩
  -- `l2r_std_enter_if(b)` / `l2r_std_leave_if(b)`: only when `b` is 1 (a
  -- task running as on a worker thread, see `l2r_task_begin`).
  let ifs : Array RR.Item := #["enter", "leave"].map fun w =>
    .fn s!"l2r_std_{w}_if" #[("b", u64)] u64 ⟨#[("one", some u64, .atom "1")],
      .ite (.atom "b == one") (.ofExpr (.call s!"l2r_std_{w}" #[] #[])) (zero "z")⟩
  -- In a program that creates tasks, `l2r_std_drop_workers()` drops the
  -- pool workers' stream cells at the task manager's finalization (each in
  -- turn made current, `l2r_worker_streams_enter`, then dropped,
  -- `l2r_std_leave`), as native worker threads' finalizers drop their
  -- current streams (lean-runtime's AR-33): the runtime calls it there,
  -- through its trampoline (`leanrt::sched::workers_end`).
  let createsTasks := (← read).createsTasks
  let tramp : RR.Item := .raw "extern \"C\" trampoline \"l2r_std_drop_workers_c\" = l2r_std_drop_workers;\n"
  let dropWorkers (base : Option Nat) : Array RR.Item := Id.run do
    unless createsTasks do return #[]
    let some b := base | return #[.fn "l2r_std_drop_workers" #[] u64 (zero "z"), tramp]
    return #[tramp, .fn "l2r_std_drop_workers" #[] u64 ⟨#[("more", some u64, .call "l2r_worker_streams_enter" #[] #[.atom (toString b)]),
      ("one", some u64, .atom "1")],
      .ite (.atom "more == one")
        ⟨#[("l", some u64, .call "l2r_std_leave" #[] #[])], .call "l2r_std_drop_workers" #[] #[]⟩ (zero "z")⟩]
  let some base := (← get).stdSlots | return #[.fn "l2r_std_enter" #[] u64 (zero "z"), .fn "l2r_std_leave" #[] u64 (zero "z")] ++ ifs ++ dropWorkers none
  let some st := (← get).stdStreamTy | return #[.fn "l2r_std_enter" #[] u64 (zero "z"), .fn "l2r_std_leave" #[] u64 (zero "z")] ++ ifs ++ dropWorkers none
  let mut lets : Array (String × Option RR.Ty × RR.Expr) := #[]
  for fd in [0:3] do
    let slot := RR.Expr.atom (toString (base + fd))
    let dropIt : RR.Block := ⟨#[(s!"s{fd}", some st, .call "l2r_once_take" #[st] #[slot]), (s!"t{fd}", some u64, .atom "0")],
      .var s!"t{fd}"⟩
    lets := lets.push (s!"d{fd}", some u64, .ite (.call "l2r_once_has" #[] #[slot]) dropIt (zero s!"f{fd}"))
  return #[.fn "l2r_std_enter" #[] u64 (.ofExpr (.call "l2r_std_push" #[] #[.atom (toString base)])),
    .fn "l2r_std_leave" #[] u64 ⟨lets, .call "l2r_std_pop" #[] #[.atom (toString base)]⟩] ++ ifs ++ dropWorkers (some base)

/-- `l2r_stderr_put(s)`, defined in every program for the runtime's
diagnostics (panics, `dbgTrace`, `timeit`): native Lean writes them with the
*current* stderr stream's `putStr` (`io_eprintln`), ignoring its result.
Without any use of the standard streams, the current stderr is descriptor 2. -/
def stderrPutFn : LowerM RR.Item := do
  let sTy := RR.Ty.named "LStr"
  let u64 := RR.Ty.named "u64"
  let simple := RR.Item.fn "l2r_stderr_put" #[("s", sTy)] u64
    (.ofExpr (.call "l2r_stream_putStr" #[] #[.atom "2", .var "s"]))
  let some st := (← get).stdStreamTy | return simple
  let .named sn := st | return simple
  let some info := (← get).typeInfos[sn]? | return simple
  let some layout := info.ctors.find? info.ctorOrder[0]! | return simple
  let some i := (getStructureFields (← getEnv) ``IO.FS.Stream).idxOf? `putStr | return simple
  let some (some (pos, fty)) := layout.fields[i]? | return simple
  let (getFn, _) ← stdStreamFns 2 st
  let (ps, t) := fnChain fty.rt
  unless ps.size == 2 do return simple
  let r ← applyCall (.field (.var "cur") pos) fty #[.var "s", .unitVal]
  return .fn "l2r_stderr_put" #[("s", sTy)] u64
    ⟨#[("cur", some st, .call getFn #[] #[]), ("r", some t, r)], .atom "0"⟩

/-- `l2r_eq_<T>(a, b)`: structural equality on generated type `tn` whose
fields are `tn` itself, strings, `Nat`s or scalars (`Lean.Name.beq`,
`lean_name_eq`: the same constructor and equal fields; a name's cached hash
is compared first). `none` for other field types. -/
partial def structEqFn (tn : String) : LowerM (Option String) := do
  let name := s!"l2r_eq_{tn}"
  if (← hasFn name) then return some name
  let some info := (← get).typeInfos[tn]? | return none
  let fieldEq (t : RR.Ty) (x y : String) : Option RR.Expr :=
    match t with
    | .named n =>
      if n == tn then some (.call name #[] #[.var x, .var y])
      else if n == "LStr" then some (.call "lean_string_dec_eq" #[] #[.var x, .var y])
      else if n == "Nat" then some (.call "lean_nat_dec_eq" #[] #[.var x, .var y])
      else if n ∈ ["u8", "u16", "u32", "u64", "i8", "i16", "i32", "i64", "bool"] then some (.atom s!"{x} == {y}")
      else none
    | _ => none
  let mut arms := #[]
  for c in info.ctorOrder do
    let some l := info.ctors.find? c | continue
    let tys := l.posTys
    let xs := (List.range tys.size).toArray.map fun i => s!"ea{i}"
    let ys := (List.range tys.size).toArray.map fun i => s!"eb{i}"
    -- Scalars first, the recursive field last.
    let order := (List.range tys.size).toArray.qsort fun i j =>
      let rank (k : Nat) := if tys[k]! == .named tn then 2 else if tys[k]! matches .named "LStr" | .named "Nat" then 1 else 0
      rank i < rank j
    let mut body : RR.Expr := .atom "true"
    for i in order.reverse do
      let some e := fieldEq tys[i]! xs[i]! ys[i]! | return none
      body := if body matches .atom "true" then e else .ite e (.ofExpr body) (.ofExpr (.atom "false"))
    let tyName := match info.shape with | .struct => tn | _ => tn
    let inner := RR.Expr.mtch (.var "b") #[
      { ty := tyName, ctor := if info.shape == .struct then none else some l.variant,
        binders := ys.map some, body := .ofExpr body },
      { ty := tyName, ctor := none, binders := #[], body := .ofExpr (.atom "false") }]
    arms := arms.push { ty := tyName, ctor := some l.variant, binders := xs.map some, body := .ofExpr inner : RR.Arm }
  if info.shape == .struct then return none
  let item := RR.Item.fn name #[("a", .named tn), ("b", .named tn)] .bool (.ofExpr (.mtch (.var "a") arms))
  modify fun s => { s with fns := s.fns.push item }
  return some name

/-- A generated function folding a Lean `List` into an accumulator:
`go(l, acc)` = `acc` extended with every element via `step(acc, x)`, the
element `x` at type `elemTy`. Cached by name (which must name `elemTy` and
`accTy`). -/
def listFold (name : String) (listTy accTy elemTy : RR.Ty) (step : RR.Expr → RR.Expr → RR.Expr) :
    LowerM String := do
  if (← hasFn name) then return name
  let .named lt := listTy | throwError "lean2rr: bad list type"
  let some info := (← get).typeInfos[lt]? | throwError "lean2rr: bad list type"
  let some nil := info.ctors.find? ``List.nil | throwError "lean2rr: bad list type"
  let some cons := info.ctors.find? ``List.cons | throwError "lean2rr: bad list type"
  -- The element converted to `elemTy` from the head's `Box` (a field of
  -- the parameter's type is a `Box` at every instantiation, `nominalType`).
  let some (_, ht) := cons.fields[0]?.join | throwError "lean2rr: bad list type {lt} (internal error)"
  let x ← coerce (.var "x") ht elemTy
  let body : RR.Block := .ofExpr (.mtch (.var "l") #[
    { ty := lt, ctor := some nil.variant, binders := #[], body := .ofExpr (.var "acc") },
    { ty := lt, ctor := some cons.variant,
      binders := (cons.place #[.var "x", .var "t"]).map fun
        | .var v => some v | _ => none,
      body := .ofExpr (.call name #[] #[.var "t", step (.var "acc") x]) }])
  modify fun s => { s with fns := s.fns.push (.fn name #[("l", listTy), ("acc", accTy)] accTy body) }
  return name

/-- The C symbols of the externs that make a task or a promise: a program
reaching one can have other contexts than `main`'s (a promise's
dependents run where it is resolved, the event loop's completions on a
context of their own). -/
def taskExternSyms : List String :=
  ["lean_task_spawn", "lean_task_map", "lean_task_bind", "lean_io_as_task", "lean_io_map_task",
   "lean_io_bind_task", "lean_io_promise_new"]

/-- Whether the program creates tasks: one of its extern instances
(`decls`, after the shim's replacements, Lean's library's code included)
makes a task or a promise (`taskExternSyms`). Every other context comes
from those: a task's own; a promise's dependents, run where it is resolved;
the event loop's completions, which resolve the promises the shim's Lean
code makes (`IO.Promise.new`). So a program without them has one context,
`main`'s, whatever else it uses (a `Std.Sync` object or a timer alone
makes none). The seven are polymorphic, so each one a program reaches is an
instance in `decls`. (The `Std.Sync` and event-loop externs, which this
once also counted to be safe, are monomorphic: they are never instances,
so that test could never match; review RS4-07.) Translation plan §5.14,
"References". -/
def programCreatesTasks (env : Environment) (keys : NameMap InstKey) (decls : Array (Decl .pure)) : Bool :=
  decls.any fun d => match d.value with
    | .extern _ =>
      let orig := ((keys.find? d.name).map (·.decl)).getD d.name
      match getExternNameFor env `c orig with
      | some sym => taskExternSyms.contains sym
      | none => false
    | _ => false

/-- In a program that creates tasks, the point before reference operation
`op` on the reference `r` (of the reference type, `refType`; prelude
`l2r_ref_*`, `leanrt::refs`): a polling point before a read, a publication
before a write, and, while some reference is taken by a `modify`, the wait
for its store (Lean 4.35's rule; `take` always records the reference).
`none` in a program without tasks. -/
def refPoint (op : String) (r : RR.Expr) : LowerM (Option (String × Option RR.Ty × RR.Expr)) := do
  unless (← read).createsTasks do return none
  let rt ← refType
  let n ← fresh "rp"
  let u64 := RR.Ty.named "u64"
  if op == "take" then return some (n, some u64, .call "l2r_ref_take_mark" #[rt] #[r])
  let (point, store) := match op with
    | "get" => ("l2r_ref_read_point", "0")
    | "set" => ("l2r_ref_write_point", "1")
    | _ => ("l2r_ref_swap_point", "1")
  return some (n, some u64,
    .ite (.call point #[] #[]) (.ofExpr (.call "l2r_ref_wait" #[rt] #[r, .atom store])) (.ofExpr (.atom "0")))

/-- Reference operation `op` on the reference `r` (of the reference type,
`refType`, whose cell holds a `Box`; `v`, for `set` and `swap`, a `Box`):
`get` (a copy: the cell keeps its reference), `take` (the value moves out
and the cell gets the placeholder, as `lean_st_ref_take` stores `box(0)`:
Lean's `modify` is take-then-set, so a value only the cell holds stays
unshared and is updated in place), `set` (`u64` result: `l2r_rc_set_ref`,
which releases the old value after storing the new one, as
`lean_st_ref_set` does: code the release runs, the `sync` dependents of a
promise it drops, sees the new value; and then the reference `r` itself,
which the caller would release natively after the set: when the set is
`r`'s last use, its cell, and the new value with it, is freed after the old
value, not at the store), `swap`. The results are `Box`es. The cell operation
alone (`refCellOp` adds the task-aware point): also the read of a
constant's walk for tasks, which natively reads the cell directly. -/
def refCellOpPlain (op : String) (r : RR.Expr) (v : Option RR.Expr) : LowerM RR.Expr := do
  let cell := RR.Expr.field r 0
  let e := RR.Ty.box
  match op, v with
  | "get", _ => return .call "l2r_rc_get" #[e] #[cell]
  | "take", _ => return .call "l2r_rc_swap" #[e] #[cell, ← zeroValue e]
  | "set", some v => return .call "l2r_rc_set_ref" #[e, ← refType] #[cell, v, r]
  | "swap", some v => return .call "l2r_rc_swap" #[e] #[cell, v]
  | _, _ => throwError "lean2rr: reference operation {op} without a value (internal error)"

/-- Reference operation `op` (`refCellOpPlain`) on the reference `r`: in a
program that creates tasks, after its `refPoint`. -/
def refCellOp (op : String) (r : RR.Expr) (v : Option RR.Expr) : LowerM RR.Expr := do
  let res ← refCellOpPlain op r v
  match ← refPoint op r with
  | some l => return .block ⟨#[l], res⟩
  | none => return res

/-- Glue for `ST.Ref` operations (translation plan §5.1). A reference is one
generated record type holding a Reussir cell of a `Box`, `L2RRefN(Cell<Box>)`
(`refType`), whatever its contents' type: two allocations per reference
(the record and the cell). Lean's mono phase types every reference
`lcAny`, so a reference travels in a `Box`; an operation unboxes it (one
variant) and acts on its one cell, boxing the value it stores and giving
the value it reads as a `Box` (the IO result's field is one). So all
aliases of a reference share its one cell. `args` are at the Reussir types
of `params`. -/
def refGlue (orig : Name) (params : Array Expr) (ret : Expr)
    (args : Array RR.Expr) : LowerM (Option RR.Expr) := do
  let resTy ← lowerType ret
  let rt ← refType
  let box := RR.Ty.box
  let tyOf (i : Nat) : LowerM RR.Ty := lowerType params[i]!
  let value (i : Nat) : LowerM RR.Expr := do coerce args[i]! (← tyOf i) box
  -- The reference `i`, at the reference type, bound to a variable.
  let handle (i : Nat) (k : RR.Expr → LowerM RR.Expr) : LowerM RR.Expr := do
    let h ← coerce args[i]! (← tyOf i) rt
    match h with
    | .var _ => k h
    | _ =>
      let n ← fresh "rh"
      return .block ⟨#[(n, some rt, h)], ← k (.var n)⟩
  -- Operation `op` on handle `i` (with value `v`): a `Box` (`u64` for `set`).
  let onHandle (op : String) (i : Nat) (v : Option RR.Expr) : LowerM RR.Expr := do
    handle i fun h => refCellOp op h v
  match orig with
  | ``ST.Prim.mkRef =>
    return some (← wrapIOResult resTy (refNew rt (← value 0)) rt)
  | ``ST.Prim.Ref.get =>
    return some (← wrapIOResult resTy (← onHandle "get" 0 none) box)
  | ``ST.Prim.Ref.take =>
    return some (← wrapIOResult resTy (← onHandle "take" 0 none) box)
  | ``ST.Prim.Ref.set =>
    let r ← fresh "rs"
    return some (.block ⟨#[(r, some (.named "u64"), ← onHandle "set" 0 (some (← value 1)))],
      ← wrapIOResult resTy .unitVal .unit⟩)
  | ``ST.Prim.Ref.swap =>
    return some (← wrapIOResult resTy (← onHandle "swap" 0 (some (← value 1))) box)
  | ``ST.Prim.Ref.ptrEq =>
    let (x, y) := (← fresh "ra", ← fresh "ra")
    let u64 := RR.Ty.named "u64"
    let addr (i : Nat) : LowerM RR.Expr := handle i fun h => pure (.call "l2r_ptr_addr_rec" #[rt] #[h])
    return some (← wrapIOResult resTy
      (.block ⟨#[(x, some u64, ← addr 0), (y, some u64, ← addr 1)], .atom s!"{x} == {y}"⟩) .bool)
  | _ => return none

/-- Externs over Lean-defined types: the runtime's generic helpers receive
the generated constructors as arguments. -/
def ctorCallbackExtern (sym : String) (ret : Expr) (args : Array RR.Expr) : LowerM (Option RR.Expr) := do
  let rt ← lowerType ret
  let lam (x : String) (t : RR.Ty) (body : RR.Expr) : RR.Expr := .lam x t (.ofExpr body)
  match sym with
  -- `timeit msg act`, `allocprof msg act`: the runtime runs the action.
  | "lean_io_timeit" | "lean_io_allocprof" =>
    let helper := if sym == "lean_io_timeit" then "l2r_io_timeit_with" else "l2r_io_allocprof_with"
    let some msg := args[0]? | return none
    let some act := args[1]? | return none
    let act ← coerce act (.fn .unit rt) (.cls .unit rt)
    return some (.call helper #[rt] #[msg, act])
  -- `IO.getEnv name : BaseIO (Option String)`.
  | "lean_io_getenv" =>
    let some name := args[0]? | return none
    let pay ← ioPayloadType ret
    let some v := (← ctorFieldTys pay ``Option.some)[0]? | return none
    let some' ← ctorValue pay ``Option.some #[← coerce (.var "s") (.named "LStr") v]
    let r := RR.Expr.call "l2r_io_getenv_with" #[pay]
      #[name, ← ctorValue pay ``Option.none #[], lam "s" (.named "LStr") some']
    return some (← wrapIOResult rt r pay)
  -- `String.mk : List Char → String`: push the characters.
  | "lean_string_compare" =>
    let v (c : Name) := ctorValue rt c #[]
    return some (.call "l2r_string_compare_with" #[rt] (args ++ #[← v ``Ordering.lt, ← v ``Ordering.eq, ← v ``Ordering.gt]))
  | "lean_string_data" =>
    let some hd := (← ctorFieldTys rt ``List.cons)[0]? | return none
    let cons ← ctorValue rt ``List.cons #[← coerce (.var "c") (.named "u32") hd, .var "t"]
    return some (.call "l2r_string_to_list" #[rt]
      (args ++ #[← ctorValue rt ``List.nil #[], lam "c" (.named "u32") (lam "t" rt cons)]))
  | "lean_string_utf8_get_opt" =>
    let some v := (← ctorFieldTys rt ``Option.some)[0]? | return none
    let some' ← ctorValue rt ``Option.some #[← coerce (.var "c") (.named "u32") v]
    return some (.call "l2r_string_utf8_get_opt_with" #[rt]
      (args ++ #[← ctorValue rt ``Option.none #[], lam "c" (.named "u32") some']))
  | "lean_float_frexp" | "lean_float32_frexp" =>
    let fty := RR.Ty.named (if sym == "lean_float_frexp" then "f64" else "f32")
    let tys ← ctorFieldTys rt ``Prod.mk
    let some mt := tys[0]? | return none
    let some et := tys[1]? | return none
    let pair ← ctorValue rt ``Prod.mk #[← coerce (.var "m") fty mt, ← coerce (.var "e") (.named "Int") et]
    let helper := if sym == "lean_float_frexp" then "l2r_float_frexp_with" else "l2r_float32_frexp_with"
    return some (.call helper #[rt] (args ++ #[lam "m" fty (lam "e" (.named "Int") pair)]))
  | _ => return none

end LeanToReussir
