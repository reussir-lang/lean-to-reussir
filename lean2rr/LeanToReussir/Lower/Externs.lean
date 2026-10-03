import LeanToReussir.Lower.Decls

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

/-- Wrap a value as the successful result of an IO action: `EST.Out.ok v`
for `EST.Out`-typed results, `ST.Out` (a one-field struct once the world
field is dropped) for `BaseIO` results. -/
def wrapIOResult (resTy : RR.Ty) (v : RR.Expr) : LowerM RR.Expr := do
  let .named tn := resTy | throwError "lean2rr: IO result of type {resTy.render}"
  let some info := (← get).typeInfos[tn]? | throwError "lean2rr: IO result of type {tn}"
  match info.shape with
  | .struct => return .ctor tn none #[v]
  | _ =>
    let some ok := info.ctors.find? ``EST.Out.ok | throwError "lean2rr: IO result type {tn} has no ok"
    return .ctor tn (some ok.variant) #[v]

/-- The payload type of an IO result type (`EST.Out.ok`'s or `ST.Out`'s value). -/
def ioPayloadTy (resTy : RR.Ty) : LowerM RR.Ty := do
  let .named tn := resTy | return RR.Ty.unit
  let some info := (← get).typeInfos[tn]? | return RR.Ty.unit
  let layout := match info.shape with
    | .struct => info.ctors.find? info.ctorOrder[0]!
    | _ => info.ctors.find? ``EST.Out.ok
  match layout.bind (·.fields[0]?) with
  | some (some (_, t)) => return t
  | _ => return RR.Ty.unit

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

/-- `Array IO.FS.DirEntry` from a directory and the runtime's entry names. -/
def dirEntriesOf (arrTy : RR.Ty) (root names : RR.Expr) : LowerM RR.Expr := do
  let some repr ← arrayRepr? arrTy | throwError "lean2rr: bad directory entry array {arrTy.render}"
  let .named en := repr.value | throwError "lean2rr: bad directory entry type"
  let name := s!"l2r_dir_entries_{en}"
  unless (← get).fns.any (fun | .fn n .. => n == name | _ => false) do
    let u64 := RR.Ty.named "u64"
    let entry ← ctorValue repr.value ``IO.FS.DirEntry.mk
      #[.var "root", .call "l2r_array_get" #[.named "LStr"] #[.var "names", .var "i"]]
    let body : RR.Block := .ofExpr <| .ite (.atom "i < n")
      ⟨#[("one", some u64, .atom "1"), ("e", some repr.storage, repr.store entry)],
        .call (name ++ "_go") #[] #[.var "root", .var "names", .atom "i + one", .var "n",
          repr.call "push" #[.var "acc", .var "e"]]⟩
      (.ofExpr (.var "acc"))
    let strs := RR.Ty.app "RVec" #[.named "LStr"]
    let entry' : RR.Block := ⟨#[("n", some u64, .call "l2r_array_size" #[.named "LStr"] #[.var "names"]),
        ("zero", some u64, .atom "0")],
      .call (name ++ "_go") #[] #[.var "root", .var "names", .var "zero", .var "n", repr.call "empty" #[]]⟩
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
its `IO.Error` field. -/
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
  let (k, errno, fname, details) := ("ek", "ee", "ef", "ed")
  let mut mk : RR.Expr := .call "l2r_unreachable" #[errTy] #[]
  for i in [:(← read).ioErrorBuilders.size] do
    let j := (← read).ioErrorBuilders.size - 1 - i
    let some inst := (← read).ioErrorBuilders[j]! | continue
    let callee ← calleeOf inst
    let .code fn ps _ := callee | continue
    let call := if ps.size == 3 then RR.Expr.call fn #[] #[.var fname, .var errno, .var details]
      else if ps.size == 2 then RR.Expr.call fn #[] #[.var errno, .var details]
      else RR.Expr.call fn #[] #[.var details]
    let kj ← fresh "kj"
    mk := .block ⟨#[(kj, some (.named "u32"), .atom (toString j))],
      .ite (.atom s!"{k} == {kj}") (.ofExpr call) (.ofExpr mk)⟩
  let errVal := RR.Expr.ctor rn (some errL.variant) #[mk]
  return RR.Expr.lam k (.named "u32") <| .ofExpr <| .lam errno (.named "u32") <| .ofExpr <|
    .lam fname (.named "LStr") <| .ofExpr <| .lam details (.named "LStr") (.ofExpr errVal)

/-- `l2r_io_finish(v, ok, err)`: the outcome of a fallible runtime primitive
(result `v : primRet`) as the IO result `resTy`: `EST.Out.ok (okOf x)`, or
`EST.Out.error e` with `e` built by Lean's own `IO.Error` builder for the
error kind the runtime reports (as Lean's `decode_io_error`). -/
def ioFinish (v : RR.Expr) (primRet resTy : RR.Ty) (okOf : RR.Expr → LowerM RR.Expr) : LowerM RR.Expr := do
  let x ← fresh "fx"
  let okFn := RR.Expr.lam x primRet (.ofExpr (← wrapIOResult resTy (← okOf (.var x))))
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
  let kind := ioErrorBuilderSyms.idxOf "lean_mk_io_user_error"
  let e ← match (← read).ioErrorBuilders[kind]?.join with
    | some inst => match ← calleeOf inst with
      | .code fn _ _ => pure (RR.Expr.call fn #[] #[← strLit msg])
      | _ => pure (RR.Expr.call "l2r_unreachable" #[errTy] #[])
    | none => pure (RR.Expr.call "l2r_unreachable" #[errTy] #[])
  return .ctor rn (some errL.variant) #[e]

/-- Glue for a fallible IO extern: call the runtime primitive, then
`l2r_io_finish` turns its outcome into `EST.Out.ok payload` or into
`EST.Out.error e`, where `e` is built by Lean's own `IO.Error` builder for
the error kind the runtime reports (as Lean's `decode_io_error`). -/
def fallibleIOGlue (prim : String) (primRet : RR.Ty) (argTys : Array RR.Ty) (args : Array RR.Expr)
    (ret : Expr) (follow : Bool := true) : LowerM RR.Expr := do
  let resTy ← lowerType ret
  let payload ← ioPayloadTy resTy
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
  let finish ← ioFinish (.var v) primRet resTy fun x => do
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
  let (ps, t) := fnChain fty
  return some (fname, ps, t)

/-- Stream field `i` on file descriptor `fd` applied to `args`: the runtime
primitive `l2r_stream_<field>`. Erased and world parameters are not passed
to the primitive. -/
def streamFieldCall (fd : Nat) (i : Nat) (streamTy : RR.Ty) (args : Array RR.Expr) : LowerM RR.Expr := do
  let some (fname, ps, t) ← streamField streamTy i | throwError "lean2rr: bad stream field"
  let passed := (args.zip ps).filterMap fun (a, pt) => if pt == .unit then none else some a
  let prim := s!"l2r_stream_{fname}"
  let call := RR.Expr.call prim #[] (#[.atom (toString fd)] ++ passed)
  let payload ← ioPayloadTy t
  match (← read).preludeRets[prim]? with
  -- Fallible operations report errors (broken pipe, closed stream, wrong
  -- direction) through the runtime's last-error protocol.
  | some primRet =>
    if fname == `isTty then wrapIOResult t call
    else ioFinish call primRet t fun x =>
      if payload == RR.Ty.unit then pure .unitVal else coerce x primRet payload
  | none =>
    -- Primitives with no result return `u64` (Reussir's `unit` is not a value).
    let v ← if payload == RR.Ty.unit then do
        let r ← fresh "r"
        pure (RR.Expr.block ⟨#[(r, some (.named "u64"), call)], .unitVal⟩)
      else pure call
    wrapIOResult t v

/-- A standard stream (`IO.getStdout` & co.) as a Lean `IO.FS.Stream` value:
each field is a function value whose target is `streamFieldCall` (a
nullary variant, so the record is the only allocation). -/
def streamValue (fd : Nat) (streamTy : RR.Ty) : LowerM RR.Expr := do
  let .named sn := streamTy | throwError "lean2rr: bad stream type"
  let fieldNames := getStructureFields (← getEnv) ``IO.FS.Stream
  let mut vals := #[]
  for i in [:fieldNames.size] do
    let some (_, ps, t) ← streamField streamTy i | continue
    let (v, _) ← partValue { id := s!"s{fd}f{i}{sn}", params := ps, ret := t, call := .stream fd i streamTy } #[]
    vals := vals.push v
  return .ctor sn none vals

/-- `l2r_get_std_<fd>()` and `l2r_set_std_<fd>(s)`: the current standard
stream `fd` is kept in a cell slot (built on first use, like Lean's
thread-local streams), which `IO.setStdout` & co. replace, returning the
previous stream. -/
def stdStreamFns (fd : Nat) (streamTy : RR.Ty) : LowerM (String × String) := do
  let getFn := s!"l2r_get_std_{fd}"
  let setFn := s!"l2r_set_std_{fd}"
  if (← get).fns.any (fun | .fn n .. => n == getFn | _ => false) then return (getFn, setFn)
  let base ← match (← get).stdSlots with
    | some b => pure b
    | none => do
      let b := (← get).cafSlots
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
  let some base := (← get).stdSlots | return #[.fn "l2r_std_enter" #[] u64 (zero "z"), .fn "l2r_std_leave" #[] u64 (zero "z")] ++ ifs
  let some st := (← get).stdStreamTy | return #[.fn "l2r_std_enter" #[] u64 (zero "z"), .fn "l2r_std_leave" #[] u64 (zero "z")] ++ ifs
  let mut lets : Array (String × Option RR.Ty × RR.Expr) := #[]
  for fd in [0:3] do
    let slot := RR.Expr.atom (toString (base + fd))
    let dropIt : RR.Block := ⟨#[(s!"s{fd}", some st, .call "l2r_once_take" #[st] #[slot]), (s!"t{fd}", some u64, .atom "0")],
      .var s!"t{fd}"⟩
    lets := lets.push (s!"d{fd}", some u64, .ite (.call "l2r_once_has" #[] #[slot]) dropIt (zero s!"f{fd}"))
  return #[.fn "l2r_std_enter" #[] u64 (.ofExpr (.call "l2r_std_push" #[] #[.atom (toString base)])),
    .fn "l2r_std_leave" #[] u64 ⟨lets, .call "l2r_std_pop" #[] #[.atom (toString base)]⟩] ++ ifs

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
  let (ps, t) := fnChain fty
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
  if (← get).fns.any (fun | .fn n .. => n == name | _ => false) then return some name
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
`go(l, acc)` = `acc` extended with every element via `step(acc, x)`. Cached
by name. -/
def listFold (name : String) (listTy accTy elemTy : RR.Ty) (step : RR.Expr → RR.Expr → RR.Expr) :
    LowerM String := do
  if (← get).fns.any fun | .fn n .. => n == name | _ => false then return name
  let .named lt := listTy | throwError "lean2rr: bad list type"
  let some info := (← get).typeInfos[lt]? | throwError "lean2rr: bad list type"
  let some nil := info.ctors.find? ``List.nil | throwError "lean2rr: bad list type"
  let some cons := info.ctors.find? ``List.cons | throwError "lean2rr: bad list type"
  -- An irrelevant element (a list of types or proofs) has no field; the
  -- step gets its placeholder.
  let headRel := (cons.fields[0]?.join).isSome
  let x ← if headRel then pure (RR.Expr.var "x") else zeroValue elemTy
  let body : RR.Block := .ofExpr (.mtch (.var "l") #[
    { ty := lt, ctor := some nil.variant, binders := #[], body := .ofExpr (.var "acc") },
    { ty := lt, ctor := some cons.variant,
      binders := (cons.place (if headRel then #[.var "x", .var "t"] else #[.var "t"])).map fun
        | .var v => some v | _ => none,
      body := .ofExpr (.call name #[] #[.var "t", step (.var "acc") x]) }])
  modify fun s => { s with fns := s.fns.push (.fn name #[("l", listTy), ("acc", accTy)] accTy body) }
  return name

/-- The generated function performing reference operation `op` (`get`,
`take`, `set`, `swap`, at element type `a`; `addr`) on a reference held in
a `Box`: a match over the reference types the program boxes. Its body is
generated at the end (`finishRefFns`), when they are all known. -/
def refBoxOpFn (op : String) (a : RR.Ty) : LowerM String := do
  let a := if op == "addr" then RR.Ty.named "u64" else a
  unless (← get).refBoxOps.contains (op, a) do
    modify fun s => { s with refBoxOps := s.refBoxOps.push (op, a) }
  return if op == "addr" then "l2r_refbox_addr" else s!"l2r_refbox_{op}_{a.enc}"

/-- The prelude function that stores a value in a reference cell holding
values of Reussir type `e`: `l2r_rc_set`, which releases the old value
after storing the new one, as `lean_st_ref_set` does (code the release
runs, the `sync` dependents of a promise it drops, sees the new value),
through an FFI call that Reussir keeps after the store; `l2r_rc_put`
(released in place) for a value that cannot cross the FFI boundary, a unit
or enumeration value, whose release runs nothing. (A `[value]` structure
with counted members is stored boxed, `.boxed`, in a shared record that
crosses it.) -/
def refSetFn (e : RR.Ty) : LowerM String := do
  return if ← isBoundaryTy e then "l2r_rc_set" else "l2r_rc_put"

/-- Reference operation `op` on a reference `r` whose cell stores elements
of type `e` as `k`, for an operation at element type `a` (values converted
between the two; `none` if they cannot be): `get` (a copy: the cell keeps
its reference), `take` (the value moves out and the cell gets the
placeholder, as `lean_st_ref_take` stores `box(0)`: Lean's `modify` is
take-then-set, so a value only the cell holds stays unshared and is updated
in place), `set` (`u64` result; `refSetFn`), `swap`. -/
def refCellOp (op : String) (r : RR.Expr) (e : RR.Ty) (k : RefKind) (a : RR.Ty) (v : Option RR.Expr) :
    LowerM (Option RR.Expr) := do
  let cell := RR.Expr.field r 0
  let toA (x : RR.Expr) : LowerM (Option RR.Expr) := tryCoerce x e a
  let fam := if k == .int then "intref" else "natref"
  let v' ← match v with
    | some v => tryCoerce v a e
    | none => pure none
  if v.isSome && v'.isNone then return none
  match k, op with
  | .direct, "get" => toA (.call "l2r_rc_get" #[e] #[cell])
  | .direct, "take" => toA (.call "l2r_rc_swap" #[e] #[cell, ← zeroValue e])
  | .direct, "set" => return some (.call (← refSetFn e) #[e] #[cell, v'.get!])
  | .direct, "swap" => toA (.call "l2r_rc_swap" #[e] #[cell, v'.get!])
  | .boxed bn, "get" => toA (.field (.call "l2r_rc_get" #[.named bn] #[cell]) 0)
  | .boxed bn, "take" => toA (.field (.call "l2r_rc_swap" #[.named bn] #[cell, .ctor bn none #[← zeroValue e]]) 0)
  | .boxed bn, "set" => return some (.call "l2r_rc_set" #[.named bn] #[cell, .ctor bn none #[v'.get!]])
  | .boxed bn, "swap" => toA (.field (.call "l2r_rc_swap" #[.named bn] #[cell, .ctor bn none #[v'.get!]]) 0)
  | _, "get" => toA (.call s!"l2r_{fam}_get" #[] #[r])
  | _, "take" => toA (.call s!"l2r_{fam}_swap" #[] #[r, ← zeroValue e])
  | _, "set" => return some (.call s!"l2r_{fam}_set" #[] #[r, v'.get!])
  | _, "swap" => toA (.call s!"l2r_{fam}_swap" #[] #[r, v'.get!])
  | _, _ => return none

/-- Glue for `ST.Ref` operations (translation plan §5.1). A reference whose
contents have Reussir type `e` is a generated record holding a Reussir
cell, `L2RRefN(Cell<e>)` (`refType`): two allocations per reference (the
record and the cell), the value stored in its own representation.
`ST.Prim.mkRef` at element type `α` creates one at `⟦α⟧` (`Box` for
uniform code, at `α = lcAny`). Lean's mono phase types every reference
`lcAny`, so a reference travels in a `Box`
except where Stage 3 typed its binders (`typedRef`, §4). An operation on a
typed handle accesses its cell directly, converting between the cell's
element type and the operation's (they differ when uniform code works on a
typed reference or the reverse); on a handle in a `Box`, it calls a
generated dispatch over the reference types that are ever boxed
(`refBoxOpFn`). So all aliases of a reference share its one cell, whatever
representation they see it at. `argTys` are the Reussir types of `args`
(the handles' own, for direct calls). -/
def refGlue (orig : Name) (typeArgs : Array Expr) (params : Array Expr) (ret : Expr)
    (args : Array RR.Expr) (argTys : Array RR.Ty) : LowerM (Option RR.Expr) := do
  let some α := typeArgs[1]? | return none
  let a ← lowerType (← toMonoTypeKeep α)
  let resTy ← lowerType ret
  let payload ← ioPayloadTy resTy
  let tyOf (i : Nat) : LowerM RR.Ty := do
    match argTys[i]? with
    | some t => pure t
    | none => lowerType params[i]!
  let value (i : Nat) : LowerM RR.Expr := do coerce args[i]! (← tyOf i) a
  -- Operation `op` on handle `i` (with value `v`): its result at `a` (`u64`
  -- for `set`).
  let onHandle (op : String) (i : Nat) (v : Option RR.Expr) : LowerM RR.Expr := do
    let ht ← tyOf i
    if let some (e, k) ← refElem? ht then
      let resT := if op == "set" then RR.Ty.named "u64" else a
      let (pre, h) ← match args[i]! with
        | .var x => pure (#[], RR.Expr.var x)
        | x => do
          let n ← fresh "rh"
          pure (#[(n, some ht, x)], RR.Expr.var n)
      let r ← match ← refCellOp op h e k a v with
        | some r => pure r
        | none => coerce (.call "l2r_internal_panic_at" #[e] #[.atom "0"]) e resT
      return if pre.isEmpty then r else .block ⟨pre, r⟩
    let h ← coerce args[i]! ht RR.Ty.box
    return .call (← refBoxOpFn op a) #[] (#[h] ++ v.toArray)
  let addrOf (i : Nat) : LowerM RR.Expr := do
    let ht ← tyOf i
    if (← refElem? ht).isSome then return .call "l2r_ptr_addr_rec" #[ht] #[args[i]!]
    return .call (← refBoxOpFn "addr" a) #[] #[← coerce args[i]! ht RR.Ty.box]
  match orig with
  | ``ST.Prim.mkRef =>
    let rt ← refType a
    let some (e, k) ← refElem? rt | return none
    let r := refNew rt e k (← value 0)
    return some (← wrapIOResult resTy (← coerce r rt payload))
  | ``ST.Prim.Ref.get =>
    return some (← wrapIOResult resTy (← coerce (← onHandle "get" 0 none) a payload))
  | ``ST.Prim.Ref.take =>
    return some (← wrapIOResult resTy (← coerce (← onHandle "take" 0 none) a payload))
  | ``ST.Prim.Ref.set =>
    let r ← fresh "rs"
    return some (.block ⟨#[(r, some (.named "u64"), ← onHandle "set" 0 (some (← value 1)))],
      ← wrapIOResult resTy .unitVal⟩)
  | ``ST.Prim.Ref.swap =>
    return some (← wrapIOResult resTy (← coerce (← onHandle "swap" 0 (some (← value 1))) a payload))
  | ``ST.Prim.Ref.ptrEq =>
    let (x, y) := (← fresh "ra", ← fresh "ra")
    let u64 := RR.Ty.named "u64"
    return some (← wrapIOResult resTy
      (.block ⟨#[(x, some u64, ← addrOf 0), (y, some u64, ← addrOf 1)], .atom s!"{x} == {y}"⟩))
  | _ => return none

/-- The bodies of the reference dispatch functions (`refBoxOpFn`): one arm
per reference type that is boxed. A `Box` that holds no reference is
unreachable there. -/
def finishRefFns : LowerM Unit := do
  for (op, a) in (← get).refBoxOps do
    let fname := if op == "addr" then "l2r_refbox_addr" else s!"l2r_refbox_{op}_{a.enc}"
    let resT := if op == "set" || op == "addr" then RR.Ty.named "u64" else a
    let mut arms : Array RR.Arm := #[]
    for (vt, vname) in (← get).boxVariants do
      let some (e, k) ← refElem? vt | continue
      let body ← if op == "addr" then pure (some (RR.Expr.call "l2r_ptr_addr_rec" #[vt] #[.var "r"]))
        else refCellOp op (.var "r") e k a (if op == "set" || op == "swap" then some (.var "v") else none)
      let body := body.getD (.call "l2r_unreachable" #[resT] #[])
      arms := arms.push { ty := boxName, ctor := some vname, binders := #[some "r"], body := .ofExpr body }
    arms := arms.push { ty := boxName, ctor := none, binders := #[], body := .ofExpr (.call "l2r_unreachable" #[resT] #[]) }
    let params := #[("b", RR.Ty.box)] ++ (if op == "set" || op == "swap" then #[("v", a)] else #[])
    let item := RR.Item.fn fname params resT (.ofExpr (.mtch (.var "b") arms))
    modify fun s => { s with fns := (s.fns.filter fun | .fn n .. => n != fname | _ => true).push item }

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
    let pay ← ioPayloadTy rt
    let some v := (← ctorFieldTys pay ``Option.some)[0]? | return none
    let some' ← ctorValue pay ``Option.some #[← coerce (.var "s") (.named "LStr") v]
    let r := RR.Expr.call "l2r_io_getenv_with" #[pay]
      #[name, ← ctorValue pay ``Option.none #[], lam "s" (.named "LStr") some']
    return some (← wrapIOResult rt r)
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
