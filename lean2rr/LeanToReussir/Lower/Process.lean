import LeanToReussir.Lower.LazyGlue

/-! # Child processes

Glue over the runtime's `l2r_proc_*` primitives (runtime/README.md, "Child
processes"; translation plan §5.8). A `Child` is a structure of its three
stream fields, `lcAny` in mono code and so `Box` (a boxed `LHandle` for a
piped stream, else a boxed unit, as natively `box(0)`), and two hidden
fields: the pid and whether the child was spawned with `setsid`
(`nominalType`). Fallible operations report errors through the runtime's
last-error protocol, as native Lean's `decode_io_error(errno, nullptr)`. -/

namespace LeanToReussir
open Lean Compiler LCNF

/-- The name, constructor and constructor layout of generated structure
type `t`. -/
def structLayoutOf (t : RR.Ty) : LowerM (String × Name × CtorLayout) := do
  let .named tn := t | throwError "lean2rr: expected a structure, got {t.render}"
  let some info := (← get).typeInfos[tn]? | throwError "lean2rr: expected a structure, got {tn}"
  let some c := info.ctorOrder[0]? | throwError "lean2rr: {tn} has no constructor"
  let some layout := info.ctors.find? c | throwError "lean2rr: {tn} has no constructor"
  unless info.shape == .struct do throwError "lean2rr: {tn} is not a structure"
  return (tn, c, layout)

/-- Field `i` (by Lean index; hidden fields follow the Lean ones) of the
structure value `x : t`, and its type. -/
def structField (t : RR.Ty) (x : RR.Expr) (i : Nat) : LowerM (RR.Expr × RR.Ty) := do
  let (tn, _, layout) ← structLayoutOf t
  match layout.fields[i]? with
  | some (some (p, ft)) => return (.field x p, ft)
  | _ => throwError "lean2rr: structure {tn} has no field {i}"

/-- `match o { some(v) => onSome v, _ => onNone }` for a variable `o` of
generated type `ot = Option α`; `onSome` receives the payload and its type. -/
def optionCases (o : RR.Expr) (ot : RR.Ty) (onSome : RR.Expr → RR.Ty → LowerM RR.Expr)
    (onNone : RR.Expr) : LowerM RR.Expr := do
  let .named on := ot | throwError "lean2rr: expected an Option, got {ot.render}"
  let some info := (← get).typeInfos[on]? | throwError "lean2rr: expected an Option, got {on}"
  let some sl := info.ctors.find? ``Option.some | throwError "lean2rr: expected an Option, got {on}"
  let some (some (_, vt)) := sl.fields[0]? | throwError "lean2rr: expected an Option, got {on}"
  let v ← fresh "ov"
  return .mtch o #[
    { ty := on, ctor := some sl.variant, binders := #[some v], body := .ofExpr (← onSome (.var v) vt) },
    { ty := on, ctor := none, binders := #[], body := .ofExpr onNone }]

/-- A generated function `name(src : srcTy) -> RVec<dstElem>` mapping each
element `x` of array `src` to `f x` (`dstElem` is stored as it is: a string
or `bool`). Cached by name. -/
def arrayMapFn (name : String) (srcTy dstElem : RR.Ty) (f : RR.Expr → LowerM RR.Expr) : LowerM String := do
  if (← get).fns.any (fun | .fn n .. => n == name | _ => false) then return name
  let some sr ← arrayRepr? srcTy | throwError "lean2rr: bad array type {srcTy.render}"
  let dstTy := RR.Ty.app "RVec" #[dstElem]
  let u64 := RR.Ty.named "u64"
  let go := name ++ "_go"
  let y ← f (.var "x")
  let loop : RR.Block := .ofExpr <| .ite (.atom "i < n")
    ⟨#[("one", some u64, .atom "1"), ("x", some sr.value, sr.load (sr.call "get" #[.var "src", .var "i"])),
        ("y", some dstElem, y)],
      .call go #[] #[.var "src", .atom "i + one", .var "n",
        .call "l2r_array_push" #[dstElem] #[.var "acc", .var "y"]]⟩
    (.ofExpr (.var "acc"))
  let entry : RR.Block := ⟨#[("n", some u64, sr.call "size" #[.var "src"]), ("zero", some u64, .atom "0")],
    .call go #[] #[.var "src", .var "zero", .var "n", .call "l2r_array_empty" #[dstElem] #[]]⟩
  modify fun s => { s with fns := s.fns ++ #[
    .fn go #[("src", srcTy), ("i", u64), ("n", u64), ("acc", dstTy)] dstTy loop,
    .fn name #[("src", srcTy)] dstTy entry] }
  return name

/-- The call of `l2r_proc_spawn` for the `SpawnArgs` value `sa : saTy` (a
variable), flattened as the primitive takes it: the command and arguments,
the working directory (`""` and `false` for `none`), the environment
changes as parallel arrays (names, values, whether the value is `some`),
the stdio modes as `stdin | stdout << 8 | stderr << 16` in
`IO.Process.Stdio` constructor indices (`modes`, or else `sa`'s),
`inheritEnv` and `setsid`. Returns the bindings (the last one binds the
pid), the pid, the `setsid` flag, and the three mode indices (`u64`; none
when `modes` is given). -/
def spawnCall (sa : RR.Expr) (saTy : RR.Ty) (modes : Option Nat) :
    LowerM (Array (String × Option RR.Ty × RR.Expr) × RR.Expr × RR.Expr × Array RR.Expr) := do
  let u64 := RR.Ty.named "u64"
  let str := RR.Ty.named "LStr"
  let strs := RR.Ty.app "RVec" #[str]
  -- Field `i` of `sa`, converted to `want` if given: a fresh name, its
  -- type and its value.
  let field (i : Nat) (want : Option RR.Ty) (pre : String) : LowerM (String × RR.Ty × RR.Expr) := do
    let (e, t) ← structField saTy sa i
    let v ← fresh pre
    match want with
    | some w => return (v, w, ← coerce e t w)
    | none => return (v, t, e)
  let mut lets : Array (String × Option RR.Ty × RR.Expr) := #[]
  let mut idx : Array RR.Expr := #[]
  let mut modesE : RR.Expr := .atom "0"
  match modes with
  | some m =>
    let v ← fresh "pm"
    lets := lets.push (v, some (.named "u32"), .atom (toString m))
    modesE := .var v
  | none =>
    let (cfg, cfgTy, cfgE) ← field 0 none "pc"
    lets := lets.push (cfg, some cfgTy, cfgE)
    for k in [0:3] do
      let (se, st) ← structField cfgTy (.var cfg) k
      let .named stn := st | throwError "lean2rr: bad IO.Process.StdioConfig type {cfgTy.render}"
      let v ← fresh "pm"
      lets := lets.push (v, some u64, .call (← enumIndexFn stn) #[] #[se])
      idx := idx.push (.var v)
    let k8 ← fresh "pk"
    let k16 ← fresh "pk"
    let m ← fresh "pm"
    let i (j : Nat) := (idx[j]!).render 0
    lets := lets ++ #[(k8, some u64, .atom "256"), (k16, some u64, .atom "65536"),
      (m, some u64, .atom s!"{i 0} + ({i 1} * {k8}) + ({i 2} * {k16})")]
    modesE := .atom s!"({m} as u32)"
  let (cmd, cmdT, cmdE) ← field 1 (some str) "pcmd"
  let (argv, argvT, argvE) ← field 2 (some strs) "pargs"
  let (co, coT, coE) ← field 3 none "pco"
  let cd ← fresh "pcd"
  let ch ← fresh "pch"
  lets := lets ++ #[(cmd, some cmdT, cmdE), (argv, some argvT, argvE), (co, some coT, coE),
    (cd, some str, ← optionCases (.var co) coT (fun v vt => coerce v vt str) (← strLit "")),
    (ch, some .bool, ← optionCases (.var co) coT (fun _ _ => pure (.atom "true")) (.atom "false"))]
  -- `env : Array (String × Option String)`.
  let (en, enT, enE) ← field 4 none "pen"
  let some er ← arrayRepr? enT | throwError "lean2rr: bad IO.Process.SpawnArgs.env type {enT.render}"
  let pairTy := er.value
  let tag := enT.enc
  let valueOf (x : RR.Expr) (onSome : RR.Expr → RR.Ty → LowerM RR.Expr) (onNone : RR.Expr) : LowerM RR.Expr := do
    let (e, t) ← structField pairTy x 1
    let o ← fresh "po"
    return .block ⟨#[(o, some t, e)], ← optionCases (.var o) t onSome onNone⟩
  let namesFn ← arrayMapFn s!"l2r_proc_env_names_{tag}" enT str fun x => do
    let (e, t) ← structField pairTy x 0
    coerce e t str
  let valuesFn ← arrayMapFn s!"l2r_proc_env_values_{tag}" enT str fun x => do
    valueOf x (fun v vt => coerce v vt str) (← strLit "")
  let setFn ← arrayMapFn s!"l2r_proc_env_set_{tag}" enT .bool fun x => do
    valueOf x (fun _ _ => pure (.atom "true")) (.atom "false")
  let names ← fresh "pnames"
  let values ← fresh "pvals"
  let set ← fresh "pset"
  let (inh, inhT, inhE) ← field 5 (some .bool) "pinh"
  let (ss, ssT, ssE) ← field 6 (some .bool) "pss"
  let pid ← fresh "ppid"
  lets := lets ++ #[(en, some enT, enE), (names, some strs, .call namesFn #[] #[.var en]),
    (values, some strs, .call valuesFn #[] #[.var en]),
    (set, some (.app "RVec" #[.bool]), .call setFn #[] #[.var en]),
    (inh, some inhT, inhE), (ss, some ssT, ssE),
    (pid, some (.named "u32"), .call "l2r_proc_spawn" #[] #[.var cmd, .var argv, .var cd, .var ch,
      .var names, .var values, .var set, modesE, .var inh, .var ss])]
  return (lets, .var pid, .var ss, idx)

/-- The `Child` (of generated type `childTy`) of the child just spawned: its
streams (stream `k`'s parent end `l2r_proc_end(k)`, boxed, when its mode
index `idx[k]` is `piped`, else a boxed unit, as natively `box(0)`), its
pid and its `setsid` flag. -/
def spawnedChild (childTy : RR.Ty) (idx : Array RR.Expr) (pid ss : RR.Expr) : LowerM RR.Expr := do
  let (_, c, layout) ← structLayoutOf childTy
  let mut vals := #[]
  for k in [0:3] do
    let some (some (_, ft)) := layout.fields[k]? | throwError "lean2rr: bad IO.Process.Child type"
    let z ← fresh "pz"
    let piped ← coerce (.call "l2r_proc_end" #[] #[.atom (toString k)]) (.named "LHandle") ft
    let other ← coerce .unitVal .unit ft
    vals := vals.push (.block ⟨#[(z, some (.named "u64"), .atom "0")],
      .ite (.atom s!"{(idx[k]!).render 0} == {z}") (.ofExpr piped) (.ofExpr other)⟩)
  ctorValue childTy c (vals ++ #[pid, ss])

/-- Glue for the child-process externs (`IO.Process.spawn` and the `Child`
operations); `none` for other externs. `args` are the relevant arguments at
the Reussir types of `params`: the `SpawnArgs` and the world for `spawn`;
for the `Child` operations the configuration (unused), the child and, but
for `pid`, the world. -/
def processExtern (orig : Name) (params : Array Expr) (ret : Expr) (args : Array RR.Expr) :
    LowerM (Option RR.Expr) := do
  unless orig ∈ [``IO.Process.spawn, ``IO.Process.Child.wait, ``IO.Process.Child.tryWait,
      ``IO.Process.Child.kill, ``IO.Process.Child.pid, ``IO.Process.Child.takeStdin] do return none
  let u32 := RR.Ty.named "u32"
  let u64 := RR.Ty.named "u64"
  let n := args.size
  if n == 0 then return none
  -- The child: the last argument of `pid`, the one before the world otherwise.
  let ci := if orig == ``IO.Process.Child.pid then n - 1 else n - 2
  let childArg (k : RR.Expr → RR.Ty → LowerM RR.Expr) : LowerM RR.Expr := do
    let ct ← lowerType params[ci]!
    withVar "ch" ct args[ci]! fun c => k c ct
  -- `wait`, `tryWait` and `kill` borrow the child (`@&`): natively it is
  -- released after the call, by its last user, so its pipes stay open
  -- while the call runs. Here the glue holds it until the result is built.
  let borrowing (c : RR.Expr) (ct : RR.Ty) (prim : RR.Expr) (primRet resTy : RR.Ty)
      (okOf : RR.Expr → LowerM RR.Expr) : LowerM RR.Expr := do
    let r ← fresh "pr"
    let res ← fresh "pres"
    let d ← fresh "pd"
    return .block ⟨#[(r, some primRet, prim), (res, some resTy, ← ioFinish (.var r) primRet resTy okOf),
      (d, some .unit, .call "lean_void_mk" #[ct] #[c])], .var res⟩
  match orig with
  | ``IO.Process.spawn =>
    let resTy ← lowerType ret
    let childTy ← ioPayloadTy resTy
    let saTy ← lowerType params[0]!
    return some (← withVar "sa" saTy args[0]! fun sa => do
      let (lets, pid, ss, idx) ← spawnCall sa saTy none
      return .block ⟨lets, ← ioFinish pid u32 resTy fun x => spawnedChild childTy idx x ss⟩)
  | ``IO.Process.Child.wait =>
    let resTy ← lowerType ret
    let pay ← ioPayloadTy resTy
    return some (← childArg fun c ct => do
      let (pid, _) ← structField ct c 3
      borrowing c ct (.call "l2r_proc_wait" #[] #[pid]) u32 resTy fun x => coerce x u32 pay)
  | ``IO.Process.Child.tryWait =>
    let resTy ← lowerType ret
    let pay ← ioPayloadTy resTy
    let some vt := (← ctorFieldTys pay ``Option.some)[0]? | return none
    return some (← childArg fun c ct => do
      let (pid, _) ← structField ct c 3
      -- `(1 << 32) | code` once the child has exited, 0 while it runs.
      borrowing c ct (.call "l2r_proc_try_wait" #[] #[pid]) u64 resTy fun x => do
        let z ← fresh "pz"
        let code ← coerce (.atom s!"({x.render 0} as u32)") u32 vt
        return .block ⟨#[(z, some u64, .atom "0")], .ite (.atom s!"{x.render 0} == {z}")
          (.ofExpr (← ctorValue pay ``Option.none #[])) (.ofExpr (← ctorValue pay ``Option.some #[code]))⟩)
  | ``IO.Process.Child.kill =>
    let resTy ← lowerType ret
    return some (← childArg fun c ct => do
      let (pid, _) ← structField ct c 3
      let (ss, _) ← structField ct c 4
      borrowing c ct (.call "l2r_proc_kill" #[] #[pid, ss]) u64 resTy fun _ => pure .unitVal)
  | ``IO.Process.Child.pid =>
    let rt ← lowerType ret
    return some (← childArg fun c ct => do
      let (pid, _) ← structField ct c 3
      coerce pid u32 rt)
  | ``IO.Process.Child.takeStdin =>
    -- `(stdin, child')`: the new child has a unit stdin (`box(0)`) and the
    -- other fields, the pid and the `setsid` flag included.
    let resTy ← lowerType ret
    let pay ← ioPayloadTy resTy
    let tys ← ctorFieldTys pay ``Prod.mk
    let some fstTy := tys[0]? | return none
    let some newTy := tys[1]? | return none
    return some (← childArg fun c ct => do
      let (s0, t0) ← structField ct c 0
      let fst ← if fstTy == .unit then pure .unitVal else coerce s0 t0 fstTy
      let (_, cn, nl) ← structLayoutOf newTy
      let mut vals := #[]
      for h : i in [:nl.fields.size] do
        let some (_, dt) := nl.fields[i] | continue
        if i == 0 then vals := vals.push (← coerce .unitVal .unit dt)
        else
          let (e, t) ← structField ct c i
          vals := vals.push (← coerce e t dt)
      wrapIOResult resTy (← ctorValue pay ``Prod.mk #[fst, ← ctorValue newTy cn vals]))
  | _ => return none

/-- The body of `IO.Process.output args input?`'s declaration (parameters
`ps`, result `ret`), in place of Lean's: that one reads stdout in a
dedicated task while it reads stderr, and lean2rr's tasks are deferred, so
a child writing more than a pipe holds to stdout before closing stderr would
block forever.
The glue follows native order: spawn with stdout and stderr piped, stdin
null, or piped when `input?` is `some s` (then `s` is written and flushed,
and the handle released and so closed, as `takeStdin`, `putStr` and
`flush` do natively); read both pipes to end of file together
(`l2r_proc_drain`); `readToEnd`'s UTF-8 check of stderr; `wait`; the same
check of stdout. Errors are native's, in the same order, but a non-UTF-8
stderr is reported once both pipes are at end of file (natively as soon as
stderr is), and a read error on either pipe at once (natively a stdout read
error after `wait`). -/
def processOutputBody (ps : Array (String × RR.Ty)) (ret : RR.Ty) : LowerM RR.Block := do
  let some (sa, saTy) := ps[0]? | throwError "lean2rr: bad IO.Process.output signature"
  let some (inp, inTy) := ps[1]? | throwError "lean2rr: bad IO.Process.output signature"
  let u32 := RR.Ty.named "u32"
  let u64 := RR.Ty.named "u64"
  let str := RR.Ty.named "LStr"
  let hTy := RR.Ty.named "LHandle"
  let bytes := RR.Ty.app "RVec" #[.named "u8"]
  let outTy ← ioPayloadTy ret
  let (_, oc, _) ← structLayoutOf outTy
  let outFs ← ctorFieldTys outTy oc
  unless outFs.size == 3 do throwError "lean2rr: bad IO.Process.Output type {outTy.render}"
  let utf8Err ← ioUserError ret "Tried to read from handle containing non UTF-8 data."
  -- Once the child runs: `rest(pid, stdout, stderr)`.
  let rest ← fresh "l2r_proc_output_rest_"
  let output ← ctorValue outTy oc #[← coerce (.var "code") u32 outFs[0]!,
    ← coerce (.var "os") str outFs[1]!, ← coerce (.var "es") str outFs[2]!]
  let afterWait : RR.Block := .ofExpr (.ite (.call "lean_string_validate_utf8" #[] #[.var "ob"])
    ⟨#[("os", some str, .call "lean_string_from_utf8_unchecked" #[] #[.var "ob"])], ← wrapIOResult ret output⟩
    (.ofExpr utf8Err))
  let afterDrain : RR.Block := ⟨#[("eb", some bytes, .call "l2r_proc_drained_err" #[] #[])],
    .ite (.call "lean_string_validate_utf8" #[] #[.var "eb"])
      ⟨#[("es", some str, .call "lean_string_from_utf8_unchecked" #[] #[.var "eb"]),
         ("code", some u32, .call "l2r_proc_wait" #[] #[.var "pid"])], ← ioCheck ret afterWait⟩
      (.ofExpr utf8Err)⟩
  let restBody : RR.Block :=
    ⟨#[("ob", some bytes, .call "l2r_proc_drain" #[] #[.var "ho", .var "he"])], ← ioCheck ret afterDrain⟩
  modify fun s => { s with fns := s.fns.push (.fn rest #[("pid", u32), ("ho", hTy), ("he", hTy)] ret restBody) }
  let pipeEnd (k : Nat) : RR.Expr := .call "l2r_proc_end" #[] #[.atom (toString k)]
  let spawnWith (modes : Nat) (k : RR.Expr → LowerM RR.Block) : LowerM RR.Expr := do
    let (lets, pid, _, _) ← spawnCall (.var sa) saTy (some modes)
    return .block ⟨lets, ← ioCheck ret (← k pid)⟩
  -- Stream modes: `piped` = 0, `null` = 2 (stdin's is the low byte).
  let noInput ← spawnWith 2 fun pid => do
    let ho ← fresh "ho"
    let he ← fresh "he"
    return ⟨#[(ho, some hTy, pipeEnd 1), (he, some hTy, pipeEnd 2)], .call rest #[] #[pid, .var ho, .var he]⟩
  let withInput (s : RR.Expr) (st : RR.Ty) : LowerM RR.Expr := spawnWith 0 fun pid => do
    let hi ← fresh "hi"
    let ho ← fresh "ho"
    let he ← fresh "he"
    let r1 ← fresh "pr"
    let r2 ← fresh "pr"
    let afterPut : RR.Block := ⟨#[(r2, some u64, .call "l2r_fs_flush" #[] #[.var hi])],
      ← ioCheck ret (.ofExpr (.call rest #[] #[pid, .var ho, .var he]))⟩
    return ⟨#[(hi, some hTy, pipeEnd 0), (ho, some hTy, pipeEnd 1), (he, some hTy, pipeEnd 2),
        (r1, some u64, .call "l2r_fs_put_str" #[] #[.var hi, ← coerce s st str])], ← ioCheck ret afterPut⟩
  return .ofExpr (← optionCases (.var inp) inTy withInput noInput)

end LeanToReussir
