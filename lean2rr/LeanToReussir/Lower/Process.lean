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
element `x` of array `src` (at the source array's element type) to `f x`.
Cached by name. -/
def arrayMapFn (name : String) (srcTy dstElem : RR.Ty) (f : RR.Expr → LowerM RR.Expr) : LowerM String := do
  if (← hasFn name) then return name
  let some se := arrayElem? srcTy | throwError "lean2rr: bad array type {srcTy.render}"
  let dstTy := RR.Ty.app "RVec" #[dstElem]
  let u64 := RR.Ty.named "u64"
  let go := name ++ "_go"
  let y ← f (.var "x")
  let loop : RR.Block := .ofExpr <| .ite (.atom "i < n")
    ⟨#[("one", some u64, .atom "1"), ("x", some se, arrayCall se "get" #[.var "src", .var "i"]),
        ("y", some dstElem, y)],
      .call go #[] #[.var "src", .atom "i + one", .var "n",
        .call "l2r_array_push" #[dstElem] #[.var "acc", .var "y"]]⟩
    (.ofExpr (.var "acc"))
  let entry : RR.Block := ⟨#[("n", some u64, arrayCall se "size" #[.var "src"]), ("zero", some u64, .atom "0")],
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
when `modes` is given). With `output? := some (input, hasInput)`, the call
is `l2r_proc_output`'s instead (`IO.Process.output`: no modes; the input
string and whether there is one after `setsid`), and the last binding is
its exit code. -/
def spawnCall (sa : RR.Expr) (saTy : RR.Ty) (modes : Option Nat)
    (output? : Option (RR.Expr × RR.Expr) := none) :
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
  match modes, output? with
  | _, some _ => pure ()
  | some m, none =>
    let v ← fresh "pm"
    lets := lets.push (v, some (.named "u32"), .atom (toString m))
    modesE := .var v
  | none, none =>
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
  -- `args : Array String`: the one array type (`RVec<Box>`), passed as it
  -- is; the runtime reads each boxed string in place (`any::str_ref`).
  let (argv, argvT, argvE) ← field 2 (some (.app "RVec" #[RR.Ty.box])) "pargs"
  let (co, coT, coE) ← field 3 none "pco"
  let cd ← fresh "pcd"
  let ch ← fresh "pch"
  lets := lets ++ #[(cmd, some cmdT, cmdE), (argv, some argvT, argvE), (co, some coT, coE),
    (cd, some str, ← optionCases (.var co) coT (fun v vt => coerce v vt str) (← strLit "")),
    (ch, some .bool, ← optionCases (.var co) coT (fun _ _ => pure (.atom "true")) (.atom "false"))]
  -- `env : Array (String × Option String)`.
  let (en, enT, enE) ← field 4 none "pen"
  let some ee := arrayElem? enT | throwError "lean2rr: bad IO.Process.SpawnArgs.env type {enT.render}"
  let tag := enT.enc
  -- An element: a pair (in a `Box`), whose value is an `Option String` (in
  -- the pair's `Box` field).
  let strE := mkConst ``String
  let pairTy ← lowerType (mkApp2 (mkConst ``Prod [levelZero, levelZero]) strE
    (mkApp (mkConst ``Option [levelZero]) strE))
  let optTy ← lowerType (mkApp (mkConst ``Option [levelZero]) strE)
  let pairOf (x : RR.Expr) (k : RR.Expr → LowerM RR.Expr) : LowerM RR.Expr := do
    let p ← fresh "pp"
    return .block ⟨#[(p, some pairTy, ← coerce x ee pairTy)], ← k (.var p)⟩
  let valueOf (x : RR.Expr) (onSome : RR.Expr → RR.Ty → LowerM RR.Expr) (onNone : RR.Expr) : LowerM RR.Expr := do
    pairOf x fun p => do
      let (e, t) ← structField pairTy p 1
      let o ← fresh "po"
      return .block ⟨#[(o, some optTy, ← coerce e t optTy)], ← optionCases (.var o) optTy onSome onNone⟩
  let namesFn ← arrayMapFn s!"l2r_proc_env_names_{tag}" enT str fun x => do
    pairOf x fun p => do
      let (e, t) ← structField pairTy p 0
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
    (pid, some (.named "u32"), match output? with
      | some (input, has) => .call "l2r_proc_output" #[] #[.var cmd, .var argv, .var cd, .var ch,
          .var names, .var values, .var set, .var inh, .var ss, input, has]
      | none => .call "l2r_proc_spawn" #[] #[.var cmd, .var argv, .var cd, .var ch,
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
  let borrowing (c : RR.Expr) (ct : RR.Ty) (prim : RR.Expr) (primRet resTy payTy : RR.Ty)
      (okOf : RR.Expr → LowerM RR.Expr) : LowerM RR.Expr := do
    let r ← fresh "pr"
    let res ← fresh "pres"
    let d ← fresh "pd"
    return .block ⟨#[(r, some primRet, prim), (res, some resTy, ← ioFinish (.var r) primRet resTy payTy okOf),
      (d, some .unit, .call "lean_void_mk" #[ct] #[c])], .var res⟩
  match orig with
  | ``IO.Process.spawn =>
    let resTy ← lowerType ret
    let childTy ← ioPayloadType ret
    let saTy ← lowerType params[0]!
    return some (← withVar "sa" saTy args[0]! fun sa => do
      let (lets, pid, ss, idx) ← spawnCall sa saTy none
      return .block ⟨lets, ← ioFinish pid u32 resTy childTy fun x => spawnedChild childTy idx x ss⟩)
  | ``IO.Process.Child.wait =>
    let resTy ← lowerType ret
    let pay ← ioPayloadType ret
    return some (← childArg fun c ct => do
      let (pid, _) ← structField ct c 3
      borrowing c ct (.call "l2r_proc_wait" #[] #[pid]) u32 resTy pay fun x => coerce x u32 pay)
  | ``IO.Process.Child.tryWait =>
    let resTy ← lowerType ret
    let pay ← ioPayloadType ret
    let some vt := (← ctorFieldTys pay ``Option.some)[0]? | return none
    return some (← childArg fun c ct => do
      let (pid, _) ← structField ct c 3
      -- `(1 << 32) | code` once the child has exited, 0 while it runs.
      borrowing c ct (.call "l2r_proc_try_wait" #[] #[pid]) u64 resTy pay fun x => do
        let z ← fresh "pz"
        let code ← coerce (.atom s!"({x.render 0} as u32)") u32 vt
        return .block ⟨#[(z, some u64, .atom "0")], .ite (.atom s!"{x.render 0} == {z}")
          (.ofExpr (← ctorValue pay ``Option.none #[])) (.ofExpr (← ctorValue pay ``Option.some #[code]))⟩)
  | ``IO.Process.Child.kill =>
    let resTy ← lowerType ret
    return some (← childArg fun c ct => do
      let (pid, _) ← structField ct c 3
      let (ss, _) ← structField ct c 4
      borrowing c ct (.call "l2r_proc_kill" #[] #[pid, ss]) u64 resTy .unit fun _ => pure .unitVal)
  | ``IO.Process.Child.pid =>
    let rt ← lowerType ret
    return some (← childArg fun c ct => do
      let (pid, _) ← structField ct c 3
      coerce pid u32 rt)
  | ``IO.Process.Child.takeStdin =>
    -- `(stdin, child')`: the new child has a unit stdin (`box(0)`) and the
    -- other fields, the pid and the `setsid` flag included.
    let resTy ← lowerType ret
    let pay ← ioPayloadType ret
    let tys ← ctorFieldTys pay ``Prod.mk
    let some fstField := tys[0]? | return none
    let some newField := tys[1]? | return none
    -- The pair's components' own types (its fields are `Box`es).
    let some pe := ioPayloadExpr? ret | return none
    unless pe.isAppOfArity ``Prod 2 do return none
    let fstTy ← lowerType pe.appFn!.appArg!
    let newTy ← lowerType pe.appArg!
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
      let child ← ctorValue newTy cn vals
      wrapIOResult resTy (← ctorValue pay ``Prod.mk #[← coerce fst fstTy fstField, ← coerce child newTy newField]) pay)
  | _ => return none

/-- The body of `IO.Process.output args input?`'s declaration (parameters
`ps`, result `ret`, of Lean type `retE`), in place of Lean's, which reads
stdout in a dedicated task while it reads stderr (lean-runtime's scheduler
runs that too: its pipe reads cooperate). The runtime's `l2r_proc_output`
(lean-runtime's `io::process::output`) reads both pipes together, and
writes a large input while it reads them, where Lean's definition writes
all of it first and then waits for good on a child that fills a pipe
(LB-40). Otherwise it does what Lean's definition does: spawn with stdout
and stderr piped, stdin null, or piped when `input?` is `some s` (then `s`
is written and flushed, and the handle closed); read both pipes to end of
file together; `readToEnd`'s UTF-8 check of stderr; `wait`; the same check
of stdout; errors in that order. On success the outputs are
`l2r_proc_output_str(1)` and `(2)`. -/
def processOutputBody (ps : Array (String × RR.Ty)) (ret : RR.Ty) (retE : Expr) : LowerM RR.Block := do
  let some (sa, saTy) := ps[0]? | throwError "lean2rr: bad IO.Process.output signature"
  let some (inp, inTy) := ps[1]? | throwError "lean2rr: bad IO.Process.output signature"
  let u32 := RR.Ty.named "u32"
  let str := RR.Ty.named "LStr"
  let outTy ← ioPayloadType retE
  let (_, oc, _) ← structLayoutOf outTy
  let outFs ← ctorFieldTys outTy oc
  unless outFs.size == 3 do throwError "lean2rr: bad IO.Process.Output type {outTy.render}"
  let pin ← fresh "pin"
  let phas ← fresh "phas"
  let inLets : Array (String × Option RR.Ty × RR.Expr) := #[
    (pin, some str, ← optionCases (.var inp) inTy (fun v vt => coerce v vt str) (← strLit "")),
    (phas, some .bool, ← optionCases (.var inp) inTy (fun _ _ => pure (.atom "true")) (.atom "false"))]
  let (lets, code, _, _) ← spawnCall (.var sa) saTy none (output? := some (.var pin, .var phas))
  let outStr (k : Nat) : RR.Expr := .call "l2r_proc_output_str" #[] #[.atom (toString k)]
  let output ← ctorValue outTy oc #[← coerce code u32 outFs[0]!,
    ← coerce (outStr 1) str outFs[1]!, ← coerce (outStr 2) str outFs[2]!]
  return ⟨inLets ++ lets, ← ioCheck ret (.ofExpr (← wrapIOResult ret output outTy))⟩

end LeanToReussir
