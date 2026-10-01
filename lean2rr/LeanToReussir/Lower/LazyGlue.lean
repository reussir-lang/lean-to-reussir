import LeanToReussir.Lower.Externs

/-! # Thunks and tasks: extern glue

Translation plan §5.14. Thunks are memoized cells. Tasks created after
`main` has started are deferred: they run when they are needed, on the stack
of whoever needs them, or when `main` returns, as Lean's task manager
finishes all queued tasks before the process exits (`leanrt::task` keeps the
queues); a pure task the program drops before it has started never runs. -/

namespace LeanToReussir
open Lean Compiler LCNF

/-- Bind `e : ty` to a fresh variable for `k` (Reussir applies only
variables and call results). -/
def withVar (pre : String) (ty : RR.Ty) (e : RR.Expr) (k : RR.Expr → LowerM RR.Expr) :
    LowerM RR.Expr := do
  match e with
  | .var _ => k e
  | _ =>
    let x ← fresh pre
    return .block ⟨#[(x, some ty, e)], ← k (.var x)⟩

/-- Run the `BaseIO` action `act : actTy` (`L2RUnit -> R` with `R` an
`ST.Out` structure) on the world `w`; its value, converted to `dst`. -/
def runIO (act : RR.Expr) (actTy : RR.Ty) (w : RR.Expr) (dst : RR.Ty) : LowerM RR.Expr := do
  let .fn _ resTy := actTy | throwError "lean2rr: IO action of type {actTy.render}"
  let .named rn := resTy | throwError "lean2rr: IO result of type {resTy.render}"
  let some info := (← get).typeInfos[rn]? | throwError "lean2rr: IO result of type {rn}"
  let some layout := info.ctors.find? info.ctorOrder[0]! | throwError "lean2rr: IO result of type {rn}"
  unless info.shape == .struct do throwError "lean2rr: BaseIO result type {rn} is not a structure"
  let some (some (j, pt)) := layout.fields[0]? | throwError "lean2rr: IO result of type {rn}"
  withVar "act" actTy act fun a => do
    let r ← fresh "io"
    return .block ⟨#[(r, some resTy, ← applyCall a actTy #[w])], ← coerce (.field (.var r) j) pt dst⟩

/-- The state type and value type of a thunk or task of Reussir type `t`. -/
def lazyOf (t : RR.Ty) : LowerM (String × RR.Ty) := do
  match ← lazyOf? t with
  | some (z, _, vt) => return (z, vt)
  | none => throwError "lean2rr: expected a thunk or task, got {t.render}"

/-- `kind` bits of `l2r_task_register` (`leanrt::task::K_PURE`, `K_DEP`). -/
def taskKind (pure dep : Bool) : Nat := (if pure then 1 else 0) + (if dep then 2 else 0)

/-- `l2r_task_defer_S(g, prio, kind)` (IO tasks, `pure = false`) and
`l2r_task_lazy_S(g, prio, kind)` (pure tasks): a new task computing `g(())`
(`bind`: continuing as the task `g(())` yields). During module
initialization Lean has no task manager and runs it at once
(`lean_task_spawn_core`); afterwards it is pending, and the runtime queues
it (`kind`, see `taskKind`: a dependent is queued or made to wait by
`l2r_task_depend_at` instead), or, at priority 2^32-1, has it run now, on
the current thread. -/
def taskNewFn (z : String) (pure : Bool) (bind : Bool := false) : LowerM String := do
  let (_, t) ← lazyInfo z
  let tag ← taskTag z
  let kind := if pure then (if bind then "lazybind" else "lazy") else (if bind then "bind" else "defer")
  let name := s!"l2r_task_{kind}_{z}"
  let get ← lazyGetFn z
  lazyFn name do
    let zt := RR.Ty.named z
    let cellTy := RR.Ty.app "LCell" #[zt]
    let u64 := RR.Ty.named "u64"
    -- `bind`: `g` yields the task this one continues as (`IO.bindTask`).
    let gTy := RR.Ty.fn .unit (if bind then cellTy else t)
    let runNow : RR.Block := ⟨#[("v", some t, .call get #[] #[.var "c"])], .var "c"⟩
    let deferred : RR.Block := ⟨#[
        ("c", some cellTy, .call "l2r_lcell_new" #[zt] #[.ctor z (some (if bind then "bind" else "pending")) #[.var "g"]]),
        ("r", some u64, .call "l2r_task_register" #[zt] #[.var "c", .atom (toString tag), .var "prio", .var "k"]),
        ("one", some u64, .atom "1")], .ite (.atom "r == one") runNow (.ofExpr (.var "c"))⟩
    let call ← applyCall (.var "g") gTy #[.unitVal]
    let force := if bind then RR.Expr.block ⟨#[("t2", some cellTy, call)], .call get #[] #[.var "t2"]⟩ else call
    let eager : RR.Block := ⟨#[("v", some t, force)], lazyDone z (.var "v")⟩
    let body := RR.Expr.ite (.call "l2r_task_deferring" #[] #[]) deferred eager
    return #[.fn name #[("g", gTy), ("prio", u64), ("k", u64)] cellTy (.ofExpr body)]

/-- The runtime's state of task `c` (0 waiting, 1 running, 2 finished). -/
def taskStatus (z : String) (c : RR.Expr) : LowerM RR.Expr := do
  return .call "l2r_task_status_at" #[] #[.call (← taskAddrFn z) #[] #[c]]

/-- Whether task `c` has finished. -/
def taskDone (z : String) (c : RR.Expr) : LowerM RR.Expr := do
  return .block ⟨#[("st", some (.named "u8"), ← taskStatus z c),
    ("fin", some (.named "u8"), .atom "2")], .atom "st == fin"⟩

/-- The value of task or thunk `c : ty`, converted to `dst`. -/
def lazyGet (c : RR.Expr) (ty : RR.Ty) (dst : RR.Ty) : LowerM RR.Expr := do
  let (z, t) ← lazyOf ty
  let get ← lazyGetFn z
  withVar "tk" ty c fun c => coerce (.call get #[] #[c]) t dst

/-- A new task of Reussir type `taskTy` whose value is `body u` (`u` is the
world, for IO tasks); `dep`: a dependent (see `taskNewFn`). -/
def newTask (taskTy : RR.Ty) (pure : Bool) (prio : RR.Expr) (body : RR.Expr → LowerM RR.Expr)
    (dep : Bool := false) : LowerM RR.Expr := do
  let (z, t) ← lazyOf taskTy
  let u ← fresh "w"
  return .call (← taskNewFn z pure) #[] #[rawFnValue (.fn .unit t) u (.ofExpr (← body (.var u))), prio,
    .atom (toString (taskKind pure dep))]

/-- The new dependent task `c : taskTy` (state type `z`) of task `src`
(whose identity function is `srcAddr`), with `sync` (a `Bool` expression):
recorded with `l2r_task_depend_at` (Lean's `add_dep`), and run now if the
runtime says so (`src` finished, priority 2^32-1). -/
def taskDepend (z : String) (taskTy : RR.Ty) (c : RR.Expr) (srcAddr : String) (src sync : RR.Expr) :
    LowerM RR.Block := do
  let get ← lazyGetFn z
  let x ← fresh "tn"
  let dp ← fresh "dp"
  let one ← fresh "one"
  let v ← fresh "tv"
  let (_, t) ← lazyInfo z
  return ⟨#[(x, some taskTy, c),
    (dp, some (.named "u64"), .call "l2r_task_depend_at" #[]
      #[.call srcAddr #[] #[src], .call "l2r_lcell_addr" #[.named z] #[.var x], sync]),
    (one, some (.named "u64"), .atom "1")],
    .ite (.atom s!"{dp} == {one}") ⟨#[(v, some t, .call get #[] #[.var x])], .var x⟩ (.ofExpr (.var x))⟩

/-- `l2r_task_step_S(c)`: run task `c`, handed over by the runtime, as a
worker would: a `bind` task (`IO.bindTask`) only runs `f`
(`taskBindStepFn`): it then finishes or waits for the task `f` returned.
Other tasks run to the end. -/
def taskStepFn (z : String) : LowerM String := do
  let (_, t) ← lazyInfo z
  let get ← lazyGetFn z
  let bindStep ← taskBindStepFn z get
  let name := s!"l2r_task_step_{z}"
  lazyFn name do
    let zt := RR.Ty.named z
    let cellTy := RR.Ty.app "LCell" #[zt]
    let u64 := RR.Ty.named "u64"
    let stepBind : RR.Block := .ofExpr (.mtch (.call "l2r_lcell_swap" #[zt] #[.var "c", .ctor z (some "busy") #[]]) #[
      lazyArm z "bind" #[some "g"] (.ofExpr (.call bindStep #[] #[.var "c", .var "g"])),
      { ty := z, ctor := none, binders := #[], body := .ofExpr (.call "l2r_unreachable" #[u64] #[]) }])
    let body : RR.Block := .ofExpr (.mtch (.call "l2r_lcell_get" #[zt] #[.var "c"]) #[
      lazyArm z "bind" #[none] (.ofExpr (.call (name ++ "_bind") #[] #[.var "c"])),
      { ty := z, ctor := none, binders := #[], body := ⟨#[("v", some t, .call get #[] #[.var "c"]),
          ("z", some u64, .atom "0")], .var "z"⟩ }])
    return #[.fn (name ++ "_bind") #[("c", cellTy)] u64 stepBind, .fn name #[("c", cellTy)] u64 body]

/-- `IO.getTaskState` glue (`leanrt::task::query`): the runtime's answer,
where 3 means the program is polling for a pending task, which then runs
and is reported finished, and 4 that it is polling for an unresolved
promise: queued tasks run until it is resolved or none is left (as workers
would meanwhile), and its state is reported then. -/
def taskStateFn (z : String) (stateTy : RR.Ty) : LowerM String := do
  let name := s!"l2r_task_state_{z}"
  let (_, t) ← lazyInfo z
  let get ← lazyGetFn z
  let addr ← taskAddrFn z
  let v (c : Name) := ctorValue stateTy c #[]
  let waiting ← v ``IO.TaskState.waiting
  let running ← v ``IO.TaskState.running
  let finished ← v ``IO.TaskState.finished
  lazyFn name do
    let zt := RR.Ty.named z
    let u8 := RR.Ty.named "u8"
    let isQ (k : Nat) (yes no : RR.Block) : RR.Block :=
      ⟨#[(s!"k{k}", some u8, .atom (toString k))], .ite (.atom s!"q == k{k}") yes no⟩
    let promise : RR.Block := ⟨#[("fs", some (.named "u64"), .call "l2r_task_force_sources" #[] #[.var "a"]),
        ("st", some u8, .call "l2r_task_status_at" #[] #[.var "a"]), ("fin", some u8, .atom "2")],
      .ite (.atom "st == fin") (.ofExpr finished) (.ofExpr running)⟩
    let body : RR.Block := ⟨#[("a", some (.named "u64"), .call addr #[] #[.var "c"]),
        ("q", some u8, .call "l2r_task_query_at" #[] #[.var "a"])],
      .block (isQ 0 (.ofExpr waiting) (isQ 1 (.ofExpr running) (isQ 2 (.ofExpr finished)
        (isQ 3 ⟨#[("v", some t, .call get #[] #[.var "c"])], finished⟩ promise))))⟩
    return #[.fn name #[("c", .app "LCell" #[zt])] stateTy body]

/-- `IO.waitAny` glue over a list of tasks of type `listTy`: the value of the
first task of the list that has finished; if none has, the first pending
one is run (it finished first), unless it waits for an unresolved promise.
If every task is running (or waits for a promise), the caller waits until
some task finishes (`l2r_task_wait_progress`: other contexts and queued
tasks run meanwhile, as workers would) and looks at the list again; when
nothing can make progress any more, they all wait for the caller: native
Lean deadlocks. -/
def taskWaitAnyFn (listTy : RR.Ty) (taskTy : RR.Ty) : LowerM String := do
  let (z, t) ← lazyOf taskTy
  let .named ln := listTy | throwError "lean2rr: bad list type {listTy.render}"
  let some info := (← get).typeInfos[ln]? | throwError "lean2rr: bad list type {ln}"
  let some nil := info.ctors.find? ``List.nil | throwError "lean2rr: bad list type {ln}"
  let some cons := info.ctors.find? ``List.cons | throwError "lean2rr: bad list type {ln}"
  let some (some (_, et)) := cons.fields[0]? | throwError "lean2rr: bad list type {ln}"
  let get ← lazyGetFn z
  let addr ← taskAddrFn z
  let name := s!"l2r_task_wait_any_{z}_{ln}"
  let run := name ++ "_run"
  let task ← coerce (.var "c") et taskTy
  lazyFn name do
    let u8 := RR.Ty.named "u8"
    let listArm (v : String) (bs : Array (Option String)) (b : RR.Block) : RR.Arm :=
      { ty := ln, ctor := some v, binders := bs, body := b }
    -- `cons` binders at the fields' record positions.
    let consBinders := (cons.place #[.var "c", .var "rest"]).map fun | .var v => some v | _ => none
    let pick (want : Nat) (next : RR.Expr) : RR.Block :=
      ⟨#[("tc", some taskTy, task), ("st", some u8, .call "l2r_task_wait_status_at" #[] #[.call addr #[] #[.var "tc"]]),
          ("want", some u8, .atom (toString want))],
        .ite (.atom "st == want") (.ofExpr (.call get #[] #[.var "tc"])) (.ofExpr next)⟩
    let firstDone : RR.Block := .ofExpr (.mtch (.var "l") #[
      listArm nil.variant #[] (.ofExpr (.call run #[] #[.var "all", .var "all"])),
      listArm cons.variant consBinders (pick 2 (.call name #[] #[.var "rest", .var "all"]))])
    let again : RR.Block := ⟨#[("r1", some (.named "u64"), .call "l2r_task_wait_progress" #[] #[]),
        ("one", some (.named "u64"), .atom "1")],
      .ite (.atom "r1 == one") (.ofExpr (.call name #[] #[.var "all", .var "all"]))
        (.ofExpr (.call "l2r_lazy_cycle" #[t] #[]))⟩
    let firstPending : RR.Block := .ofExpr (.mtch (.var "l") #[
      listArm nil.variant #[] again,
      listArm cons.variant consBinders (pick 0 (.call run #[] #[.var "rest", .var "all"]))])
    return #[.fn run #[("l", listTy), ("all", listTy)] t firstPending,
      .fn name #[("l", listTy), ("all", listTy)] t firstDone]

/-- A task priority (`Task.Priority`, a `Nat`) for the runtime, which takes
it modulo 2^32 as Lean's `lean_unbox(prio)` passed as an `unsigned`. -/
def prioOf (p : RR.Expr) : RR.Expr := .call "lean_usize_of_nat" #[] #[p]

/-- The glue of `lazyExtern`, on arguments that are variables. -/
def lazyExternGlue (orig : Name) (params : Array Expr) (ret : Expr) (args : Array RR.Expr) :
    LowerM (Option RR.Expr) := do
  let pty (i : Nat) : LowerM RR.Ty := lowerType params[i]!
  -- `f : PUnit → α` applied to `()`, or `f : α → β` to a task's value.
  let applyTo (f : RR.Expr) (fTy : RR.Ty) (arg : RR.Expr) (argTy : RR.Ty) (dst : RR.Ty) : LowerM RR.Expr := do
    let .fn d c := fTy | throwError "lean2rr: application of {fTy.render}"
    let a ← coerce arg argTy d
    withVar "tf" fTy f fun g => do coerce (← applyCall g fTy #[a]) c dst
  match orig with
  | ``Thunk.mk =>
    let (z, t) ← lazyOf (← lowerType ret)
    let f ← coerce args[0]! (← pty 0) (.fn .unit t)
    return some (.call "l2r_lcell_new" #[.named z] #[.ctor z (some "pending") #[f]])
  | ``Thunk.pure | ``Task.pure =>
    let (z, t) ← lazyOf (← lowerType ret)
    return some (lazyDone z (← coerce args[0]! (← pty 0) t))
  | ``Thunk.get | ``Task.get => return some (← lazyGet args[0]! (← pty 0) (← lowerType ret))
  -- `IO.getTID` inside a task: natively a worker thread's (see
  -- `leanrt::task::tid_offset`).
  | ``IO.getTID =>
    let u64 := RR.Ty.named "u64"
    return some (← wrapIOResult (← lowerType ret) (.block ⟨#[("tid", some u64, .call "l2r_io_get_tid" #[] #[]),
      ("toff", some u64, .call "l2r_task_tid_offset" #[] #[])], .atom "tid + toff"⟩))
  -- Pure tasks (see `taskNewFn`).
  | ``Task.spawn =>
    let rt ← lowerType ret
    let (z, t) ← lazyOf rt
    let f ← coerce args[0]! (← pty 0) (.fn .unit t)
    return some (.call (← taskNewFn z true) #[] #[f, prioOf args[1]!, .atom (toString (taskKind true false))])
  | ``Task.map | ``Task.bind =>
    -- `map f x prio sync`, `bind x f prio sync`. With `sync := true` and
    -- `x` finished, Lean applies `f` at once in the calling thread
    -- (`lean_task_map_core`/`lean_task_bind_core`); otherwise the new task
    -- depends on `x` (`add_dep`), and a `bind` task continues as the task
    -- `f` returns.
    let isMap := orig == ``Task.map
    let (fi, xi) := if isMap then (0, 1) else (1, 0)
    let rt ← lowerType ret
    let (z, t) ← lazyOf rt
    let xTy ← pty xi
    let (xz, xt) ← lazyOf xTy
    let fTy ← pty fi
    let .fn _ fRes := fTy | throwError "lean2rr: {orig} of a function of type {fTy.render}"
    let applied : LowerM RR.Expr := do
      applyTo args[fi]! fTy (← lazyGet args[xi]! xTy xt) xt (if isMap then t else rt)
    let now ← if isMap then do pure (lazyDone z (← applied)) else applied
    let u ← fresh "w"
    let g := rawFnValue (.fn .unit (if isMap then t else rt)) u (.ofExpr (← applied))
    let later := RR.Expr.call (← taskNewFn z true (bind := !isMap)) #[]
      #[g, prioOf args[2]!, .atom (toString (taskKind true true))]
    let _ := fRes
    let laterB ← taskDepend z rt later (← taskAddrFn xz) args[xi]! args[3]!
    let d ← fresh "sync"
    let cond : RR.Expr := .ite args[3]! (.ofExpr (← taskDone xz args[xi]!)) (.ofExpr (.atom "false"))
    return some (.block ⟨#[(d, some .bool, cond)], .ite (.var d) (.ofExpr now) laterB⟩)
  -- IO tasks: `asTask act prio`, `mapTask f t prio sync`, `bindTask t f prio
  -- sync`; results are `ST.Out` structures.
  | ``BaseIO.asTask =>
    let resTy ← lowerType ret
    let taskTy ← ioPayloadTy resTy
    let (_, t) ← lazyOf taskTy
    let actTy ← pty 0
    let c ← newTask taskTy false (prioOf args[1]!) fun w => runIO args[0]! actTy w t
    return some (← wrapIOResult resTy c)
  | ``BaseIO.mapTask | ``BaseIO.bindTask =>
    let isMap := orig == ``BaseIO.mapTask
    let (fi, ti) := if isMap then (0, 1) else (1, 0)
    let resTy ← lowerType ret
    let taskTy ← ioPayloadTy resTy
    let (z, t) ← lazyOf taskTy
    let srcTy ← pty ti
    let (sz, _) ← lazyOf srcTy
    let fTy ← pty fi
    let .fn fd actTy := fTy | throwError "lean2rr: {orig} of a function of type {fTy.render}"
    -- The new task's value, running `f` on the world `w`; for `bindTask`,
    -- the task it continues as.
    let value (w : RR.Expr) : LowerM RR.Expr := do
      let x ← lazyGet args[ti]! srcTy fd
      withVar "tf" fTy args[fi]! fun f => do
        if isMap then runIO (← applyCall f fTy #[x]) actTy w t
        else
          runIO (← applyCall f fTy #[x]) actTy w taskTy
    -- With `sync := true` and `t` finished, Lean runs `f` at once
    -- (`lean_task_map_core`/`lean_task_bind_core`); otherwise the task is
    -- deferred, and canceled if `t` is unfinished now and finishes canceled.
    let now ← if isMap then do
        let v ← value args[4]!
        pure (lazyDone z v)
      else do
        let x ← lazyGet args[ti]! srcTy fd
        withVar "tf" fTy args[fi]! fun f => do
          runIO (← applyCall f fTy #[x]) actTy args[4]! taskTy
    let later ← if isMap then newTask taskTy false (prioOf args[2]!) value (dep := true) else do
      let u ← fresh "w"
      pure (RR.Expr.call (← taskNewFn z false (bind := true)) #[]
        #[rawFnValue (.fn .unit taskTy) u (.ofExpr (← value (.var u))), prioOf args[2]!,
          .atom (toString (taskKind false true))])
    let d ← fresh "sync"
    let cond : RR.Expr := .ite args[3]! (.ofExpr (← taskDone sz args[ti]!)) (.ofExpr (.atom "false"))
    let laterB ← taskDepend z taskTy later (← taskAddrFn sz) args[ti]! args[3]!
    let r ← fresh "tn"
    return some (.block ⟨#[(d, some .bool, cond), (r, some taskTy, .ite (.var d) (.ofExpr now) laterB)],
      ← wrapIOResult resTy (.var r)⟩)
  | ``IO.wait =>
    let resTy ← lowerType ret
    return some (← wrapIOResult resTy (← lazyGet args[0]! (← pty 0) (← ioPayloadTy resTy)))
  | ``IO.waitAny =>
    let resTy ← lowerType ret
    let lt ← pty 0
    let some et := (← ctorFieldTys lt ``List.cons)[0]? | return none
    let (_, t) ← lazyOf et
    let f ← taskWaitAnyFn lt et
    let v ← coerce (.call f #[] #[args[0]!, args[0]!]) t (← ioPayloadTy resTy)
    return some (← wrapIOResult resTy v)
  | ``IO.getTaskState =>
    let resTy ← lowerType ret
    let (z, _) ← lazyOf (← pty 0)
    return some (← wrapIOResult resTy (.call (← taskStateFn z (← ioPayloadTy resTy)) #[] #[args[0]!]))
  | ``IO.cancel =>
    let resTy ← lowerType ret
    let (z, _) ← lazyOf (← pty 0)
    let r ← fresh "cn"
    return some (.block ⟨#[(r, some (.named "u64"), .call "l2r_task_cancel_at" #[] #[.call (← taskAddrFn z) #[] #[args[0]!]])],
      ← wrapIOResult resTy .unitVal⟩)
  | _ => return none

/-- Glue for the thunk and task externs; `none` for other externs. `args`
are the relevant arguments, already at the Reussir types of `params`. -/
def lazyExtern (orig : Name) (params : Array Expr) (ret : Expr) (args0 : Array RR.Expr) :
    LowerM (Option RR.Expr) := do
  unless orig ∈ [``Thunk.mk, ``Thunk.pure, ``Task.pure, ``Thunk.get, ``Task.get, ``Task.spawn,
      ``Task.map, ``Task.bind, ``BaseIO.asTask, ``BaseIO.mapTask, ``BaseIO.bindTask, ``IO.wait,
      ``IO.waitAny, ``IO.getTaskState, ``IO.cancel, ``IO.getTID] do return none
  let pty (i : Nat) : LowerM RR.Ty := lowerType params[i]!
  -- Arguments may be used several times below: bind them to variables.
  let mut pre := #[]
  let mut args := #[]
  for h : i in [:args0.size] do
    match args0[i] with
    | .var n => args := args.push (RR.Expr.var n)
    | a =>
      let x ← fresh "ta"
      pre := pre.push (x, some (← pty i), a)
      args := args.push (.var x)
  let some e ← lazyExternGlue orig params ret args | return none
  return some (if pre.isEmpty then e else .block ⟨pre, e⟩)

/-- The runtime primitive of a slice extern (see `customExtern`). -/
def sliceGlue? : String → Option String
  | "lean_byteslice_beq" => some "l2r_byteslice_beq"
  | "lean_slice_hash" => some "l2r_slice_hash"
  | "lean_slice_dec_lt" => some "l2r_slice_dec_lt"
  | _ => none

end LeanToReussir
