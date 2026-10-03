import LeanToReussir.Lower.FnValues

/-! # Thunks and tasks: forcing

A `Thunk α` or `Task α` is a runtime cell `LCell<S>` holding a generated
state `S { pending(L2RUnit -> α), busy, done(α), conv(L2RUnit -> α, Box) }`
(a task's `conv` also holds a `u64`, and a task has a `bind` state;
`lazyState`, translation plan §5.14). The functions below are generated
once per state type. -/

namespace LeanToReussir
open Lean Compiler LCNF

/-- Generate the functions `mk` builds under the name `name`, once. -/
def lazyFn (name : String) (mk : LowerM (Array RR.Item)) : LowerM String := do
  if (← get).lazyFnNames.contains name then return name
  modify fun s => { s with lazyFnNames := s.lazyFnNames.insert name }
  let items ← mk
  modify fun s => { s with fns := s.fns ++ items }
  return name

/-- Whether state type `z` is a task's, and its value type. -/
def lazyInfo (z : String) : LowerM (Bool × RR.Ty) := do
  match (← get).lazyInfos[z]? with
  | some i => return i
  | none => throwError "lean2rr: {z} is not a thunk or task state (internal error)"

/-- A match arm on state type `z`. -/
def lazyArm (z v : String) (binders : Array (Option String)) (body : RR.Block) : RR.Arm :=
  { ty := z, ctor := some v, binders, body }

/-- The binders of the fields of a `conv` state after its computation: the
original cell (boxed) and, for a task, the original's address. -/
def convTail (task : Bool) (o : Option String := none) (a : Option String := none) : Array (Option String) :=
  if task then #[o, a] else #[o]

/-- `l2r_task_addr_S(c)`: a task's identity for the runtime (`leanrt::task`):
the address of its cell, or the original's that a converted task records
(`lazyConv`) until it has its value. -/
def taskAddrFn (z : String) : LowerM String := do
  let name := s!"l2r_task_addr_{z}"
  lazyFn name do
    let zt := RR.Ty.named z
    let body : RR.Block := .ofExpr (.mtch (.call "l2r_lcell_get" #[zt] #[.var "c"]) #[
      lazyArm z "conv" (#[none] ++ convTail true none (some "a")) (.ofExpr (.var "a")),
      { ty := z, ctor := none, binders := #[], body := .ofExpr (.call "l2r_lcell_addr" #[zt] #[.var "c"]) }])
    return #[.fn name #[("c", .app "LCell" #[zt])] (.named "u64") body]

/-- `l2r_task_bindstep_S(c, g)`: a `bind` task (`IO.bindTask`, `Task.bind`)
runs `f` (`g(())` gives the task it continues as). If that task has
finished, so has this one, with its value (`task_bind_fn1`), and its
dependents are walked on its thread; otherwise it waits for that task,
keeping its priority and flags, and finishes as it (`l2r_task_bind_wait`;
Lean re-adds it as a dependent). `get` is the state's forcing function. -/
def taskBindStepFn (z get : String) : LowerM String := do
  let (_, t) ← lazyInfo z
  let addr ← taskAddrFn z
  let name := s!"l2r_task_bindstep_{z}"
  lazyFn name do
    let zt := RR.Ty.named z
    let cellTy := RR.Ty.app "LCell" #[zt]
    let u64 := RR.Ty.named "u64"
    let onCell (f : String) : RR.Expr := .call f #[zt] #[.var "c"]
    let u ← fresh "u"
    let cont := rawFnValue (.fn .unit t) u (.ofExpr (.call get #[] #[.var "t2"]))
    let finish : RR.Block := ⟨#[("v", some t, .call get #[] #[.var "t2"]),
      ("s", some u64, .call "l2r_lcell_set" #[zt] #[.var "c", .ctor z (some "done") #[.var "v"]]),
      ("e", some u64, onCell "l2r_task_end"), ("wk", some u64, .call "l2r_task_walk_if" #[] #[.var "e"]),
      ("sl", some u64, .call "l2r_std_leave_if" #[] #[.var "b"])], .atom "0"⟩
    let wait : RR.Block := ⟨#[("sl", some u64, .call "l2r_std_leave_if" #[] #[.var "b"]),
      ("s", some u64, .call "l2r_lcell_set" #[zt] #[.var "c", .ctor z (some "pending") #[cont]]),
      ("w", some u64, .call "l2r_task_bind_wait" #[zt] #[.var "c", .call addr #[] #[.var "t2"]])], .atom "0"⟩
    let body : RR.Block := ⟨#[("b", some u64, onCell "l2r_task_begin"),
      ("se", some u64, .call "l2r_std_enter_if" #[] #[.var "b"]),
      ("t2", some cellTy, ← applyCall (.var "g") (.fn .unit cellTy) #[.unitVal]),
      ("st", some (.named "u8"), .call "l2r_task_status_at" #[] #[.call addr #[] #[.var "t2"]]),
      ("fin", some (.named "u8"), .atom "2")], .ite (.atom "st == fin") finish wait⟩
    return #[.fn name #[("c", cellTy), ("g", .fn .unit cellTy)] u64 body]

/-- `l2r_thunk_get_S(c)` / `l2r_task_get_S(c)`: the value of a thunk or
task, computed on first use and kept. The slow path swaps in `busy` (so the
pending state, now uniquely held, can be reused for `done`), runs the
closure and stores its value, like `lean_thunk_get_core`, which takes the
closure out before calling it. Forcing a `busy` thunk means the value is
needed by its own computation: native Lean then waits forever, and so do
we; a `busy` task runs on another (blocked) context of the runtime's
scheduler and is waited for, unless it is the running context's own
(translation plan §5.14). A converted copy (`conv`, see `lazyConv`) has
no running state of its own: forcing it runs its computation, which forces
the original (whose state, `busy` included, is the copy's) and converts the
value, and stores `done` (releasing the original). So a copy forced again
meanwhile (by the original's `sync` dependent, which the original's end
runs inside the copy's computation, or by another context) has the
original's value as soon as the original has finished. A pending task is also registered as
running for the duration (`IO.checkCanceled`, and it leaves the queue of
pending tasks), and runs with its own standard streams,
as a native task runs on a worker thread (`l2r_std_enter_if`/`l2r_std_leave_if`),
unless the runtime runs it on the current thread (a `sync` dependent). When
it has finished, its dependents are walked on its thread, with its streams
(`l2r_task_walk_if`), before the caller's streams are back. -/
def lazyGetFn (z : String) : LowerM String := do
  let (task, t) ← lazyInfo z
  let kind := if task then "task" else "thunk"
  let get := s!"l2r_{kind}_get_{z}"
  let run := s!"l2r_{kind}_run_{z}"
  let bindStep ← if task then taskBindStepFn z get else pure ""
  lazyFn get do
    let zt := RR.Ty.named z
    let cellTy := RR.Ty.app "LCell" #[zt]
    let u64 := RR.Ty.named "u64"
    -- A `busy` task runs on another context of the runtime's scheduler (a
    -- task that blocked): wait until it has finished, then look again; on
    -- the current context, it needs itself (`l2r_task_wait_running` waits
    -- forever then). A `busy` thunk is being forced on another context
    -- (natively another thread, which this one waits for) or by its own
    -- computation (natively a wait forever): wait until it has its value
    -- (`l2r_thunk_wait_busy`, woken by `l2r_thunk_done`).
    let busy : RR.Block := if task then
        ⟨#[("wb", some u64, .call "l2r_task_wait_running" #[] #[.call "l2r_lcell_addr" #[zt] #[.var "c"]])],
          .call get #[] #[.var "c"]⟩
      else
        ⟨#[("wb", some u64, .call "l2r_thunk_wait_busy" #[] #[.call "l2r_lcell_addr" #[zt] #[.var "c"]])],
          .call get #[] #[.var "c"]⟩
    let force ← applyCall (.var "f") (.fn .unit t) #[.unitVal]
    let conv : RR.Block := ⟨#[("v", some t, force),
      ("s", some u64, .call "l2r_lcell_set" #[zt] #[.var "c", .ctor z (some "done") #[.var "v"]])],
      .var "v"⟩
    let getWith (other : RR.Block) : RR.Block := .ofExpr (.mtch (.call "l2r_lcell_get" #[zt] #[.var "c"]) #[
      lazyArm z "done" #[some "v"] (.ofExpr (.var "v")),
      lazyArm z "busy" #[] busy,
      lazyArm z "conv" (#[some "f"] ++ convTail task) conv,
      { ty := z, ctor := none, binders := #[], body := other }])
    -- A task first runs the chain of pending tasks it waits for, deepest
    -- first (`l2r_task_force_sources`), then looks again (one of them may
    -- have run it, as a `sync` dependent).
    let getBody : RR.Block := if task then
        getWith ⟨#[("fs", some u64, .call "l2r_task_force_sources" #[] #[.call "l2r_lcell_addr" #[zt] #[.var "c"]])],
          .call (get ++ "_now") #[] #[.var "c"]⟩
      else getWith (.ofExpr (.call run #[] #[.var "c"]))
    let nowBody : RR.Block := getWith (.ofExpr (.call run #[] #[.var "c"]))
    let onCell (f : String) : RR.Expr := .call f #[zt] #[.var "c"]
    let lets : Array (String × Option RR.Ty × RR.Expr) :=
      (if task then #[("b", some u64, onCell "l2r_task_begin"), ("se", some u64, .call "l2r_std_enter_if" #[] #[.var "b"])]
        else #[]) ++
      #[("v", some t, force),
        ("s", some u64, .call "l2r_lcell_set" #[zt] #[.var "c", .ctor z (some "done") #[.var "v"]])] ++
      (if task then #[("e", some u64, onCell "l2r_task_end"), ("wk", some u64, .call "l2r_task_walk_if" #[] #[.var "e"]),
          ("sl", some u64, .call "l2r_std_leave_if" #[] #[.var "b"])]
        else #[("td", some u64, .call "l2r_thunk_done" #[] #[onCell "l2r_lcell_addr"])])
    -- A `bind` task runs `f` (`taskBindStepFn`): it has then finished, or
    -- waits for the task it continues as; either way it is needed now.
    let bindArm : Array RR.Arm := if task then
        #[lazyArm z "bind" #[some "g"] ⟨#[("bs", some u64, .call bindStep #[] #[.var "c", .var "g"])],
          .call get #[] #[.var "c"]⟩]
      else #[]
    let runBody : RR.Block := .ofExpr (.mtch (.call "l2r_lcell_swap" #[zt] #[.var "c", .ctor z (some "busy") #[]]) (#[
      lazyArm z "pending" #[some "f"] ⟨lets, .var "v"⟩] ++ bindArm ++ #[
      { ty := z, ctor := none, binders := #[], body := .ofExpr (.call "l2r_unreachable" #[t] #[]) }]))
    return #[.fn run #[("c", cellTy)] t runBody, .fn get #[("c", cellTy)] t getBody] ++
      (if task then #[.fn (get ++ "_now") #[("c", cellTy)] t nowBody] else #[])

/-- The runtime tag of task state type `z`: the entry point runs the tasks
still queued when `main` returns, dispatching on it. -/
def taskTag (z : String) : LowerM Nat := do
  match (← get).taskTags.idxOf? z with
  | some i => return i
  | none =>
    let i := (← get).taskTags.size
    modify fun s => { s with taskTags := s.taskTags.push z }
    return i

/-- A new cell in state `done(v)` (`Thunk.pure`, `Task.pure`, tasks computed
at once during initialization, and `sync` dependents of finished tasks). -/
def lazyDone (z : String) (v : RR.Expr) : RR.Expr :=
  .call "l2r_lcell_new" #[.named z] #[.ctor z (some "done") #[v]]

/-- A new reference of type `rt` (element type `e`, stored as `k`) holding
`v : e`. -/
def refNew (rt : RR.Ty) (e : RR.Ty) (k : RefKind) (v : RR.Expr) : RR.Expr :=
  let rn := match rt with | .named n => n | _ => ""
  match k with
  | .direct => .ctor rn none #[.call "core::intrinsic::cell::alloc" #[] #[v]]
  | .boxed bn => .ctor rn none #[.call "core::intrinsic::cell::alloc" #[] #[.ctor bn none #[v]]]
  | .nat => .call "l2r_natref_new" #[] #[v]
  | .int => .call "l2r_intref_new" #[] #[v]

end LeanToReussir
