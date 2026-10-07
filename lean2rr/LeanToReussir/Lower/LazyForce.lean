import LeanToReussir.Lower.FnValues

/-! # Thunks and tasks: forcing

A `Thunk α` or `Task α` is a runtime cell `LCell<S>` holding a generated
state `S { pending(L2RUnit -> Box), busy, done(Box) }` (a task also has a
`bind` state), one state type for thunks and one for tasks, whatever `α`
is (`lazyState`, translation plan §5.14). The functions below are generated
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

/-- Whether state type `z` is the tasks' (otherwise it is the thunks'). -/
def lazyIsTask (z : String) : LowerM Bool := do
  match ← lazyOf? (.app "LCell" #[.named z]) with
  | some (_, task) => return task
  | none => throwError "lean2rr: {z} is not a thunk or task state (internal error)"

/-- A match arm on state type `z`. -/
def lazyArm (z v : String) (binders : Array (Option String)) (body : RR.Block) : RR.Arm :=
  { ty := z, ctor := some v, binders, body }

/-- A task's identity for the runtime (`leanrt::task`): the address of its
cell `c` (of state type `z`). -/
def taskAddr (z : String) (c : RR.Expr) : RR.Expr :=
  .call "l2r_lcell_addr" #[.named z] #[c]

/-- `l2r_task_bindstep_S(c, g)`: a `bind` task (`IO.bindTask`, `Task.bind`)
runs `f` (`g(())` gives the task it continues as). If that task has
finished, so has this one, with its value (`task_bind_fn1`), and its
dependents are walked on its thread; otherwise it waits for that task,
keeping its priority and flags, and finishes as it (`l2r_task_bind_wait`;
Lean re-adds it as a dependent). `get` is the state's forcing function. -/
def taskBindStepFn (z get : String) : LowerM String := do
  let t := RR.Ty.box
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
      ("w", some u64, .call "l2r_task_bind_wait" #[zt] #[.var "c", taskAddr z (.var "t2")])], .atom "0"⟩
    let body : RR.Block := ⟨#[("b", some u64, onCell "l2r_task_begin"),
      ("se", some u64, .call "l2r_std_enter_if" #[] #[.var "b"]),
      ("t2", some cellTy, ← applyCall (.var "g") (.fn .unit cellTy) #[.unitVal]),
      ("st", some (.named "u8"), .call "l2r_task_status_at" #[] #[taskAddr z (.var "t2")]),
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
(translation plan §5.14). A pending task is
also registered as running for the duration (`IO.checkCanceled`, and it leaves the queue of
pending tasks), and runs with its own standard streams,
as a native task runs on a worker thread (`l2r_std_enter_if`/`l2r_std_leave_if`),
unless the runtime runs it on the current thread (a `sync` dependent). When
it has finished, its dependents are walked on its thread, with its streams
(`l2r_task_walk_if`), before the caller's streams are back. -/
def lazyGetFn (z : String) : LowerM String := do
  let task ← lazyIsTask z
  let t := RR.Ty.box
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
    let getWith (other : RR.Block) : RR.Block := .ofExpr (.mtch (.call "l2r_lcell_get" #[zt] #[.var "c"]) #[
      lazyArm z "done" #[some "v"] (.ofExpr (.var "v")),
      lazyArm z "busy" #[] busy,
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

/-- The runtime tag of the task state type, 0 (there is one, `lazyState`):
the functions that run the tasks the runtime hands over dispatch on it
(`taskDispatchFns`), and exist once a task is registered. -/
def taskTag : LowerM Nat := do
  modify fun s => { s with taskTagged := true }
  return 0

/-- A new cell in state `done(v)` (`Thunk.pure`, `Task.pure`, tasks computed
at once during initialization, and `sync` dependents of finished tasks). -/
def lazyDone (z : String) (v : RR.Expr) : RR.Expr :=
  .call "l2r_lcell_new" #[.named z] #[.ctor z (some "done") #[v]]

/-- A new reference of the reference type `rt` (`refType`) holding the
`Box` `v`. -/
def refNew (rt : RR.Ty) (v : RR.Expr) : RR.Expr :=
  let rn := match rt with | .named n => n | _ => ""
  .ctor rn none #[.call "core::intrinsic::cell::alloc" #[] #[v]]

end LeanToReussir
