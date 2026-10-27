import LeanToReussir.Lower.Process

/-! # Promises

`IO.Promise α` is `lcAny` in mono code, so a promise is passed boxed: a
runtime `LPromise` holding the cell of its task (the one task type, whose
value, an `Option α`, is boxed), whatever `α` is (translation plan
§5.14). The task is pending, without a computation the runtime would run,
until the promise is resolved; forcing it while unresolved waits for it in
lean-runtime's `wait` (`l2r_task_source_next_at`: other contexts and
queued tasks run meanwhile, as other threads would), as natively, until
the promise is resolved, by the program or with `none` when its last
reference goes (the resolution stores the value before the wait returns).
Its `pending` closure waits forever: a fallback, run only if the wait
returned with the promise still unresolved. -/

namespace LeanToReussir
open Lean Compiler LCNF

/-- The task type of every promise (`Task (Option lcAny)`), its state type
and the `Option` type of its value (held boxed in the task's state). -/
def promiseTask : LowerM (RR.Ty × String × RR.Ty) := do
  let optTy ← lowerType (mkApp (mkConst ``Option [levelZero]) (mkConst ``lcAny))
  let z ← lazyState true
  return (.app "LCell" #[.named z], z, optTy)

/-- `l2r_promise_resolve_S(c, v)`: resolve the promise task `c` with `v`
unless it is resolved already (only the first resolution counts): its
dependents are walked on this thread (Lean's `resolve_core`). The test and
the cell's store are the runtime's, inside lean-runtime's `resolve`, after
its writers point (`l2r_promise_resolve_with`): a test here, before that
point, could see the promise unresolved while another context resolves it
during the point, and the store would replace that resolution (review
HR-01). Also `l2r_promise_drop(c)`, which the runtime calls (as the
trampoline `l2r_promise_drop_c`) when the last reference to a promise goes:
an unresolved promise is resolved with `none` (`deactivate_promise`). -/
def promiseResolveFn : LowerM String := do
  let (cellTy, z, optTy) ← promiseTask
  let name := s!"l2r_promise_resolve_{z}"
  lazyFn name do
    let zt := RR.Ty.named z
    let u64 := RR.Ty.named "u64"
    -- The task's value is the `Option`, boxed.
    let bv ← coerce (.var "v") optTy RR.Ty.box
    let body : RR.Block := .ofExpr
      (.call "l2r_promise_resolve_with" #[zt] #[.var "c", .ctor z (some "done") #[bv]])
    let none' ← ctorValue optTy ``Option.none #[]
    return #[.fn name #[("c", cellTy), ("v", optTy)] u64 body,
      .fn "l2r_promise_drop" #[("c", cellTy)] u64 (.ofExpr (.call name #[] #[.var "c", none'])),
      .raw "extern \"C\" trampoline \"l2r_promise_drop_c\" = l2r_promise_drop;\n"]

/-- Glue for the promise externs (`IO.Promise.new`, `resolve`, `result?`,
and `Option.getOrBlock!`, which `Promise.result!` maps over `result?`);
`none` for other externs. -/
def promiseExtern (sym : String) (params : Array Expr) (ret : Expr) (args : Array RR.Expr) :
    LowerM (Option RR.Expr) := do
  let lpTy := RR.Ty.named "LPromise"
  let cellOf (i : Nat) : LowerM RR.Expr := do
    let (_, z, _) ← promiseTask
    return .call "l2r_promise_cell" #[.named z] #[← coerce args[i]! (← lowerType params[i]!) lpTy]
  match sym with
  | "lean_io_promise_new" =>
    let (cellTy, z, _) ← promiseTask
    let _ ← promiseResolveFn
    let resTy ← lowerType ret
    let u ← fresh "u"
    let hang := rawFnValue (.fn .unit RR.Ty.box) u (.ofExpr (.call "l2r_lazy_cycle" #[RR.Ty.box] #[]))
    let c ← fresh "pc"
    let p ← fresh "pr"
    return some (.block ⟨#[(c, some cellTy, .call "l2r_lcell_new" #[.named z] #[.ctor z (some "pending") #[hang]]),
      (p, some lpTy, .call "l2r_promise_new" #[.named z] #[.var c])], ← wrapIOResult resTy (.var p) lpTy⟩)
  | "lean_io_promise_resolve" =>
    let some _ := args[1]? | return none
    let (cellTy, _, optTy) ← promiseTask
    let resolve ← promiseResolveFn
    let boxed ← coerce args[0]! (← lowerType params[0]!) RR.Ty.box
    let (_, z, _) ← promiseTask
    let q ← fresh "pq"
    let c ← fresh "pc"
    let r ← fresh "pr"
    let k ← fresh "pk"
    -- The promise is borrowed: it is released after the resolution (were
    -- this its last reference, releasing it first would resolve it with
    -- `none`).
    return some (.block ⟨#[(q, some lpTy, ← coerce args[1]! (← lowerType params[1]!) lpTy),
      (c, some cellTy, .call "l2r_promise_cell" #[.named z] #[.var q]),
      (r, some (.named "u64"), .call resolve #[] #[.var c, ← ctorValue optTy ``Option.some #[boxed]]),
      (k, some (.named "u64"), .call "l2r_promise_release" #[] #[.var q])],
      ← wrapIOResult (← lowerType ret) .unitVal .unit⟩)
  | "lean_io_promise_result_opt" =>
    let some _ := args[0]? | return none
    let (cellTy, _, _) ← promiseTask
    let c ← fresh "pc"
    return some (.block ⟨#[(c, some cellTy, ← cellOf 0)], ← coerce (.var c) cellTy (← lowerType ret)⟩)
  | "lean_option_get_or_block" =>
    let some o := args.back? | return none
    let ot ← lowerType params.back!
    let rt ← lowerType ret
    let x ← fresh "oo"
    return some (.block ⟨#[(x, some ot, o)], ← optionCases (.var x) ot (fun v vt => coerce v vt rt)
      (.call "l2r_option_get_or_block_none" #[rt] #[])⟩)
  | _ => return none

/-- `l2r_task_run_one()`, the program's dispatcher, which lean-runtime
reaches through the trampoline `l2r_task_run_one_c`: a task's job
(`leanrt::task`'s `run_job`, or `unrun` for a job lean-runtime drops
unrun) hands it one counted reference to the task's cell, with the state
type's tag (`taskTag`), and it runs the task as a worker would
(`taskStepFn`), or drops the reference when the runtime says the task is
deleted (`l2r_task_deleting`). It answers 1, or 0 when nothing is handed
over (the runtime ignores the answer). lean-runtime walks dependents,
waits for tasks and runs what is left after `main` itself: the generated
code has no other dispatcher. Generated once every task is registered;
every program has it, with no arm if it registers no task. -/
def taskDispatchFns : LowerM (Array RR.Item) := do
  -- The task state type, tag 0 (`taskTag`), once a task is registered.
  let tags ← if ← getPart (·.taskTagged) then pure #[← lazyState true] else pure #[]
  let u64 := RR.Ty.named "u64"
  let mut chain : RR.Block := ⟨#[("none", some u64, .atom "0")], .var "none"⟩
  for i in [:tags.size] do
    let j := tags.size - 1 - i
    let z := tags[j]!
    let step ← taskStepFn z
    chain := ⟨#[(s!"k{j}", some u64, .atom (toString j))], .ite (.atom s!"tag == k{j}")
      ⟨#[("c", some (.app "LCell" #[.named z]), .call "l2r_task_take" #[.named z] #[]),
        ("d", some .bool, .call "l2r_task_deleting" #[] #[]),
        ("v", some u64, .ite (.var "d") ⟨#[("z", some u64, .atom "0")], .var "z"⟩
          (.ofExpr (.call step #[] #[.var "c"])))], .atom "1"⟩ chain⟩
  return #[
    .fn "l2r_task_run_one" #[] u64 ⟨#[("tag", some u64, .call "l2r_task_next_tag" #[] #[])], .block chain⟩,
    -- The runtime's scheduler runs a task's job, on the context it chooses
    -- (`leanrt::sched`), through this entry point.
    .raw "extern \"C\" trampoline \"l2r_task_run_one_c\" = l2r_task_run_one;\n"]

end LeanToReussir
