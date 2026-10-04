import LeanToReussir.Lower.Process

/-! # Promises

`IO.Promise α` is `lcAny` in mono code, so a promise is passed boxed: a
runtime `LPromise` holding the cell of its task, a task over `Option Box`
whatever `α` is, so that typed and uniform code share it (translation plan
§5.14). The task is pending, without a computation the runtime would run,
until the promise is resolved; forcing it while unresolved runs queued
tasks until one resolves it (`l2r_task_force_sources`), and otherwise
waits forever (its `pending` closure), as natively. -/

namespace LeanToReussir
open Lean Compiler LCNF

/-- The task type of every promise (`Task (Option lcAny)`), its state type
and its value type. -/
def promiseTask : LowerM (RR.Ty × String × RR.Ty) := do
  let optTy ← lowerType (mkApp (mkConst ``Option [levelZero]) (mkConst ``lcAny))
  let z ← lazyState true optTy
  return (.app "LCell" #[.named z], z, optTy)

/-- `l2r_promise_resolve_S(c, v)`: resolve the promise task `c` with `v`
unless it is resolved already (only the first resolution counts): its
dependents are walked on this thread (Lean's `resolve_core`). Also
`l2r_promise_drop(c)`, which the runtime calls (as the trampoline
`l2r_promise_drop_c`) when the last reference to a promise goes: an
unresolved promise is resolved with `none` (`deactivate_promise`). -/
def promiseResolveFn : LowerM String := do
  let (cellTy, z, optTy) ← promiseTask
  let name := s!"l2r_promise_resolve_{z}"
  lazyFn name do
    let zt := RR.Ty.named z
    let u64 := RR.Ty.named "u64"
    let body : RR.Block := .ofExpr (.mtch (.call "l2r_lcell_get" #[zt] #[.var "c"]) #[
      lazyArm z "done" #[none] ⟨#[("z", some u64, .atom "0")], .var "z"⟩,
      { ty := z, ctor := none, binders := #[], body := ⟨#[
          ("s", some u64, .call "l2r_lcell_set" #[zt] #[.var "c", .ctor z (some "done") #[.var "v"]]),
          ("r", some u64, .call "l2r_task_resolve_at" #[] #[.call "l2r_lcell_addr" #[zt] #[.var "c"]]),
          ("wk", some u64, .call "l2r_task_walk_if" #[] #[.var "r"])], .atom "0"⟩ }])
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
    let (cellTy, z, optTy) ← promiseTask
    let _ ← promiseResolveFn
    let resTy ← lowerType ret
    let u ← fresh "u"
    let hang := rawFnValue (.fn .unit optTy) u (.ofExpr (.call "l2r_lazy_cycle" #[optTy] #[]))
    let c ← fresh "pc"
    let p ← fresh "pr"
    let v ← coerce (.var p) lpTy (← ioPayloadTy resTy)
    return some (.block ⟨#[(c, some cellTy, .call "l2r_lcell_new" #[.named z] #[.ctor z (some "pending") #[hang]]),
      (p, some lpTy, .call "l2r_promise_new" #[.named z] #[.var c])], ← wrapIOResult resTy v⟩)
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
      ← wrapIOResult (← lowerType ret) .unitVal⟩)
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

/-- The functions that run tasks handed over by the runtime, dispatching on
their state type's tag: `l2r_task_run_one()` (the next queued task: 1 if
there was one), `l2r_run_pending_tasks()` (the final run of queued tasks
when `main` has returned), `l2r_task_walk()` (the `sync` dependents of a
task that just finished, in Lean's walk order; `l2r_task_walk_if(e)` when
`l2r_task_end` said so) and `l2r_task_force_sources(a)` (the chain of
pending tasks that task `a` waits for, deepest first, or queued tasks while
it waits for a promise), `l2r_task_run_before(h, a)` (the tasks walk `h`
of a constant collected that natively run before task `a`). Each runs its task as a worker would
(`taskStepFn`), or drops it when the runtime says it is deleted (a pure
task the program has dropped), then asks again. Generated once every task
type is known. -/
def taskDispatchFns : LowerM (Array RR.Item) := do
  let tags ← getPart (·.taskTags)
  let u64 := RR.Ty.named "u64"
  let mk (name : String) (params : Array (String × RR.Ty)) (first : RR.Expr) (take : String) (again : RR.Expr) :
      LowerM RR.Item := do
    let mut chain : RR.Block := ⟨#[("none", some u64, .atom "0")], .var "none"⟩
    for i in [:tags.size] do
      let j := tags.size - 1 - i
      let z := tags[j]!
      let step ← taskStepFn z
      chain := ⟨#[(s!"k{j}", some u64, .atom (toString j))], .ite (.atom s!"tag == k{j}")
        ⟨#[("c", some (.app "LCell" #[.named z]), .call take #[.named z] #[]),
          ("d", some .bool, .call "l2r_task_deleting" #[] #[]),
          ("v", some u64, .ite (.var "d") ⟨#[("z", some u64, .atom "0")], .var "z"⟩
            (.ofExpr (.call step #[] #[.var "c"])))], again⟩ chain⟩
    return .fn name params u64 ⟨#[("tag", some u64, first)], .block chain⟩
  let ifOne (x : String) (yes : RR.Expr) : RR.Block :=
    ⟨#[("one", some u64, .atom "1")], .ite (.atom s!"{x} == one") (.ofExpr yes) ⟨#[("z", some u64, .atom "0")], .var "z"⟩⟩
  return #[
    ← mk "l2r_task_run_one" #[] (.call "l2r_task_next_tag" #[] #[]) "l2r_task_take" (.atom "1"),
    .fn "l2r_run_pending_tasks" #[] u64 ⟨#[("r", some u64, .call "l2r_task_run_one" #[] #[])],
      .block (ifOne "r" (.call "l2r_run_pending_tasks" #[] #[]))⟩,
    ← mk "l2r_task_walk" #[] (.call "l2r_task_walk_next" #[] #[]) "l2r_task_handed" (.call "l2r_task_walk" #[] #[]),
    .fn "l2r_task_walk_if" #[("e", u64)] u64 (ifOne "e" (.call "l2r_task_walk" #[] #[])),
    ← mk "l2r_task_force_sources" #[("a", u64)] (.call "l2r_task_source_next_at" #[] #[.var "a"]) "l2r_task_handed"
      (.call "l2r_task_force_sources" #[] #[.var "a"]),
    -- The walk of a constant for its tasks (`l2r_persist_T`): before it
    -- waits for task `a`, the tasks it collected that natively run before
    -- it (`leanrt::persist::before`).
    ← mk "l2r_task_run_before" #[("h", u64), ("a", u64)] (.call "l2r_persist_before_at" #[] #[.var "h", .var "a"])
      "l2r_task_handed" (.call "l2r_task_run_before" #[] #[.var "h", .var "a"]),
    -- The runtime's scheduler starts queued tasks on contexts of their own
    -- (`leanrt::sched`) through this entry point, and walks the dependents
    -- of promises dropped inside a free once it is over through the next.
    .raw "extern \"C\" trampoline \"l2r_task_run_one_c\" = l2r_task_run_one;\n",
    .raw "extern \"C\" trampoline \"l2r_task_walk_c\" = l2r_task_walk;\n"]

end LeanToReussir
