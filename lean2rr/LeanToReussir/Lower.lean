import Lean
import LeanToReussir.MonoTypesKeep
import LeanToReussir.LowerBase

/-!
# Stage 4: lowering mono LCNF to Reussir

Translation plan §5.2–§5.8. Code is lowered declaration by declaration:

* calls follow Lean's arities exactly (§5.2): a saturated call is a direct
  call, a partial application becomes a chain of single-parameter lambdas
  that calls the function only when its last argument arrives, and an
  over-application calls and then applies the result;
* closure values are curried and applied one argument at a time (§5.3);
* `cases` becomes `if`, `match` or field access (§5.5);
* join points are inlined (J1), turned into a structured `let` (J2), or
  outlined into a function called in tail position (J3) (§5.6);
* conversions to and from `Box` are inserted where a value's type differs
  from the type its use expects.
-/

namespace LeanToReussir
open Lean Compiler LCNF

/-- How a jump to a join point is lowered. -/
inductive JumpAction where
  /-- J1: the join point has a single jump; its body is inlined there. -/
  | inline (params : Array (Param .pure)) (body : Code .pure)
  /-- J2: jumps produce the join point's arguments as the value of the
  enclosing structured `let`. -/
  | yield (tys : Array RR.Ty)
  /-- J3: jumps call the outlined function with the captured variables
  followed by the arguments. -/
  | call (fn : String) (captured : Array String)
  /-- J4: jumps re-enter the declaration's state machine at the join point's
  variant (see `StateMachine`). -/
  | enter (variant : String) (captured : Array String)

/-- A self-recursive declaration with outlined join points is lowered as one
function over a `[value]` enum of entry points (J4, translation plan §5.6):
the declaration's own entry and one variant per outlined join point. Jumps to
those join points and self tail calls become self tail calls of that
function, which LLVM turns into a loop; separate functions would make the
loop mutually recursive. -/
structure StateMachine where
  /-- The dispatching function: the declaration's parameters, then the
  entry point. -/
  fn : String
  /-- The entry-point enum: nullary `e` for the declaration itself (no
  allocation), one variant per outlined join point. -/
  mode : String
  /-- The declaration, whose tail calls re-enter at `entry`. -/
  self : Name
  arity : Nat
  /-- Names of the declaration's parameters, passed through unchanged when
  entering a join point. -/
  params : Array String
  entry : String := "e"

/-- A matched value that stays live in its arm, whose fields are bound where
they are used (see `lowerCases`). `fields` are the arm's field parameters
that the arm uses, with their binder index and type; `pending` those not
bound yet. -/
structure LazyMatch where
  discr : FVarId
  scrut : String
  ty : String
  variant : String
  nbinders : Nat
  fields : Array (FVarId × Nat × RR.Ty)
  pending : Array (FVarId × Nat × RR.Ty)
  /-- A structure: its pending fields are projected where they are used
  (Reussir has no structure patterns). -/
  struct : Bool := false

structure CodeCtx where
  vars : Std.HashMap FVarId (String × RR.Ty) := {}
  jumps : Std.HashMap FVarId JumpAction := {}
  /-- Types of join-point parameters, for lowering jump arguments. -/
  jpParams : Std.HashMap FVarId (Array RR.Ty) := {}
  sm : Option StateMachine := none
  /-- Matched values whose fields are bound lazily (outermost first). -/
  lazy : Array LazyMatch := #[]
  /-- Bodies of the join points in scope. -/
  jpBodies : Std.HashMap FVarId (Code .pure) := {}

/-! ## Function values

A Lean function value of (lowered, curried) type `T = A₁ → … → Aₙ → R` is
a value of a generated shared enum `L2RFn_…` (translation plan §5.3), not
a Reussir closure: applying a shared Reussir closure copies it, and
curried application allocates a closure per argument. The variants:
- `z`: the `box(0)` placeholder, a function that is never applied (an
  application returns the zero of its result type);
- `raw(A₁ -> …)`: a Reussir closure (built by glue code);
- `p<m>_<id>(c₁, …, cₘ)`: target `id` (a declaration, extern, constructor
  or stream primitive) with its first `m` arguments captured;
- `w<S>(g)`: a function value `g` of another representation `S` of the same
  Lean type, converted at each application.
Applying `j` arguments calls a generated `l2r_ap<j>_…` that matches the
variant. A target whose remaining arity is `j` is called directly and
nothing is allocated, as with `lean_apply_n` at exact arity; with fewer
arguments a new `p` value is built (a partial application); with more, the
result is applied to the rest. The application functions and the enums are
generated at the end (`finishFnValues`), when all variants are known. -/

/-- Parameter types of a function type's curried chain, and its result. -/
partial def fnChain (t : RR.Ty) : Array RR.Ty × RR.Ty :=
  go t #[]
where
  go : RR.Ty → Array RR.Ty → Array RR.Ty × RR.Ty
    | .fn d c, acc => go c (acc.push d)
    | t, acc => (acc, t)

/-- The type of a value of function type `t` applied to `j` arguments. -/
def fnResult : RR.Ty → Nat → RR.Ty
  | t, 0 => t
  | .fn _ c, j + 1 => fnResult c j
  | t, _ => t

def fnVariantName : FnVariant → String
  | .part id m => s!"p{m}_{id}"
  | .wrap src => s!"w{src.enc}"

def applyFnName (t : RR.Ty) (j : Nat) : String := s!"l2r_ap{j}_{t.enc}"

def addFnVariant (t : RR.Ty) (v : FnVariant) : LowerM Unit := do
  let vs := (← get).fnVariants.getD t #[]
  unless vs.contains v do
    modify fun s => { s with fnVariants := s.fnVariants.insert t (vs.push v) }

/-- `f`, of function type `t`, applied to `args` (at `t`'s parameter types;
at most the chain length). -/
def applyCall (f : RR.Expr) (t : RR.Ty) (args : Array RR.Expr) : LowerM RR.Expr := do
  let j := args.size
  unless (← get).fnApplies.contains (t, j) do
    modify fun s => { s with fnApplies := s.fnApplies.push (t, j) }
  return .call (applyFnName t j) #[] (#[f] ++ args)

/-- A function value of type `t = A → B` from a Reussir lambda
`|x : A| body`, where `body : B`. -/
def rawFnValue (t : RR.Ty) (x : String) (body : RR.Block) : RR.Expr :=
  match t with
  | .fn d _ => .ctor (RR.fnTypeName t) (some "raw") #[.lam x d body]
  | _ => .lam x t body

/-- The type of target `tg` with its first `m` arguments captured. -/
def partTy (tg : FnTarget) (m : Nat) : RR.Ty :=
  tg.params[m:].toArray.foldr (fun a b => RR.Ty.fn a b) tg.ret

/-- Target `tg` with its first arguments `captured` (at `tg`'s parameter
types; fewer than all of them), and the value's type. -/
def partValue (tg : FnTarget) (captured : Array RR.Expr) : LowerM (RR.Expr × RR.Ty) := do
  unless (← get).fnTargets.contains tg.id do
    modify fun s => { s with fnTargets := s.fnTargets.insert tg.id tg }
  let t := partTy tg captured.size
  let v := FnVariant.part tg.id captured.size
  addFnVariant t v
  return (.ctor (RR.fnTypeName t) (some (fnVariantName v)) captured, t)

/-- `l2r_fconv_S_T(f)`: function value `f : S` at representation `T`. A
value that is itself a wrapped value of another representation `R`
(`w<R>(g)`) is converted from `R` directly (`g` itself when `R` is `T`), so
that a value converted back and forth (a structure field crossing uniform
code in a loop) is not wrapped again each time; otherwise it is wrapped
(`w<S>`). The body is generated at the end (`genFnConv`). -/
def fnConvFn (src dst : RR.Ty) : LowerM String := do
  unless (← get).fnConvs.contains (src, dst) do
    modify fun s => { s with fnConvs := s.fnConvs.push (src, dst) }
  return s!"l2r_fconv_{src.enc}_{dst.enc}"

/-- The generated function unboxing a `Box` to function type `t` (its body
is generated at the end, with the other unboxing functions). -/
def unboxFnFn (t : RR.Ty) : LowerM String := do
  unless (← get).fnUnboxTargets.contains t do
    modify fun s => { s with fnUnboxTargets := s.fnUnboxTargets.push t }
  return s!"l2r_unbox_fn_{t.enc}"

/-! ## Thunks and tasks: forcing

A `Thunk α` or `Task α` is a runtime cell `LCell<S>` holding a generated
state `S { pending(L2RUnit -> α), busy, done(α), conv(L2RUnit -> α, Box,
u64), busyconv(u64), convdone(α, Box, u64) }` (`lazyState`, translation plan
§5.14). The functions below are generated once per state type. -/

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

/-- `l2r_task_addr_S(c)`: a task's identity for the runtime (`leanrt::task`):
the address of its cell, or the original's that a converted task records
(`lazyConv`) until it has run itself. -/
def taskAddrFn (z : String) : LowerM String := do
  let name := s!"l2r_task_addr_{z}"
  lazyFn name do
    let zt := RR.Ty.named z
    let body : RR.Block := .ofExpr (.mtch (.call "l2r_lcell_get" #[zt] #[.var "c"]) #[
      lazyArm z "conv" #[none, none, some "a"] (.ofExpr (.var "a")),
      lazyArm z "busyconv" #[some "a"] (.ofExpr (.var "a")),
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
(translation plan §5.14). A `conv` state (see `lazyConv`) is forced like a pending one. A task is
also registered as running for the duration (`IO.checkCanceled`, and it
leaves the queue of pending tasks), and runs with its own standard streams,
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
    -- forever then). A converted copy being forced (`busyconv`) runs as a
    -- task of its own cell (`l2r_task_begin`), so it is waited for by that
    -- cell's address too.
    let busy : RR.Block := if task then
        ⟨#[("wb", some u64, .call "l2r_task_wait_running" #[] #[.call "l2r_lcell_addr" #[zt] #[.var "c"]])],
          .call get #[] #[.var "c"]⟩
      else .ofExpr (.call "l2r_lazy_cycle" #[t] #[])
    let getWith (other : RR.Block) : RR.Block := .ofExpr (.mtch (.call "l2r_lcell_get" #[zt] #[.var "c"]) #[
      lazyArm z "done" #[some "v"] (.ofExpr (.var "v")),
      lazyArm z "convdone" #[some "v", none, none] (.ofExpr (.var "v")),
      lazyArm z "busy" #[] busy,
      lazyArm z "busyconv" #[none] busy,
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
    let force ← applyCall (.var "f") (.fn .unit t) #[.unitVal]
    -- The computed state: `done(v)`, or for a converted cell `convdone`,
    -- which keeps the original and its identity (see `addrOf`).
    let lets (final : RR.Expr) : Array (String × Option RR.Ty × RR.Expr) :=
      (if task then #[("b", some u64, onCell "l2r_task_begin"), ("se", some u64, .call "l2r_std_enter_if" #[] #[.var "b"])]
        else #[]) ++
      #[("v", some t, force),
        ("s", some u64, .call "l2r_lcell_set" #[zt] #[.var "c", final])] ++
      (if task then #[("e", some u64, onCell "l2r_task_end"), ("wk", some u64, .call "l2r_task_walk_if" #[] #[.var "e"]),
          ("sl", some u64, .call "l2r_std_leave_if" #[] #[.var "b"])]
        else #[])
    let doneV := RR.Expr.ctor z (some "done") #[.var "v"]
    -- A `bind` task runs `f` (`taskBindStepFn`): it has then finished, or
    -- waits for the task it continues as; either way it is needed now.
    let bindArm : Array RR.Arm := if task then
        #[lazyArm z "bind" #[some "g"] ⟨#[("bs", some u64, .call bindStep #[] #[.var "c", .var "g"])],
          .call get #[] #[.var "c"]⟩]
      else #[]
    let runBody : RR.Block := .ofExpr (.mtch (.call "l2r_lcell_swap" #[zt] #[.var "c", .ctor z (some "busy") #[]]) (#[
      lazyArm z "pending" #[some "f"] ⟨lets doneV, .var "v"⟩,
      lazyArm z "conv" #[some "f", some "o", some "a"]
        ⟨#[("ba", some u64, .call "l2r_lcell_set" #[zt] #[.var "c", .ctor z (some "busyconv") #[.var "a"]])] ++
            lets (.ctor z (some "convdone") #[.var "v", .var "o", .var "a"]),
          .var "v"⟩] ++ bindArm ++ #[
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

/-! ## Conversions -/

/-- Head constant of the Lean type a generated nominal type represents. -/
def nominalHead (n : String) : LowerM (Option Name) := do
  match (← get).typeKeys[n]? with
  | some k => return k.getAppFn.constName?
  | none => return none

/-- Whether a value of type `t` may contain a task (in fields, array
elements, a task's value, a thunk, a function value's captured values, a
`Box`'s payload), as far as can be told before all variants of function
types and `Box` are known: those, and thunks, may. Types already being
examined count as not containing one (the least fixed point, for recursive
types). -/
partial def mayHoldTask (t : RR.Ty) (seen : List RR.Ty := []) : LowerM Bool := do
  if seen.contains t then return false
  let seen := t :: seen
  match t with
  | .app "LCell" _ => return (← lazyOf? t).isSome
  | .app "RVec" #[st] => mayHoldTask st seen
  | .fn .. => return true
  | .named n =>
    if n == boxName then return true
    if let some info := (← get).typeInfos[n]? then
      for c in info.ctorOrder do
        let some l := info.ctors.find? c | continue
        for ft in l.posTys do
          if ← mayHoldTask ft seen then return true
      return false
    match (← get).tupleTypes.toList.find? (·.2 == n) with
    | some (k, _) =>
      let fields := if k.size == 2 && k[1]! == .named "__elem_box" then #[k[0]!] else k
      for ft in fields do
        if ← mayHoldTask ft seen then return true
      return false
    | none => return false
  | _ => return false

/-- The name of the traversal of values of type `t` for tasks
(`finishPersistFns`). -/
def persistFnName (t : RR.Ty) : String := s!"l2r_persist_{t.enc}"

/-- `l2r_persist_T(v)` for the value `v : t` of a constant when it is first
computed, if `t` may contain tasks: native Lean calls `lean_mark_persistent`
on a closed term when it is first evaluated (`lean_obj_once_cold`), which
waits for every task it reaches (`lean_task_get`), through fields, arrays,
the values of tasks, thunks (their computation, or their value: not
forcing them), closures (their captured values) and boxed values. A
`Task.spawn` extracted as a closed term has finished once the term has
been evaluated. The traversal is generated at the end
(`finishPersistFns`). -/
def persistCall (t : RR.Ty) (v : RR.Expr) : LowerM (Option RR.Expr) := do
  unless ← mayHoldTask t do return none
  unless (← get).persistReqs.contains t do
    modify fun s => { s with persistReqs := s.persistReqs.push t }
  return some (.call (persistFnName t) #[] #[v])

/-- The accessor of a constant (a declaration without parameters): its value
is computed once, by `<name>_init`, and kept in a runtime once-cell for the
rest of the run, like native Lean's CAFs and closed terms (translation plan
§5.12). The cell stores a boundary type; other values are boxed. A value
that may contain tasks first waits for them (`persistCall`). -/
def cafAccessor (name : String) (ret : RR.Ty) : LowerM RR.Item := do
  let slot := (← get).cafSlots
  modify fun s => { s with cafSlots := slot + 1 }
  let (st, boxed) ← arrayElemTy ret
  let wrap (e : RR.Expr) : RR.Expr := match st with
    | .named bn => if boxed then .ctor bn none #[e] else e
    | _ => e
  let unwrap (e : RR.Expr) : RR.Expr := if boxed then .field e 0 else e
  let k := RR.Expr.atom (toString slot)
  let init := RR.Expr.call (name ++ "_init") #[] #[]
  let init := match ← persistCall ret (.var "v") with
    | some p => RR.Expr.block ⟨#[("v", some ret, init), ("p", some (.named "u64"), p)], .var "v"⟩
    | none => init
  -- `l2r_once_claim`: a context of the runtime's scheduler that needs the
  -- value while another computes it waits for it.
  let body : RR.Block := .ofExpr (.ite (.call "l2r_once_claim" #[] #[k])
    (.ofExpr (unwrap (.call "l2r_once_get" #[st] #[k])))
    (.ofExpr (unwrap (.call "l2r_once_set" #[st] #[k, wrap init]))))
  return .fn name #[] ret body

/-- A placeholder of Reussir type `t`. Lean passes `box(0)` for values that
are never inspected: erased arguments (`◾`) at relevant types, and the
`unsafeCast ()` its library stores into array slots so that the element
being updated stays unshared (`Array.modifyMUnsafe`, `Array.mapMUnsafe`).
lean2rr materializes `box(0)` at the expected type as that type's zero:
`0`, `false`, the first constructor whose fields have zeros, a closure
returning a zero, an empty array (for `Nat`, `Bool` and enumerations this is
exactly what `box(0)` denotes in Lean). Only a type without a finite value
gets `l2r_unreachable`. Each placeholder is a generated function
`l2r_zero_N`. A placeholder that would allocate (a string, an array, a
record, a closure, a boxed unit) is built once and kept in a once-cell like
a constant (`cafAccessor`): `Array.modify` stores one per update, and it is
never inspected, so a shared value does as well as a fresh one. -/
partial def zeroValue (t : RR.Ty) : LowerM RR.Expr := do
  if t == .unit then return .unitVal
  if let some f := (← get).zeroFns[t]? then return .call f #[] #[]
  let f ← fresh "l2r_zero_"
  modify fun s => { s with zeroFns := s.zeroFns.insert t f, zeroBusy := s.zeroBusy.insert t }
  let lit (text : String) : RR.Block := ⟨#[("z", some t, .atom text)], .var "z"⟩
  let unreachable : RR.Block := .ofExpr (.call "l2r_unreachable" #[t] #[])
  let body : RR.Block ← match t with
    | .named n =>
      if n ∈ ["u8", "u16", "u32", "u64", "i8", "i16", "i32", "i64"] then pure (lit "0")
      else if n ∈ ["f32", "f64"] then pure (lit "0.0")
      else if n == "bool" then pure (.ofExpr (.atom "false"))
      else if n == "Nat" then
        pure ⟨#[("z", some (.named "u64"), .atom "0")], .ctor "Nat" (some "Small") #[.var "z"]⟩
      else if n == "Int" then
        pure ⟨#[("z", some (.named "i64"), .atom "0")], .ctor "Int" (some "Small") #[.var "z"]⟩
      else if n == "LStr" then pure (.ofExpr (← strLit ""))
      else if n == "LNatArr" then pure (.ofExpr (.call "l2r_natarr_empty" #[] #[]))
      else if n == "LIntArr" then pure (.ofExpr (.call "l2r_intarr_empty" #[] #[]))
      else if n == boxName then
        pure (.ofExpr (.ctor boxName (some (← boxVariant .unit)) #[.unitVal]))
      else if let some (e, k) := (← get).refInfos[n]? then
        -- A reference (never used: any cell will do).
        if (← get).zeroBusy.contains e then pure unreachable
        else pure (.ofExpr (refNew t e k (← zeroValue e)))
      else if let some info := (← get).typeInfos[n]? then
        -- The first constructor none of whose fields is a type whose
        -- placeholder is being built (so the value is finite).
        let busy := (← get).zeroBusy
        let ok (tys : Array RR.Ty) := tys.all fun ft => !busy.contains ft
        let fieldsOf (layout : CtorLayout) := layout.posTys
        let cands := info.ctorOrder.filterMap info.ctors.find?
        match cands.find? (fieldsOf · |>.isEmpty) <|> cands.find? (ok ∘ fieldsOf) with
        | some layout =>
          let vals ← (fieldsOf layout).mapM zeroValue
          pure <| .ofExpr <| match info.shape with
            | .struct => .ctor n none vals
            | _ => .ctor n (some layout.variant) vals
        | none => pure unreachable
      else
        -- Generated positional structs (`Tuple…`, `ElemBox…`).
        match (← get).tupleTypes.toList.find? (·.2 == n) with
        | some (k, _) =>
          let fields := if k.size == 2 && k[1]! == .named "__elem_box" then #[k[0]!] else k
          if fields.any (← get).zeroBusy.contains then pure unreachable
          else pure (.ofExpr (.ctor n none (← fields.mapM zeroValue)))
        | none => pure unreachable
    | .app "RVec" #[e] => pure (.ofExpr (.call "l2r_array_empty" #[e] #[]))
    | .app "LCell" _ =>
      match ← lazyOf? t with
      | some (z, _, vt) =>
        if (← get).zeroBusy.contains vt then pure unreachable
        else pure (.ofExpr (lazyDone z (← zeroValue vt)))
      | none => pure unreachable
    -- A function value that is never applied (applying it gives a zero).
    | .fn .. => pure (.ofExpr (.ctor (RR.fnTypeName t) (some "z") #[]))
    | _ => pure unreachable
  modify fun s => { s with zeroBusy := s.zeroBusy.erase t }
  -- Heap values are shared (a nullary constructor of a shared enum does not
  -- allocate).
  let heap ← match t with
    | .named n =>
      if n ∈ ["LStr", "LNatArr", "LIntArr", boxName] || (← get).refInfos.contains n then pure true
      else match (← get).typeInfos[n]? with
        | some info => pure (info.shape != .enumLike && !info.value)
        | none => pure ((← storageElem t).2)
    | .app "RVec" _ | .fn .. => pure true
    | _ => pure false
  let nullary := match body with
    | ⟨#[], .ctor _ _ #[]⟩ => true
    | _ => false
  if heap && !nullary then
    let acc ← cafAccessor f t
    modify fun s => { s with fns := s.fns.push (.fn (f ++ "_init") #[] t body) |>.push acc }
  else
    modify fun s => { s with fns := s.fns.push (.fn f #[] t body) }
  return .call f #[] #[]

/-- The index of a value of an enumeration type (a generated `[value]`
enum without fields), as `u64`: a generated `match`. -/
def enumIndexFn (tn : String) : LowerM String := do
  let name := s!"l2r_enum_index_{tn}"
  unless (← get).fns.any (fun | .fn n .. => n == name | _ => false) do
    let some info := (← get).typeInfos[tn]? | throwError "lean2rr: no enumeration {tn}"
    let arms := info.ctorOrder.zipIdx.filterMap fun (c, i) => (info.ctors.find? c).map fun l =>
      { ty := tn, ctor := some l.variant, binders := #[], body := ⟨#[("i", some (.named "u64"), .atom (toString i))], .var "i"⟩ : RR.Arm }
    let body : RR.Block := if arms.isEmpty then .ofExpr (.call "l2r_unreachable" #[.named "u64"] #[])
      else .ofExpr (.mtch (.var "x") arms)
    modify fun s => { s with fns := s.fns.push (.fn name #[("x", .named tn)] (.named "u64") body) }
  return name

/-- The value of enumeration type `tn` with index `i : u64` (a generated
chain of comparisons). -/
def enumOfIndexFn (tn : String) : LowerM String := do
  let name := s!"l2r_enum_of_index_{tn}"
  unless (← get).fns.any (fun | .fn n .. => n == name | _ => false) do
    let some info := (← get).typeInfos[tn]? | throwError "lean2rr: no enumeration {tn}"
    let ls := info.ctorOrder.filterMap info.ctors.find?
    let some last := ls.back? | do
      -- No values: the conversion is unreachable.
      modify fun s => { s with fns := s.fns.push (.fn name #[("x", .named "u64")] (.named tn)
        (.ofExpr (.call "l2r_unreachable" #[.named tn] #[]))) }
      return name
    let mut e : RR.Expr := .ctor tn (some last.variant) #[]
    for j in [:ls.size - 1] do
      let i := ls.size - 2 - j
      let some l := ls[i]? | continue
      e := .block ⟨#[("k", some (.named "u64"), .atom (toString i))],
        .ite (.atom "x == k") (.ofExpr (.ctor tn (some l.variant) #[])) (.ofExpr e)⟩
    modify fun s => { s with fns := s.fns.push (.fn name #[("x", .named "u64")] (.named tn) (.ofExpr e)) }
  return name

/-- Unwrap a `Box` whose variant for Reussir type `t` is fixed by the Lean
types: the variant's payload, or, for a boxed unit, the placeholder of `t`
(a boxed unit used at another type is Lean's `box(0)`, see `zeroValue`); any
other variant is unreachable. -/
def unboxMatch (e : RR.Expr) (t : RR.Ty) (slow : Option String := none) : LowerM RR.Expr := do
  let v ← boxVariant t
  let u ← boxVariant .unit
  let x ← fresh "ub"
  let mut arms : Array RR.Arm :=
    #[{ ty := boxName, ctor := some v, binders := #[some x], body := .ofExpr (.var x) }]
  if u != v then
    arms := arms.push { ty := boxName, ctor := some u, binders := #[none], body := .ofExpr (← zeroValue t) }
  -- Other variants: unreachable, or the generated unboxing function `slow`
  -- (values of other types read through `unsafeCast`).
  let (e, pre) ← match slow, e with
    | none, _ | some _, .var _ => pure (e, #[])
    | some _, _ => do
      let b ← fresh "ubx"
      pure (RR.Expr.var b, #[(b, some RR.Ty.box, e)])
  let other : RR.Expr := match slow with
    | some f => .call f #[] #[e]
    | none => .call "l2r_unreachable" #[t] #[]
  let m := RR.Expr.mtch e (arms.push { ty := boxName, ctor := none, binders := #[], body := .ofExpr other })
  return if pre.isEmpty then m else .block ⟨pre, m⟩

/-- An enumeration: `bool`, or a generated `[value]` enum without fields. -/
def isEnumName (n : String) : LowerM Bool := do
  if n == "bool" then return true
  return ((← get).typeInfos[n]?.map (·.shape == .enumLike)).getD false

/-- The word `lean_unbox` gives for value `e` of Reussir type `n` natively
represented by a boxed scalar of its own (`UInt8/16/32`, `Char`, `Bool`, an
enumeration: its index), as `u64`. `none` for other types. -/
def scalarWord (e : RR.Expr) (n : String) : LowerM (Option RR.Expr) := do
  let u64 := RR.Ty.named "u64"
  if n ∈ ["u8", "u16", "u32"] then return some (.cast e u64)
  if n == "bool" then
    let o ← fresh "ix"
    return some (.ite e ⟨#[(o, some u64, .atom "1")], .var o⟩ ⟨#[(o, some u64, .atom "0")], .var o⟩)
  if ← isEnumName n then return some (.call (← enumIndexFn n) #[] #[e])
  return none

/-- Whether a generated type has a constructor without relevant fields
(natively the boxed scalar of its index). -/
def hasNullaryCtor (info : TypeInfo) : Bool :=
  info.ctorOrder.any fun c => (info.ctors.find? c).any (·.fields.all Option.isNone)

/-- `l2r_ctor_word_T(x)`: the index of a constructor without fields of
generated type `tn`, which natively is the boxed scalar of its index; a
value with fields is an object (its "word" an address): unreachable. -/
def ctorWordFn (tn : String) (info : TypeInfo) : LowerM String := do
  let name := s!"l2r_ctor_word_{tn}"
  unless (← get).fns.any (fun | .fn n .. => n == name | _ => false) do
    let u64 := RR.Ty.named "u64"
    let mut arms : Array RR.Arm := #[]
    for h : i in [:info.ctorOrder.size] do
      let some l := info.ctors.find? info.ctorOrder[i] | continue
      if l.fields.all Option.isNone then
        arms := arms.push { ty := tn, ctor := some l.variant, binders := #[], body := ⟨#[("i", some u64, .atom (toString i))], .var "i"⟩ }
    arms := arms.push { ty := tn, ctor := none, binders := #[], body := .ofExpr (.call "l2r_unreachable" #[u64] #[]) }
    modify fun s => { s with fns := s.fns.push (.fn name #[("x", .named tn)] u64 (.ofExpr (.mtch (.var "x") arms))) }
  return name

/-- `l2r_ctor_of_word_T(w)`: the value of generated type `tn` that is the
boxed scalar `w` natively: its constructor `w` when that has no fields (a
word past the last constructor selects the last one, as Lean's `switch`
does); otherwise unreachable (natively an object read from a scalar). -/
def ctorOfWordFn (tn : String) (info : TypeInfo) : LowerM String := do
  let name := s!"l2r_ctor_of_word_{tn}"
  unless (← get).fns.any (fun | .fn n .. => n == name | _ => false) do
    let u64 := RR.Ty.named "u64"
    let t := RR.Ty.named tn
    let ls := info.ctorOrder.filterMap info.ctors.find?
    let nullary (l : CtorLayout) := l.fields.all Option.isNone
    let mk (l : CtorLayout) : RR.Expr := if info.shape == .struct then .ctor tn none #[] else .ctor tn (some l.variant) #[]
    let unreachable := RR.Expr.call "l2r_unreachable" #[t] #[]
    let mut e : RR.Expr := match ls.back? with
      | some l => if nullary l then .block ⟨#[("k", some u64, .atom (toString (ls.size - 1)))],
          .ite (.atom "w >= k") (.ofExpr (mk l)) (.ofExpr unreachable)⟩ else unreachable
      | none => unreachable
    for j in [:ls.size - 1] do
      let i := ls.size - 2 - j
      let some l := ls[i]? | continue
      if !nullary l then continue
      e := .block ⟨#[("k", some u64, .atom (toString i))], .ite (.atom "w == k") (.ofExpr (mk l)) (.ofExpr e)⟩
    modify fun s => { s with fns := s.fns.push (.fn name #[("w", u64)] t (.ofExpr e)) }
  return name

/-- The word `lean_unbox` gives natively for value `e` of Reussir type `n`
(`unsafeCast` to a scalar reads it): a `Nat`'s value (`lean_usize_of_nat`;
for a big one, natively an address, its low bits), an `Int`'s 32 bits
(`l2r_int_word`), the index of an enumeration or of a constructor without
fields, a fixed-width integer's value. `none` for other types. -/
def wordOf (e : RR.Expr) (n : String) : LowerM (Option RR.Expr) := do
  if n == "Nat" then return some (.call "lean_usize_of_nat" #[] #[e])
  if n == "Int" then return some (.call "l2r_int_word" #[] #[e])
  if let some w ← scalarWord e n then return some w
  if let some info := (← get).typeInfos[n]? then
    if !info.value && hasNullaryCtor info then return some (.call (← ctorWordFn n info) #[] #[e])
  return none

/-- The value of Reussir type `n` that natively is the boxed scalar of word
`w : u64` (see `wordOf`): `Nat` `w`; `Int` the signed value of its 32 bits
(`lean_scalar_to_int64`); a fixed-width integer, `Bool` (nonzero) or an
enumeration the bits of its width (`lean_unbox` then truncation; an index
past the last constructor gives the last one, as Lean's `switch` does); a
constructor without fields (`ctorOfWordFn`). `none` for other types. -/
def ofWord (w : RR.Expr) (n : String) : LowerM (Option RR.Expr) := do
  let u64 := RR.Ty.named "u64"
  if n == "Nat" then return some (.ctor "Nat" (some "Small") #[w])
  if n == "Int" then return some (.call "l2r_int_of_word" #[] #[w])
  if n ∈ ["u8", "u16", "u32"] then return some (.cast w (.named n))
  if n == "bool" then
    let x ← fresh "ix"
    let z ← fresh "iz"
    return some (.block ⟨#[(x, some (.named "u8"), .cast w (.named "u8")), (z, some (.named "u8"), .atom "0")],
      .atom s!"{x} != {z}"⟩)
  if let some info := (← get).typeInfos[n]? then
    if info.shape == .enumLike then
      let size := info.ctorOrder.size
      let mask := if size ≤ 256 then 255 else if size ≤ 65536 then 65535 else 4294967295
      let x ← fresh "ix"
      let m ← fresh "im"
      return some (.block ⟨#[(x, some u64, w), (m, some u64, .atom (toString mask))],
        .call (← enumOfIndexFn n) #[] #[.atom s!"{x} & {m}"]⟩)
    if !info.value && hasNullaryCtor info then return some (.call (← ctorOfWordFn n info) #[] #[w])
  return none

/-- Lean's native layout slot of each field of constructor `c` (Lean's own
`getCtorLayout`): `(0, i, 8)` the `i`-th object field, `(1, i, 8)` the
`i`-th `usize` field, `(2, offset, size)` a scalar in the scalar area;
`none` for a field without data. `none` if Lean has no layout for it. -/
def nativeSlots (c : Name) : LowerM (Option (Array (Option (Nat × Nat × Nat)))) := do
  try
    let l ← Lean.Compiler.LCNF.getCtorLayout c
    return some (l.fieldInfo.map fun
      | .object i _ => some (0, i, 8)
      | .usize i => some (1, i, 8)
      | .scalar sz off _ => some (2, off, sz)
      | _ => none)
  catch _ => return none

/-- Which field of constructor `sc` (layout `sl`, of a value's own type) each
field of constructor `dc` (layout `dl`, of the type the value is cast to)
reads, as natively. Lean stores the object fields of a constructor first,
in declaration order, then the `usize` fields, then the other scalars by
decreasing size (ties in declaration order), so fields correspond by their
native slot, not by declaration position: `S₁ {a : UInt8, b : Nat}` read as
`S₂ {x : Nat, y : UInt8}` is `x = b`, `y = a`. For each Lean field of `dc`:
`none` if it has no representation, `some (some k)` if it reads field `k`
of `sc`, `some none` if the field there has no representation here (a
placeholder: the zero). The result is `none` when a field reads data that
the source does not have, or only part of a scalar. Without native layouts,
relevant fields correspond by position. -/
def castFieldMap (sc dc : Name) (sl dl : CtorLayout) : LowerM (Option (Array (Option (Option Nat)))) := do
  let positional : Option (Array (Option (Option Nat))) := Id.run do
    let srcIdx := (List.range sl.fields.size).toArray.filter fun k => (sl.fields[k]?.join).isSome
    let mut out := #[]
    let mut r := 0
    for f in dl.fields do
      match f with
      | some _ =>
        let some k := srcIdx[r]? | return none
        out := out.push (some (some k))
        r := r + 1
      | none => out := out.push none
    return some out
  let (some ss, some ds) := (← nativeSlots sc, ← nativeSlots dc) | return positional
  if ss.size != sl.fields.size || ds.size != dl.fields.size then return positional
  let mut out := #[]
  for h : j in [:dl.fields.size] do
    if dl.fields[j].isNone then
      out := out.push none
      continue
    match ds[j]! with
    -- No data natively (a field relevant only here): a placeholder.
    | none => out := out.push (some none)
    | some slot =>
      match ss.findIdx? (· == some slot) with
      | some k => out := out.push (some (if (sl.fields[k]?.join).isSome then some k else none))
      | none => return none
  return some out

/-- See `retypable`; `assumed`: pairs of types under comparison. -/
partial def retypableAux (a b : RR.Ty) (assumed : Array (String × String)) :
    LowerM (Option (Array (String × String))) := do
  if a == b then return some assumed
  match a, b with
  | .named an, .named bn =>
    if assumed.contains (an, bn) then return some assumed
    let infos := (← get).typeInfos
    let (some ai, some bi) := (infos[an]?, infos[bn]?) | return none
    if ai.value != bi.value || ai.shape != bi.shape || ai.ctorOrder.size != bi.ctorOrder.size then return none
    let sameHead := (← nominalHead an) == (← nominalHead bn)
    let mut asm := assumed.push (an, bn)
    for (ca, cb) in ai.ctorOrder.zip bi.ctorOrder do
      let (some la, some lb) := (ai.ctors.find? ca, bi.ctors.find? cb) | return none
      let pa := la.posTys
      let pb := lb.posTys
      if pa.size != pb.size then return none
      -- The fields a conversion pairs are at the same record positions.
      if sameHead then
        if la.fields.map (·.map (·.1)) != lb.fields.map (·.map (·.1)) then return none
      else
        let some fm ← castFieldMap ca cb la lb | return none
        for h : j in [:lb.fields.size] do
          let some (p, _) := lb.fields[j] | continue
          let some (some k) := fm[j]?.join | return none
          if (la.fields[k]?.join.map (·.1)) != some p then return none
      for (x, y) in pa.zip pb do
        let some asm' ← retypableAux x y asm | return none
        asm := asm'
    return some asm
  | .app "RVec" #[x], .app "RVec" #[y] =>
    -- Element storage: the same wrapping, wrapped values retypable.
    let (ex, bx) ← storageElem x
    let (ey, by_) ← storageElem y
    if bx != by_ then return none
    retypableAux (if bx then ex else x) (if bx then ey else y) assumed
  | _, _ => return none

/-- Whether a value of Reussir type `a` can be used as a value of type `b`
as it is, the same object reinterpreted (`l2r_retype`): both cross the FFI
boundary (shared records, arrays), and their layouts are the same: records
with the same constructors whose fields, position by position, have the
same layouts (coinductively, for recursive types), arrays of such
elements; the conversion between them (`structConv`, `vecConv`) would pair
exactly those fields. Instantiations of an inductive that differ only in
phantom positions, and isomorphic inductives read through `unsafeCast` (a
user list as `List`), are then not converted at all: no time, no copy, and
the value keeps its identity. -/
def retypable (a b : RR.Ty) : LowerM Bool := do
  if a == b then return false
  if !(← isBoundaryTy a) || !(← isBoundaryTy b) then return false
  match a with
  | .named n => if n == boxName || !(← get).typeInfos.contains n then return false
  | .app "RVec" _ => pure ()
  | _ => return false
  return (← retypableAux a b #[]).isSome

mutual
  /-- Convert `e` from representation `src` to `dst`. Besides `Box`
  conversions and closure wrappers, two instantiations of the same inductive
  are converted structurally: Lean's mono `cse` compares erased types, so it
  may merge e.g. `[] : List Shape` with `[] : List Nat`; such a merged value
  carries no data at the differing type parameter, so rebuilding it at the
  target type is always possible (an arm that would need an impossible
  element conversion is unreachable). -/
  partial def coerce (e : RR.Expr) (src dst : RR.Ty) : LowerM RR.Expr := do
    match ← tryCoerce e src dst with
    | some r => return r
    | none =>
      let keyOf (t : RR.Ty) : LowerM String := do
        match t with
        | .named n => return match (← get).typeKeys[n]? with | some k => s!"{n} = {k}" | none => n
        | _ => return t.render
      -- No conversion: only reachable through an `unsafeCast` between
      -- types whose values Lean represents alike but lean2rr does not.
      -- The program is still translated; the cast panics if executed.
      IO.eprintln s!"lean2rr: warning: no representation conversion from {← keyOf src} to {← keyOf dst}; the conversion panics at run time"
      return .call "l2r_internal_panic_at" #[dst] #[.atom "0"]

  partial def tryCoerce (e : RR.Expr) (src dst : RR.Ty) : LowerM (Option RR.Expr) := do
    if src == dst then return some e
    -- A function value is boxed as it is; unboxing it to another
    -- representation wraps it (`l2r_unbox_fn_…`), so a function value that
    -- goes through uniform code and back is not wrapped at all.
    if dst == RR.Ty.box then
      return some (.ctor boxName (some (← boxVariant src)) #[e])
    if src == RR.Ty.box then
      match dst with
      | .fn .. => return some (.call (← unboxFnFn dst) #[] #[e])
      | _ =>
        if let .named tn := dst then
          if (← get).typeInfos.contains tn then
            -- Any instantiation of the same inductive may have been boxed,
            -- and (through `unsafeCast`) values of types Lean represents
            -- alike (`boxCastCompatible`).
            return some (.call (← unboxFn tn) #[] #[e])
          if tn ∈ ["Nat", "Int", "u8", "u16", "u32", "bool", "u64", "f64", "f32"] then
            -- The variant of `dst` in line; others (another word type read
            -- through `unsafeCast`) through the generated function.
            return some (← unboxMatch e dst (slow := some (← unboxFn tn)))
        if (← arrayRepr? dst).isSome || dst matches .app "LCell" _ then
          -- Any representation of the same array (or thunk, task) type may
          -- have been boxed.
          return some (.call (← unboxArrFn dst) #[] #[e])
        return some (← unboxMatch e dst)
    match src, dst with
    -- A unit-like value used at another type is an `unsafeCast ()`
    -- placeholder (see `zeroValue`).
    | .named "L2RUnit", _ => return some (← zeroValue dst)
    -- Any value at a unit-like type (an irrelevant position: a proof, a
    -- phantom) carries nothing; it is still evaluated.
    | _, .named "L2RUnit" =>
      let d ← fresh "du"
      return some (.block ⟨#[(d, some src, e)], .unitVal⟩)
    | .fn a1 b1, .fn a2 b2 =>
      -- Another representation of the same function type: wrapped, and
      -- converted at each application.
      let some _ ← tryCoerce (.var "l2rcv") a2 a1 | return none
      let some _ ← tryCoerce (.var "l2rcv") b1 b2 | return none
      addFnVariant dst (.wrap src)
      return some (.call (← fnConvFn src dst) #[] #[e])
    -- Between a function value and a Reussir closure (prelude callbacks):
    -- a lambda. `e` is bound first, so that it is evaluated once.
    | .fn a1 b1, .cls a2 b2 =>
      let (pre, callee) ← match e with
        | .var _ => pure (#[], e)
        | _ => do
          let v ← fresh "cf"
          pure (#[(v, some src, e)], RR.Expr.var v)
      let x ← fresh "cv"
      let some arg ← tryCoerce (.var x) a2 a1 | return none
      let some res ← tryCoerce (← applyCall callee src #[arg]) b1 b2 | return none
      let lam := RR.Expr.lam x a2 (.ofExpr res)
      return some (if pre.isEmpty then lam else .block ⟨pre, lam⟩)
    | .cls a1 b1, .fn a2 b2 =>
      let (pre, callee) ← match e with
        | .var _ => pure (#[], e)
        | _ => do
          let v ← fresh "cf"
          pure (#[(v, some src, e)], RR.Expr.var v)
      let x ← fresh "cv"
      let some arg ← tryCoerce (.var x) a2 a1 | return none
      let some res ← tryCoerce (.apply callee arg) b1 b2 | return none
      let f := rawFnValue dst x (.ofExpr res)
      return some (if pre.isEmpty then f else .block ⟨pre, f⟩)
    | .named sn, .named dn =>
      -- Instantiations of one inductive, or (through `unsafeCast`) another
      -- inductive that Lean represents alike: structurally.
      if let (some sh, some dh) := (← nominalHead sn, ← nominalHead dn) then
        if sh == dh || (← isomorphic sn dn) then
          if ← retypable src dst then return some (.call "l2r_retype" #[src, dst] #[e])
          return some (.call (← structConv sn dn) #[] #[e])
      -- The rest is only reachable through `unsafeCast`, between values that
      -- Lean represents by the same word; the conversions follow Lean's
      -- `lean_box`/`lean_unbox`. Scalars of the same size in a constructor's
      -- scalar area: the bits.
      match sn, dn with
      | "u64", "f64" => return some (.call "lean_float_of_bits" #[] #[e])
      | "f64", "u64" => return some (.call "lean_float_to_bits" #[] #[e])
      | "u32", "f32" => return some (.call "lean_float32_of_bits" #[] #[e])
      | "f32", "u32" => return some (.call "lean_float32_to_bits" #[] #[e])
      -- `Nat` and `Int`: the same value (natively the same boxed scalar for
      -- small values, the same big number object otherwise; a `Nat` from
      -- 2^31 to 2^63 is not a valid small `Int` natively).
      | "Nat", "Int" => return some (.call "lean_nat_to_int" #[] #[e])
      | "Int", "Nat" => return some (.call "l2r_int_cast_nat" #[] #[e])
      | _, _ => pure ()
      -- A `[value]` struct is natively its field.
      let infos := (← get).typeInfos
      if let some si := infos[sn]? then
        if si.value && (← nominalHead sn) != (← nominalHead dn) then
          if let some ft := (si.ctors.find? si.ctorOrder[0]!).bind (·.posTys[0]?) then
            let (pre, v) ← match e with
              | .var _ => pure (#[], e)
              | _ => do
                let x ← fresh "vs"
                pure (#[(x, some src, e)], RR.Expr.var x)
            let some r ← tryCoerce (.field v 0) ft dst | return none
            return some (if pre.isEmpty then r else .block ⟨pre, r⟩)
      if let some di := infos[dn]? then
        if di.value && (← nominalHead sn) != (← nominalHead dn) then
          if let some ft := (di.ctors.find? di.ctorOrder[0]!).bind (·.posTys[0]?) then
            let some v ← tryCoerce e src ft | return none
            return some (.ctor dn none #[v])
      -- Boxed scalars: `Nat`, `Int`, fixed-width integers, `Bool`,
      -- enumerations, constructors without fields.
      if let some w ← wordOf e sn then
        if let some r ← ofWord w dn then return some r
      vecCoerce e src dst
    | .app "LCell" #[.named sz], .app "LCell" #[.named dz] =>
      match ← lazyConv sz dz with
      | some f => return some (.call f #[] #[e])
      | none => return none
    | _, _ => vecCoerce e src dst

  /-- Arrays whose element types differ (an array reinterpreted by Lean's
  uniform-representation code, e.g. `Array α` as `Array NonScalar`): rebuilt
  element by element. -/
  partial def vecCoerce (e : RR.Expr) (src dst : RR.Ty) : LowerM (Option RR.Expr) := do
    let some sr ← arrayRepr? src | return none
    let some dr ← arrayRepr? dst | return none
    if ← retypable src dst then return some (.call "l2r_retype" #[src, dst] #[e])
    match ← vecConv src dst sr dr with
    | some f => return some (.call f #[] #[e])
    | none => return none

  /-- The generated function converting an array with element storage `se`
  to one with element storage `de` (cached). -/
  partial def vecConv (src dst : RR.Ty) (sr dr : ArrayRepr) : LowerM (Option String) := do
    if let some f := (← get).vecConvs[(src, dst)]? then return some f
    let f ← fresh "l2r_vconv_"
    modify fun s => { s with vecConvs := s.vecConvs.insert (src, dst) f }
    let x := sr.load (sr.call "get" #[.var "src", .var "i"])
    -- Elements that cannot be converted (`Array Nat` to `Array Int`) mean
    -- that the array is empty whenever this runs: an empty array that `cse`
    -- shared between two element types, or the array `Array.map` returns
    -- when it had nothing to map (Stage 3).
    let y ← match ← tryCoerce x sr.value dr.value with
      | some y => pure y
      | none => pure (.call "l2r_unreachable" #[dr.value] #[])
    let go := f ++ "_go"
    let u64 := RR.Ty.named "u64"
    let loop : RR.Block := .ofExpr <| .ite (.atom "i < n")
      ⟨#[("one", some u64, .atom "1"), ("y", some dr.storage, dr.store y)],
        .call go #[] #[.var "src", .atom "i + one", .var "n", dr.call "push" #[.var "acc", .var "y"]]⟩
      (.ofExpr (.var "acc"))
    let entry : RR.Block :=
      ⟨#[("n", some u64, sr.call "size" #[.var "src"]), ("zero", some u64, .atom "0")],
        .call go #[] #[.var "src", .var "zero", .var "n", dr.call "empty" #[]]⟩
    modify fun s => { s with fns := s.fns ++ #[
      .fn go #[("src", src), ("i", u64), ("n", u64), ("acc", dst)] dst loop,
      .fn f #[("src", src)] dst entry] }
    return some f

  /-- Whether values of generated type `sn` can be read as values of `dn`
  (through `unsafeCast`, where Lean's representations coincide): the same
  number of constructors, and each field of a constructor of `dn` reads a
  field of the corresponding constructor of `sn` (`castFieldMap`). -/
  partial def isomorphic (sn dn : String) : LowerM Bool := do
    let some si := (← get).typeInfos[sn]? | return false
    let some di := (← get).typeInfos[dn]? | return false
    if si.ctorOrder.size != di.ctorOrder.size then return false
    for (a, b) in si.ctorOrder.zip di.ctorOrder do
      let (some la, some lb) := (si.ctors.find? a, di.ctors.find? b) | return false
      if (← castFieldMap a b la lb).isNone then return false
    return true

  /-- The generated function converting a thunk or task with state type `sz`
  to one with state type `dz` (same kind, value types differing only in
  representation, as for `structConv`). The result is a new cell that
  records the cell it was converted from, boxed, and that cell's address:
  converting it back gives that very cell (a thunk crossing between typed
  and uniform code in a loop does not build a chain of cells), its identity
  is the original's (`ptrAddrUnsafe`, see `addrOf`; for a task also the
  runtime's, `l2r_task_addr_S`), and keeping the original keeps that
  address from being reused. A computed value is converted now (state
  `convdone`). Otherwise the new cell is in state `conv`: its computation
  forces the original and converts the value (so the original's
  computation still runs at most once). A cell converted from a converted
  one records the first original. `none` if the values are not
  convertible. -/
  partial def lazyConv (sz dz : String) : LowerM (Option String) := do
    let some (sk, st) := (← get).lazyInfos[sz]? | return none
    let some (dk, dt) := (← get).lazyInfos[dz]? | return none
    if sk != dk then return none
    let name := s!"l2r_lazyconv_{sz}_{dz}"
    if (← get).lazyFnNames.contains name then return some name
    modify fun s => { s with lazyFnNames := s.lazyFnNames.insert name }
    let fail : LowerM (Option String) := do
      modify fun s => { s with lazyFnNames := s.lazyFnNames.erase name }
      return none
    let some now ← tryCoerce (.var "v") st dt | fail
    let get ← lazyGetFn sz
    let some later ← tryCoerce (.call get #[] #[.var "c"]) st dt | fail
    let srcCell := RR.Ty.app "LCell" #[.named sz]
    let dstCell := RR.Ty.app "LCell" #[.named dz]
    let srcBox ← boxVariant srcCell
    let dstBox ← boxVariant dstCell
    let u ← fresh "u"
    let mkConv (o a : RR.Expr) : RR.Expr := .call "l2r_lcell_new" #[.named dz]
      #[.ctor dz (some "conv") #[rawFnValue (.fn .unit dt) u (.ofExpr later), o, a]]
    let ident : RR.Expr := .call "l2r_lcell_addr" #[.named sz] #[.var "c"]
    let fresh' : RR.Block := ⟨#[("o", some RR.Ty.box, .ctor boxName (some srcBox) #[.var "c"]),
      ("a", some (.named "u64"), ident)], mkConv (.var "o") (.var "a")⟩
    let doneConv : RR.Block := ⟨#[("w", some dt, now), ("o", some RR.Ty.box, .ctor boxName (some srcBox) #[.var "c"]),
      ("a", some (.named "u64"), ident)],
      .call "l2r_lcell_new" #[.named dz] #[.ctor dz (some "convdone") #[.var "w", .var "o", .var "a"]]⟩
    -- From a converted cell: its original if that has the target type,
    -- otherwise the original converted directly (through the `Box`
    -- converter, which knows every representation), so chains through
    -- several representations stay one level deep.
    let back : RR.Expr := .mtch (.var "o") #[
      { ty := boxName, ctor := some dstBox, binders := #[some "x"], body := .ofExpr (.var "x") },
      { ty := boxName, ctor := none, binders := #[], body := .ofExpr (.call (← unboxArrFn dstCell) #[] #[.var "o"]) }]
    let busy : RR.Block := ⟨#[("o", some RR.Ty.box, .ctor boxName (some srcBox) #[.var "c"])], mkConv (.var "o") (.var "a")⟩
    let body : RR.Block := .ofExpr (.mtch (.call "l2r_lcell_get" #[.named sz] #[.var "c"]) #[
      lazyArm sz "done" #[some "v"] doneConv,
      lazyArm sz "conv" #[none, some "o", some "a"] (.ofExpr back),
      lazyArm sz "convdone" #[none, some "o", some "a"] (.ofExpr back),
      lazyArm sz "busyconv" #[some "a"] busy,
      { ty := sz, ctor := none, binders := #[], body := fresh' }])
    modify fun s => { s with fns := s.fns.push (.fn name #[("c", srcCell)] dstCell body) }
    return some name

  /-- The generated function converting instantiation `sn` to `dn` of the
  same inductive (cached). -/
  partial def structConv (sn dn : String) : LowerM String := do
    let fname := s!"l2r_conv_{sn}_{dn}"
    if (← get).fns.any (fun | .fn n .. => n == fname | _ => false) ||
       (← get).convsInProgress.contains fname then return fname
    modify fun s => { s with convsInProgress := s.convsInProgress.insert fname }
    let some si := (← get).typeInfos[sn]? | throwError "lean2rr: no type {sn}"
    let some di := (← get).typeInfos[dn]? | throwError "lean2rr: no type {dn}"
    let mut arms := #[]
    let mut structBody : Option RR.Block := none
    -- Constructors correspond by name (instantiations of one inductive) or
    -- by position (isomorphic inductives, through `unsafeCast`).
    let sameHead := (← nominalHead sn) == (← nominalHead dn)
    for h : ci in [:si.ctorOrder.size] do
      let ctor := si.ctorOrder[ci]
      let some sl := si.ctors.find? ctor | continue
      let dctor := if sameHead then ctor else di.ctorOrder[ci]?.getD ctor
      let some dl := di.ctors.find? dctor | continue
      let srcFields := sl.fields.filterMap id
      let dstFields := dl.fields.filterMap id
      let names ← srcFields.mapM fun _ => fresh "cf"
      let mut vals := #[]
      let mut possible := true
      if sameHead then
        -- Fields by Lean index. A field relevant in the target but not in
        -- the source (a proof-like type such as `PLift p` in one of the
        -- instantiations) was never inspected: its placeholder.
        let srcIdx := (List.range sl.fields.size).toArray.filter fun j => (sl.fields[j]?.join).isSome
        for h : j in [:dl.fields.size] do
          let some (_, dt) := dl.fields[j] | continue
          match sl.fields[j]?.join, srcIdx.idxOf? j with
          | some (_, st), some k =>
            match ← tryCoerce (.var names[k]!) st dt with
            | some v => vals := vals.push v
            | none => possible := false
          | _, _ => vals := vals.push (← zeroValue dt)
      else
        -- Another inductive (through `unsafeCast`): fields by native
        -- layout slot (`castFieldMap`).
        let srcIdx := (List.range sl.fields.size).toArray.filter fun j => (sl.fields[j]?.join).isSome
        match ← castFieldMap ctor dctor sl dl with
        | none => possible := false
        | some fm =>
          for h : j in [:dl.fields.size] do
            let some (_, dt) := dl.fields[j] | continue
            match fm[j]?.join with
            | some (some k) =>
              let some (_, st) := sl.fields[k]?.join | possible := false
              let some r := srcIdx.idxOf? k | possible := false
              match ← tryCoerce (.var names[r]!) st dt with
              | some v => vals := vals.push v
              | none => possible := false
            | _ => vals := vals.push (← zeroValue dt)
      -- Fields are bound from and placed at their record positions.
      let placedVals := dl.place vals
      let body : RR.Block := if possible then
          .ofExpr (match di.shape with
            | .struct => .ctor dn none placedVals
            | _ => .ctor dn (some dl.variant) placedVals)
        else .ofExpr (.call "l2r_unreachable" #[.named dn] #[])
      match si.shape with
      | .struct =>
        structBody := some ⟨(names.zip srcFields).map (fun (n, (p, t)) => (n, some t, RR.Expr.field (.var "x") p)), body.result⟩
      | _ =>
        let mut binders : Array (Option String) := Array.replicate srcFields.size none
        for (n, (p, _)) in names.zip srcFields do binders := binders.set! p (some n)
        arms := arms.push { ty := sn, ctor := some sl.variant, binders, body }
    let body := match structBody with
      | some b => b
      | none => .ofExpr (.mtch (.var "x") arms)
    modify fun s => { s with fns := s.fns.push (.fn fname #[("x", .named sn)] (.named dn) body) }
    return fname
end

/-! ## Declarations and signatures -/

/-- Parameter types and result type of a function type with `n` parameters. -/
def splitFnType (ty : Expr) (n : Nat) : Array Expr × Expr := Id.run do
  let mut ty := ty
  let mut ps := #[]
  for _ in [:n] do
    match ty.consumeMData with
    | .forallE _ d b _ => ps := ps.push d; ty := b.instantiate1 anyExpr
    | _ => break
  return (ps, ty)

/-- What a constant application targets. -/
inductive Callee where
  /-- A declaration with code in the translated program. -/
  | code (fn : String) (params : Array RR.Ty) (ret : RR.Ty)
  /-- An extern: Lean name (original, for the extern table), key type
  arguments (for polymorphic externs), mono parameter types, result type. -/
  | extern (orig : Name) (typeArgs : Array Expr) (params : Array Expr) (ret : Expr)
  /-- A constructor. -/
  | ctor (info : ConstructorVal)
  /-- A constant defined by `initialize`: read from its once-cell. -/
  | initConst (slot : Nat) (type : Expr)

def calleeOf (f : Name) : LowerM Callee := do
  if let some slot := (← get).initSlots.find? f then
    return .initConst slot (← toMonoTypeKeep (← getOtherDeclBaseType f []))
  if let some (.ctorInfo c) := (← getEnv).find? f then
    -- Constructors of builtin types implemented by the runtime
    -- (`Int.ofNat` is `lean_nat_to_int`, …) are calls, as in Lean's IR.
    unless isExtern (← getEnv) f do return .ctor c
  if let some d := (← read).decls.find? f then
    let (ps, r) := splitFnType d.type d.params.size
    match d.value with
    | .code _ => return .code (fnName f) (← ps.mapM lowerType) (← lowerType r)
    | .extern _ =>
      let key := (← read).keys.find? f
      return .extern (key.map (·.decl) |>.getD f) (key.map (·.typeArgs) |>.getD #[]) ps r
  -- A monomorphic extern kept under its own name: take Lean's persisted mono signature.
  if let some d ← getMonoDecl? f then
    let (ps, r) := splitFnType d.type d.params.size
    return .extern f #[] ps r
  if let some (.ctorInfo c) := (← getEnv).find? f then
    let ty ← toMonoTypeKeep (← getOtherDeclBaseType f [])
    let (ps, r) := splitFnType ty (c.numParams + c.numFields)
    return .extern f #[] ps r
  throwError "lean2rr: unknown callee {f} (internal error)"

/-- Argument lowering with conversion to the expected type. -/
def lowerArg (ctx : CodeCtx) (a : Arg .pure) (expected : RR.Ty) : LowerM RR.Expr := do
  match a with
  | .fvar x =>
    match ctx.vars[x]? with
    | some (n, t) => coerce (.var n) t expected
    | none => throwError "lean2rr: unbound variable {x.name} (internal error)"
  -- `◾` (type arguments, proofs, or `box(0)` at a relevant type)
  | _ => zeroValue expected

/-- A partial application of target `tg` to `supplied` (at its parameter
types) as a value of type `expected`, the type of the binder. That may be
another representation (a lifted lambda whose result Lean typed `lcAny`,
a closure stored at a uniform type, `Box`): the value is then converted
(`tryCoerce`). The target runs only when its last argument arrives. -/
def partialApp (tg : FnTarget) (supplied : Array RR.Expr) (expected : RR.Ty) : LowerM RR.Expr := do
  let (v, t) ← partValue tg supplied
  coerce v t expected

/-- Apply `f : t` to `args` (each with its type): up to a chain's length at
a time (`applyCall`); a function value of statically unknown type (`Box`)
is unboxed to `Box → Box`. The result and its type. -/
def applyExprs (f : RR.Expr) (t : RR.Ty) (args : Array (RR.Expr × RR.Ty)) :
    LowerM (RR.Expr × RR.Ty) := do
  let mut e := f
  let mut t := t
  let mut i := 0
  while i < args.size do
    if t == RR.Ty.box then
      let canon := RR.Ty.fn RR.Ty.box RR.Ty.box
      e ← coerce e RR.Ty.box canon
      t := canon
    let (doms, _) := fnChain t
    if doms.isEmpty then throwError "lean2rr: application of a non-function value of type {t.render}"
    let j := min doms.size (args.size - i)
    let mut as := #[]
    for k in [:j] do
      let (a, aty) := args[i + k]!
      as := as.push (← coerce a aty doms[k]!)
    e ← applyCall e t as
    t := fnResult t j
    i := i + j
  return (e, t)

/-- Apply a function value `f : fty` to further (Lean) arguments. -/
def applyChain (f : RR.Expr) (fty : RR.Ty) (ctx : CodeCtx) (args : Array (Arg .pure)) :
    LowerM (RR.Expr × RR.Ty) := do
  let mut e := f
  let mut t := fty
  let mut i := 0
  while i < args.size do
    if t == RR.Ty.box then
      let canon := RR.Ty.fn RR.Ty.box RR.Ty.box
      e ← coerce e RR.Ty.box canon
      t := canon
    let (doms, _) := fnChain t
    if doms.isEmpty then throwError "lean2rr: application of a non-function value of type {t.render}"
    let j := min doms.size (args.size - i)
    let mut as := #[]
    for k in [:j] do
      as := as.push (← lowerArg ctx args[i + k]! doms[k]!)
    e ← applyCall e t as
    t := fnResult t j
    i := i + j
  return (e, t)

/-! ## Externs -/

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
(`leanrt::once::push_context`); `main` starts with empty cells too. Without
any use of the standard streams they do nothing. -/
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

/-- Reference operation `op` on a reference `r` whose cell stores elements
of type `e` as `k`, for an operation at element type `a` (values converted
between the two; `none` if they cannot be): `get` (a copy: the cell keeps
its reference), `take` (the value moves out and the cell gets the
placeholder, as `lean_st_ref_take` stores `box(0)`: Lean's `modify` is
take-then-set, so a value only the cell holds stays unshared and is updated
in place), `set` (`u64` result), `swap`. -/
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
  | .direct, "set" => return some (.call "l2r_rc_set" #[e] #[cell, v'.get!])
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
cell, `L2RRef_N(Cell<e>)` (`refType`): one allocation per reference, the
value stored in its own representation. `ST.Prim.mkRef` at element type `α`
creates one at `⟦α⟧` (`Box` for uniform code, at `α = lcAny`). Lean's mono
phase types every reference `lcAny`, so a reference travels in a `Box`
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

/-! ## Thunks and tasks: extern glue

Translation plan §5.14. Thunks are memoized cells. Tasks created after
`main` has started are deferred: they run when they are needed, on the stack
of whoever needs them, or when `main` returns, as Lean's task manager
finishes all queued tasks before the process exits (`leanrt::task` keeps the
queues); a pure task the program drops before it has started never runs. -/

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
/-! ## Child processes

Glue over the runtime's `l2r_proc_*` primitives (runtime/README.md, "Child
processes"; translation plan §5.8). A `Child` is a structure of its three
stream fields, `lcAny` in mono code and so `Box` (a boxed `LHandle` for a
piped stream, else a boxed unit, as natively `box(0)`), and two hidden
fields: the pid and whether the child was spawned with `setsid`
(`nominalType`). Fallible operations report errors through the runtime's
last-error protocol, as native Lean's `decode_io_error(errno, nullptr)`. -/

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

/-! ## Promises

`IO.Promise α` is `lcAny` in mono code, so a promise is passed boxed: a
runtime `LPromise` holding the cell of its task, a task over `Option Box`
whatever `α` is, so that typed and uniform code share it (translation plan
§5.14). The task is pending, without a computation the runtime would run,
until the promise is resolved; forcing it while unresolved runs queued
tasks until one resolves it (`l2r_task_force_sources`), and otherwise
waits forever (its `pending` closure), as natively. -/

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
it waits for a promise). Each runs its task as a worker would
(`taskStepFn`), or drops it when the runtime says it is deleted (a pure
task the program has dropped), then asks again. Generated once every task
type is known. -/
def taskDispatchFns : LowerM (Array RR.Item) := do
  let tags := (← get).taskTags
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
    -- The runtime's scheduler starts queued tasks on contexts of their own
    -- (`leanrt::sched`) through this entry point.
    .raw "extern \"C\" trampoline \"l2r_task_run_one_c\" = l2r_task_run_one;\n"]

/-! ## Identity (`ptrAddrUnsafe`)

`ptrAddrUnsafe x` answers what native Lean answers (translation plan §9):
the word of a boxed scalar (`lean_box(n) = 2n+1`) for values Lean
represents so, the address of the Lean object otherwise. lean2rr's
representations are mapped back to Lean's: a `Box` answers its payload's
identity, a function value wrapped for another representation the wrapped
value's, a thunk or task converted to another representation the
original's, a `[value]` struct its field's. -/

/-- Whether values of type `t` are natively boxed into a new cell each time
they are boxed (`lean_box_uint64`, `lean_box_float`, …; also `Int64`,
`ISize`, which are `UInt64` underneath). -/
def cellScalar (t : RR.Ty) : Bool :=
  match t with
  | .named n => n ∈ ["u64", "i64", "f64", "f32"]
  | _ => false

/-- The type a value of type `t` is natively represented by: through
`[value]` structs, their field's type. -/
partial def nativeLeaf (t : RR.Ty) : LowerM RR.Ty := do
  let .named n := t | return t
  let some info := (← get).typeInfos[n]? | return t
  if !info.value then return t
  let some layout := info.ctors.find? info.ctorOrder[0]! | return t
  let some ft := layout.posTys[0]? | return t
  nativeLeaf ft

/-- `l2r_lazy_addr_S(c)`: the identity of a thunk or task: its cell's
address, or the original's that a converted cell records (see
`lazyConv`). -/
def lazyAddrFn (z : String) : LowerM String := do
  let name := s!"l2r_lazy_addr_{z}"
  lazyFn name do
    let zt := RR.Ty.named z
    let body : RR.Block := .ofExpr (.mtch (.call "l2r_lcell_get" #[zt] #[.var "c"]) #[
      lazyArm z "conv" #[none, none, some "a"] (.ofExpr (.var "a")),
      lazyArm z "busyconv" #[some "a"] (.ofExpr (.var "a")),
      lazyArm z "convdone" #[none, none, some "a"] (.ofExpr (.var "a")),
      { ty := z, ctor := none, binders := #[], body := .ofExpr (.call "l2r_lcell_addr" #[zt] #[.var "c"]) }])
    return #[.fn name #[("c", .app "LCell" #[zt])] (.named "u64") body]

/-- `l2r_fn_addr_T(f)`, the identity of a function value of type `t`
(generated at the end, when its variants are known: `genFnAddr`). -/
def fnAddrFn (t : RR.Ty) : LowerM String := do
  unless (← get).fnAddrTargets.contains t do
    modify fun s => { s with fnAddrTargets := s.fnAddrTargets.push t }
  return s!"l2r_fn_addr_{t.enc}"

/-- `l2r_box_addr(b)`, the identity of a `Box`'s payload (generated at the
end, when the variants are known: `genBoxAddr`). -/
def boxAddrFn : LowerM String := do
  modify fun s => { s with boxAddrWanted := true }
  return "l2r_box_addr"

/-- A `u64` literal as an expression. -/
def u64Lit (k : Nat) : LowerM RR.Expr := do
  let o ← fresh "pa"
  return .block ⟨#[(o, some (.named "u64"), .atom (toString k))], .var o⟩

/-- `l2r_addr_T(x)` for a shared nominal type `tn` with constructors
without fields: natively those are the boxed scalars of their index. -/
def recAddrFn (tn : String) (info : TypeInfo) : LowerM String := do
  let name := s!"l2r_addr_{tn}"
  unless (← get).fns.any (fun | .fn n .. => n == name | _ => false) do
    let mut arms : Array RR.Arm := #[]
    for h : i in [:info.ctorOrder.size] do
      let some l := info.ctors.find? info.ctorOrder[i] | continue
      if (l.fields.filterMap id).isEmpty then
        arms := arms.push { ty := tn, ctor := some l.variant, binders := #[], body := .ofExpr (← u64Lit (2 * i + 1)) }
    let dflt := RR.Expr.call "l2r_ptr_addr_rec" #[.named tn] #[.var "x"]
    arms := arms.push { ty := tn, ctor := none, binders := #[], body := .ofExpr dflt }
    modify fun s => { s with fns := s.fns.push (.fn name #[("x", .named tn)] (.named "u64") (.ofExpr (.mtch (.var "x") arms))) }
  return name

/-- `ptrAddrUnsafe` of value `e : t` (see the section comment). A value
natively boxed into a new cell at each boxing (`UInt64`, `Float`) answers
a fresh number: natively two calls on the same variable box it twice (only
Lean's CSE, which lean2rr keeps, merges calls). -/
partial def addrOf (e : RR.Expr) (t : RR.Ty) : LowerM RR.Expr := do
  let evalThen (k : RR.Expr) : LowerM RR.Expr := do
    let d ← fresh "pd"
    return .block ⟨#[(d, some t, e)], k⟩
  match t with
  | .named n =>
    if n == "Nat" then return .call "l2r_addr_nat" #[] #[e]
    if n == "Int" then return .call "l2r_addr_int" #[] #[e]
    -- `box(0)`.
    if n == "L2RUnit" then return ← evalThen (← u64Lit 1)
    if cellScalar t then return ← evalThen (.call "l2r_addr_fresh" #[] #[])
    if n == boxName then return .call (← boxAddrFn) #[] #[e]
    -- `UInt8/16/32`, `Char`, `Bool`, enumerations.
    if let some i ← scalarWord e n then return .call "l2r_addr_word" #[] #[i]
    if n ∈ ["LStr", "LBig", "LNatArr", "LIntArr", "LHandle"] then
      return .call "l2r_ptr_addr_obj" #[t] #[e]
    match (← get).typeInfos[n]? with
    | some info =>
      if info.value then
        let some layout := info.ctors.find? info.ctorOrder[0]! | return ← evalThen (← u64Lit 1)
        let some ft := layout.posTys[0]? | return ← evalThen (← u64Lit 1)
        return ← withVar "pv" t e fun v => addrOf (.field v 0) ft
      if hasNullaryCtor info then return .call (← recAddrFn n info) #[] #[e]
      return .call "l2r_ptr_addr_rec" #[t] #[e]
    | none =>
      if ← isBoundaryTy t then return .call "l2r_ptr_addr_obj" #[t] #[e]
      evalThen (.call "l2r_addr_fresh" #[] #[])
  | .app "RVec" _ | .app "LRef" _ => return .call "l2r_ptr_addr_obj" #[t] #[e]
  | .app "LCell" #[.named z] => return .call (← lazyAddrFn z) #[] #[e]
  | .fn .. => return .call (← fnAddrFn t) #[] #[e]
  | _ => evalThen (.call "l2r_addr_fresh" #[] #[])

/-- Generate `l2r_fn_addr_T` (see `fnAddrFn`): a wrapped value answers the
identity of the value it wraps, the `box(0)` placeholder `1`, others their
cell. -/
def genFnAddr (t : RR.Ty) : LowerM Unit := do
  let name := s!"l2r_fn_addr_{t.enc}"
  let tn := RR.fnTypeName t
  let mut arms : Array RR.Arm := #[{ ty := tn, ctor := some "z", binders := #[], body := .ofExpr (← u64Lit 1) }]
  for v in (← get).fnVariants.getD t #[] do
    let .wrap src := v | continue
    let a ← addrOf (.var "l2rg") src
    arms := arms.push { ty := tn, ctor := some (fnVariantName v), binders := #[some "l2rg"], body := .ofExpr a }
  arms := arms.push { ty := tn, ctor := none, binders := #[], body := .ofExpr (.call "l2r_ptr_addr_rec" #[t] #[.var "l2rf"]) }
  let item := RR.Item.fn name #[("l2rf", t)] (.named "u64") (.ofExpr (.mtch (.var "l2rf") arms))
  modify fun s => { s with fns := (s.fns.filter fun | .fn n .. => n != name | _ => true).push item }

/-- Generate `l2r_box_addr` (see `boxAddrFn`): the payload's identity; a
payload natively boxed into a cell (`UInt64`, `Float`, or a `[value]`
struct over one) answers the `Box` cell, which is that cell here. -/
def genBoxAddr : LowerM Unit := do
  let name := "l2r_box_addr"
  let mut arms : Array RR.Arm := #[]
  for (vt, v) in (← get).boxVariants do
    if cellScalar (← nativeLeaf vt) then
      let cell := RR.Expr.call "l2r_ptr_addr_rec" #[RR.Ty.box] #[.var "b"]
      arms := arms.push { ty := boxName, ctor := some v, binders := #[none], body := .ofExpr cell }
    else
      arms := arms.push { ty := boxName, ctor := some v, binders := #[some "x"], body := .ofExpr (← addrOf (.var "x") vt) }
  let item := RR.Item.fn name #[("b", RR.Ty.box)] (.named "u64") (.ofExpr (.mtch (.var "b") arms))
  modify fun s => { s with fns := (s.fns.filter fun | .fn n .. => n != name | _ => true).push item,
                           boxAddrDone := s.boxVariants.size }

/-- Externs whose results mention Lean-defined types get generated glue
(translation plan §5.8); returns `none` for ordinary externs. -/
def customExtern (orig : Name) (params : Array Expr) (ret : Expr) (args : Array RR.Expr) :
    LowerM (Option RR.Expr) := do
  if let some e ← ctorCallbackExtern (← externSymbol orig) ret args then return some e
  if let some e ← lazyExtern orig params ret args then return some e
  if let some e ← promiseExtern (← externSymbol orig) params ret args then return some e
  if let some e ← processExtern orig params ret args then return some e
  match orig with
  -- `IO.Process.exit : UInt8 → IO α` never returns; nor does `forceExit`,
  -- which skips flushing and exit handlers.
  | ``IO.Process.exit | ``IO.Process.forceExit =>
    let rt ← lowerType ret
    let e ← fresh "ex"
    let prim := if orig == ``IO.Process.exit then "l2r_process_exit" else "l2r_process_force_exit"
    return some (.block ⟨#[(e, some (.named "u64"), .call prim #[] #[args[0]!])],
      .call "l2r_unreachable" #[rt] #[]⟩)
  | _ => pure ()
  -- `ptrAddrUnsafe`: what native Lean answers (see `addrOf`).
  if (← externSymbol orig) == "lean_ptr_addr" then
    let some p := params[0]? | return none
    return some (← addrOf args[0]! (← lowerType p))
  -- `Lean.Name.beq`: structural equality (see `structEqFn`).
  if (← externSymbol orig) == "lean_name_eq" then
    let .named tn ← lowerType params[0]! | return none
    let some f ← structEqFn tn | return none
    return some (.call f #[] #[args[0]!, args[1]!])
  -- Slices (`ByteSlice.beq`, `String.Slice` hash and `<`): the runtime
  -- takes the fields — the bytes or string, start, end — of each slice.
  let sliceSym := (← externSymbol orig)
  if let some prim := sliceGlue? sliceSym then
    let st ← lowerType params[0]!
    let .named sn := st | return none
    let some info := (← get).typeInfos[sn]? | return none
    let some layout := info.ctors.find? info.ctorOrder[0]! | return none
    let some (some (pa, _)) := layout.fields[0]? | return none
    let some (some (ps, _)) := layout.fields[1]? | return none
    let some (some (pe, _)) := layout.fields[2]? | return none
    let parts (x : RR.Expr) : Array RR.Expr :=
      #[.field x pa, .call "lean_usize_of_nat" #[] #[.field x ps], .call "lean_usize_of_nat" #[] #[.field x pe]]
    if args.size == 1 then
      return some (← withVar "bs" st args[0]! fun a => pure (.call prim #[] (parts a)))
    return some (← withVar "bs" st args[0]! fun a => withVar "bs" st args[1]! fun b =>
      pure (.call prim #[] (parts a ++ parts b)))
  -- `ShareCommon.State.shareCommon s a`: hash-consing natively; its
  -- reference body `(a, s)` is observably the same (sharing is not).
  if orig == ``ShareCommon.State.shareCommon then
    let rt ← lowerType ret
    let tys ← ctorFieldTys rt ``Prod.mk
    let some at' := tys[0]? | return none
    let some stt := tys[1]? | return none
    let n := params.size
    let a ← coerce args[n - 1]! (← lowerType params[n - 1]!) at'
    let st ← coerce args[n - 2]! (← lowerType params[n - 2]!) stt
    return some (← ctorValue rt ``Prod.mk #[a, st])
  -- `String.ofList : List Char → String`
  if orig == ``String.ofList then
    let lt ← lowerType params[0]!
    let fn ← listFold s!"l2r_list_to_string_{lt.render.map fun c => if c.isAlphanum then c else '_'}" lt
      (.named "LStr") (.named "u32") fun acc x => .call "lean_string_push" #[] #[acc, x]
    return some (.call fn #[] #[args[0]!, ← strLit ""])
  -- `Array.mk : List α → Array α`
  -- `String.mk : List Char → String`: push the characters onto "".
  if (← externSymbol orig) == "lean_string_mk" then
    let lt ← lowerType params[0]!
    let fn ← listFold s!"l2r_string_of_list_{lt.render.map fun c => if c.isAlphanum then c else '_'}" lt
      (.named "LStr") (.named "u32") fun acc x => .call "lean_string_push" #[] #[acc, x]
    return some (.call fn #[] #[args[0]!, ← strLit ""])
  if orig == ``Array.mk then
    let lt ← lowerType params[0]!
    let arrTy ← lowerType ret
    let some repr ← arrayRepr? arrTy | throwError "lean2rr: bad array type {arrTy.render}"
    let fn ← listFold s!"l2r_list_to_array_{lt.render.map fun c => if c.isAlphanum then c else '_'}" lt arrTy
      repr.value fun acc x => repr.call "push" #[acc, repr.store x]
    return some (.call fn #[] #[args[0]!, repr.call "empty" #[]])
  -- `Array.toList : Array α → List α`: cons the elements from the last.
  if orig == ``Array.toList then
    let arrTy ← lowerType params[0]!
    let lt ← lowerType ret
    let some repr ← arrayRepr? arrTy | throwError "lean2rr: bad array type {arrTy.render}"
    let .named ltn := lt | throwError "lean2rr: bad list type"
    let some info := (← get).typeInfos[ltn]? | throwError "lean2rr: bad list type"
    let some nil := info.ctors.find? ``List.nil | throwError "lean2rr: bad list type"
    let some cons := info.ctors.find? ``List.cons | throwError "lean2rr: bad list type"
    let valTy? := (cons.fields[0]?.join).map (·.2)
    let name := s!"l2r_array_to_list_{ltn}_{repr.family}"
    unless (← get).fns.any (fun | .fn n .. => n == name | _ => false) do
      let u64 := RR.Ty.named "u64"
      -- Elements without a representation (types, proofs) are not stored.
      let (xLet, fieldVals) ← match valTy? with
        | some valTy => do
          let x := repr.load (repr.call "get" #[.var "v", .var "j"])
          pure (#[("x", some valTy, ← coerce x repr.value valTy)], #[RR.Expr.var "x", .var "acc"])
        | none => pure (#[], #[RR.Expr.var "acc"])
      let body : RR.Block := ⟨#[("zero", some u64, .atom "0")], .ite (.atom "zero < i")
        ⟨#[("one", some u64, .atom "1"), ("j", some u64, .atom "i - one")] ++ xLet ++
         #[("c", some lt, .ctor ltn (some cons.variant) (cons.place fieldVals))],
          .call (name ++ "_go") #[] #[.var "v", .var "j", .var "c"]⟩
        (.ofExpr (.var "acc"))⟩
      let entry : RR.Block :=
        .ofExpr (.call (name ++ "_go") #[] #[.var "v", repr.call "size" #[.var "v"],
          .ctor ltn (some nil.variant) #[]])
      modify fun s => { s with fns := s.fns ++ #[
        .fn (name ++ "_go") #[("v", arrTy), ("i", u64), ("acc", lt)] lt body,
        .fn name #[("v", arrTy)] lt entry] }
    return some (.call name #[] #[args[0]!])
  let std? : Option (Nat × Bool) := match orig with
    | ``IO.getStdin => some (0, false)
    | ``IO.getStdout => some (1, false)
    | ``IO.getStderr => some (2, false)
    | ``IO.setStdin => some (0, true)
    | ``IO.setStdout => some (1, true)
    | ``IO.setStderr => some (2, true)
    | _ => none
  if let some (fd, set) := std? then
    -- `BaseIO FS.Stream`: the result is `ST.Out σ FS.Stream`.
    let resTy ← lowerType ret
    let .named rn := resTy | return none
    let some info := (← get).typeInfos[rn]? | return none
    let some layout := info.ctors.find? info.ctorOrder[0]! | return none
    let some (some (_, streamTy)) := layout.fields[0]? | return none
    let (getFn, setFn) ← stdStreamFns fd streamTy
    if set then
      let s ← coerce args[0]! (← lowerType params[0]!) streamTy
      return some (← wrapIOResult resTy (.call setFn #[] #[s]))
    return some (← wrapIOResult resTy (.call getFn #[] #[]))
  return none

/-- Emit a saturated extern call. Default: call the prelude function named
after the C symbol with the passed arguments.

For extern instances (polymorphic externs such as `Array.push {α}`), the
prelude function is generic; it receives the storage types of the type
arguments explicitly. A type argument whose values cannot cross Reussir's
FFI boundary (a value type, a closure) is stored boxed in a one-field shared
struct, so arguments of that type are wrapped and a result of that type is
unwrapped here. -/
def lowerExternCall (orig : Name) (typeArgs : Array Expr) (params : Array Expr) (ret : Expr)
    (args : Array RR.Expr) : LowerM RR.Expr := do
  -- Glue sees only relevant parameters: erased ones (type arguments,
  -- proofs) are dropped; the world is kept (IO glue applies actions to it).
  let relevant := (params.zip args).filter fun (p, _) =>
    let p := p.consumeMData
    !(p.isErased || p.isSort)
  if let some e ← customExtern orig (relevant.map (·.1)) ret (relevant.map (·.2)) then return e
  if orig.getPrefix == `ST.Prim || orig.getPrefix == `ST.Prim.Ref then
    if let some e ← refGlue orig typeArgs (relevant.map (·.1)) ret (relevant.map (·.2))
        (← relevant.mapM (lowerType ·.1)) then return e
  let sym ← externSymbol orig
  -- Which parameters the runtime receives: not erased ones, not the world,
  -- not proofs.
  -- A parameter declared at a type variable is passed even when that is
  -- instantiated with a proof-like type (`Array.push` at `PLift True`).
  let (uses0, _) ← typeVarUses orig
  let mask ← params.zipIdx.mapM fun (p, i) => do
    if (uses0[i]?.join).isSome then return true
    return externParamPassed p && !(← isPropTy p)
  let passedArgs := (mask.zip args).filterMap fun (m, a) => if m then some a else none
  -- A fallible IO extern (files): the runtime's last-error protocol.
  if isFallibleIOSym sym then
    let prim := fallibleIOPrim sym
    if let some primRet := (← read).preludeRets[prim]? then
      let argTys ← (mask.zip params).filterMapM fun (m, p) => if m then some <$> lowerType p else pure none
      return ← fallibleIOGlue prim primRet argTys passedArgs ret (follow := sym != "lean_io_symlink_metadata")
  -- A `BaseIO` extern that cannot fail: the runtime provides its payload
  -- as `l2r_<sym without lean_>`; the result is wrapped as an IO result.
  if sym.startsWith "lean_" then
    let prim := "l2r_" ++ (sym.drop 5).toString
    if (← read).preludeFns.contains prim then
      let resTy ← lowerType ret
      if let .named rn := resTy then
        if let some k := (← get).typeKeys[rn]? then
          if k.isAppOf ``EST.Out || k.isAppOf ``ST.Out then
            -- Arguments at the primitive's parameter types (a handle is
            -- `lcAny` in mono code, so it arrives boxed).
            let argTys ← (mask.zip params).filterMapM fun (m, p) => if m then some <$> lowerType p else pure none
            let want := (← read).preludeParams[prim]?.getD argTys
            let passed ← (passedArgs.zip (argTys.zip want)).mapM fun (a, (t, w)) => coerce a t w
            -- The result too, from a non-generic primitive's result type (a
            -- runtime object such as a mutex or promise is `lcAny` in mono
            -- code).
            let payload ← match (← read).preludeRets[prim]?, (← read).preludeParams.contains prim with
              | some r, true => coerce (.call prim #[] passed) r (← ioPayloadTy resTy)
              | _, _ => pure (.call prim #[] passed)
            return ← wrapIOResult resTy payload
  -- A generic prelude function in plain Reussir that does not store its
  -- values in runtime containers (`dbgTrace`, `dbgSleep`, `panic`, …) is
  -- instantiated at the value types themselves: its arguments and result
  -- are passed as they are, closures included. Only FFI functions and
  -- containers need array storage types.
  if let some n := (← read).valueGenericFns[sym]? then
    let tys ← if n == typeArgs.size then typeArgs.mapM fun t => do lowerType (← toMonoTypeKeep t)
      else pure #[]
    -- A function value becomes a Reussir closure for the prelude.
    let argTys ← (mask.zip params).filterMapM fun (m, p) => if m then some <$> lowerType p else pure none
    let cls := (← read).valueGenericCls.getD sym #[]
    let passed ← (passedArgs.zip argTys).zipIdx.mapM fun ((a, t), i) => match t with
      | .fn d c => if cls[i]?.getD false then coerce a t (.cls d c) else pure a
      | _ => pure a
    return .call sym tys passed
  -- Array externs at `Array Nat`/`Array Int` use the one-word arrays.
  if let some α := typeArgs[0]? then
    let fam? := match ← lowerType (← toMonoTypeKeep α) with
      | .named "Nat" => some "natarr"
      | .named "Int" => some "intarr"
      | _ => none
    if let some fam := fam? then
      if let some sym' := natArrSym? sym fam then
        return .call sym' #[] passedArgs
  -- Storage for each type argument: the storage type, and the conversions
  -- of a value to and from it (`ArrayRepr.store`/`load`). An extern over
  -- arrays of the type argument stores it as the arrays do (an enumeration
  -- as its index, `arrayStorage`); any other as `arrayElemTy`.
  let overArrays := (params.push ret).any fun p => (p.find? (·.isAppOf ``Array)).isSome
  let mut storage : Array ArrayRepr := #[]
  for t in typeArgs do
    -- Instance keys hold base-phase types.
    let rt ← lowerType (← toMonoTypeKeep t)
    let st ← if overArrays then arrayStorage rt else pure (← arrayElemTy rt).1
    let some r ← arrayRepr? (.app "RVec" #[st]) | throwError "lean2rr: no storage for {rt.render}"
    storage := storage.push r
  -- Values whose declared type is a type parameter `α` are passed and
  -- returned in `α`'s storage (e.g. `Array.push`'s element): wrapped if the
  -- storage is a wrapper, as an index for an enumeration.
  let (uses, retUse) ← typeVarUses orig
  let reprOf (use : Option Nat) : Option ArrayRepr := do storage[← use]?
  let mut passed := #[]
  for i in [:params.size] do
    if mask[i]! then
      let a := args[i]!
      match reprOf (uses[i]?.join) with
      | some r => passed := passed.push (r.store a)
      | none => passed := passed.push a
  let call := RR.Expr.call sym (storage.map (·.storage)) passed
  match reprOf retUse with
  | some r => return r.load call
  | none => return call

/-! ## Values -/

/-- A `Nat` literal: `Small` below 2^64, otherwise parsed by the runtime
from its decimal digits in the string literal table (a flat call: a nested
arithmetic expression per limb overflowed rrc's stack for literals of
thousands of digits, and cost quadratic time). -/
def natLiteral (n : Nat) : LowerM RR.Expr := do
  if n < 2 ^ 64 then return .ctor "Nat" (some "Small") #[.atom (toString n)]
  return .call "l2r_nat_norm" #[] #[.call "l2r_big_of_decimal_lstr" #[] #[← strLit (toString n)]]

/-- Constructor `c` applied to all its arguments `vals` (parameters, then
fields), building a value of `fullRt`. -/
def ctorBuild (c : Name) (fullRt : RR.Ty) (vals : Array RR.Expr) : LowerM RR.Expr := do
  match fullRt with
  | .named "bool" => return .atom (if c == ``Bool.true then "true" else "false")
  | .named "L2RUnit" => return .unitVal
  | .named tn =>
    match (← get).typeInfos[tn]? with
    | some info =>
      let some layout := info.ctors.find? c
        | throwError "lean2rr: constructor {c} not in type {tn}"
      let mut fieldVals := #[]
      for h : i in [:layout.fields.size] do
        if let some (_, t) := layout.fields[i] then
          -- Hidden fields (`IO.Process.Child`'s) have no Lean argument.
          fieldVals := fieldVals.push (← match vals[layout.numParams + i]? with
            | some v => pure v
            | none => zeroValue t)
      let placedVals := layout.place fieldVals
      match info.shape with
      | .struct => return .ctor tn none placedVals
      | _ => return .ctor tn (some layout.variant) placedVals
    | none => throwError "lean2rr: constructor {c} of non-nominal type {tn}"
  | t => throwError "lean2rr: constructor {c} at type {t.render}"

/-- Lean definitions replaced by prelude functions with the same results
(runtime requests 12, 27): `Nat.repr` divides by 10 digit by digit, and
`Nat.reprFast` reads a table of strings through a once-cell. -/
def preludeReplacement? (f : Name) : LowerM (Option (String × RR.Ty)) := do
  let orig := ((← read).keys.find? f).map (·.decl) |>.getD f
  match orig with
  | ``Nat.repr | ``Nat.reprFast => return some ("l2r_nat_repr", .named "Nat")
  | ``Int.repr => return some ("l2r_int_repr", .named "Int")
  | _ => return none

/-- A saturated call of an `ST.Ref` operation: the reference arguments are
passed at their own representation (a typed reference, or a `Box`; see
`refGlue`), not converted to the extern's parameter type (`lcAny`, which
would box a typed reference). -/
def refCall? (ctx : CodeCtx) (orig : Name) (typeArgs : Array Expr) (params : Array Expr) (ret : Expr)
    (args : Array (Arg .pure)) : LowerM (Option RR.Expr) := do
  unless orig.getPrefix == `ST.Prim.Ref do return none
  let mut ps := #[]
  let mut as := #[]
  let mut ts := #[]
  for (a, p) in args.zip params do
    let p' := p.consumeMData
    if p'.isErased || p'.isSort then continue
    let pt ← lowerType p
    -- The references: the first relevant parameter (both, for `ptrEq`).
    let handle := ps.size == 0 || (orig == ``ST.Prim.Ref.ptrEq && ps.size == 1)
    match a, handle with
    | .fvar x, true =>
      let some (vn, vt) := ctx.vars[x]? | throwError "lean2rr: unbound variable {x.name} (internal error)"
      as := as.push (RR.Expr.var vn)
      ts := ts.push vt
    | _, _ =>
      as := as.push (← lowerArg ctx a pt)
      ts := ts.push pt
    ps := ps.push p
  refGlue orig typeArgs ps ret as ts

/-- Lower a constant application with Lean's arity rules. -/
def lowerConstApp (ctx : CodeCtx) (f : Name) (args : Array (Arg .pure)) (resTy : Expr) :
    LowerM RR.Expr := do
  if args.size == 1 then
    if let some (prim, argTy) ← preludeReplacement? f then
      return ← coerce (.call prim #[] #[← lowerArg ctx args[0]! argTy]) (.named "LStr") (← lowerType resTy)
  match ← calleeOf f with
  | .initConst slot ty =>
    let t ← lowerType ty
    let (st, boxed) ← arrayElemTy t
    let v := RR.Expr.call "l2r_once_get" #[st] #[.atom (toString slot)]
    let v := if boxed then .field v 0 else v
    let (e, t) ← applyChain v t ctx args
    coerce e t (← lowerType resTy)
  | .code fn params ret =>
    let n := params.size
    if args.size == n then
      let as ← (args.zip params).mapM fun (a, t) => lowerArg ctx a t
      coerce (.call fn #[] as) ret (← lowerType resTy)
    else if args.size < n then
      let supplied ← (args.zip params).mapM fun (a, t) => lowerArg ctx a t
      partialApp { id := "d" ++ fn, params, ret, call := .code fn } supplied (← lowerType resTy)
    else
      let as ← (args[:n].toArray.zip params).mapM fun (a, t) => lowerArg ctx a t
      let (e, t) ← applyChain (.call fn #[] as) ret ctx args[n:].toArray
      coerce e t (← lowerType resTy)
  | .extern orig typeArgs params ret =>
    let n := params.size
    let ptys ← params.mapM lowerType
    let retTy ← lowerType ret
    if args.size == n then
      -- `ptrAddrUnsafe x`: the identity of `x` in its own representation
      -- (converted to the parameter's, it would be another object).
      if (← externSymbol orig) == "lean_ptr_addr" then
        if let some (.fvar x) := args.back? then
          if let some (vn, vt) := ctx.vars[x]? then
            return ← coerce (← addrOf (.var vn) vt) (.named "u64") (← lowerType resTy)
      if let some e ← refCall? ctx orig typeArgs params ret args then
        return ← coerce e retTy (← lowerType resTy)
      let as ← (args.zip ptys).mapM fun (a, t) => lowerArg ctx a t
      coerce (← lowerExternCall orig typeArgs params ret as) retTy (← lowerType resTy)
    else if args.size < n then
      let supplied ← (args.zip ptys).mapM fun (a, t) => lowerArg ctx a t
      partialApp { id := "e" ++ fnName f, params := ptys, ret := retTy, call := .extern orig typeArgs params ret }
        supplied (← lowerType resTy)
    else
      let as ← (args[:n].toArray.zip ptys).mapM fun (a, t) => lowerArg ctx a t
      let call ← lowerExternCall orig typeArgs params ret as
      let (e, t) ← applyChain call retTy ctx args[n:].toArray
      coerce e t (← lowerType resTy)
  | .ctor c =>
    let arity := c.numParams + c.numFields
    let rt ← lowerType (← if args.size ≥ arity then pure resTy else pure resTy)
    -- The instance is determined by the result type of a saturated
    -- application; for a partial application, by the codomain.
    let (_, fullTy) := splitFnType resTy (arity - min arity args.size)
    let fullRt ← if args.size ≥ arity then pure rt else lowerType fullTy
    -- Expected Reussir types of the constructor's arguments.
    let argTys ← do
      match fullRt with
      | .named tn =>
        match (← get).typeInfos[tn]? with
        | some info =>
          let some layout := info.ctors.find? c.name | pure (Array.replicate arity RR.Ty.unit)
          let tys := (Array.replicate layout.numParams RR.Ty.unit) ++ layout.fields.map fun
            | some ((_ : Nat), t) => t
            | none => RR.Ty.unit
          pure (tys.extract 0 arity)
        | none => pure (Array.replicate arity RR.Ty.unit)
      | _ => pure (Array.replicate arity RR.Ty.unit)
    let vals ← (args.zip argTys).mapM fun (a, t) => lowerArg ctx a t
    if args.size ≥ arity then ctorBuild c.name fullRt vals
    else partialApp { id := "k" ++ fullRt.enc ++ "_" ++ fnName c.name, params := argTys, ret := fullRt,
                      call := .ctor c.name fullRt } vals (← lowerType resTy)

/-- How a `cases` (or projection) of inductive `typeName` treats a
discriminant of Reussir type `sty`. Mono erases `unsafeCast`, so the
discriminant can be a value of another type that Lean represents alike
(translation plan §5.5): an inductive with the same constructor shapes, a
`Nat` or `UInt8` used as an enumeration. -/
inductive CastCases where
  /-- A value of `typeName` (the usual case). -/
  | same
  /-- A value of isomorphic inductive `sn` (§5.1), matched as `dn`, an
  instance of `typeName`: constructors correspond by position, relevant
  fields by position (`viewLayout`), and are bound at their own types. -/
  | view (sn dn : String)
  /-- Converted to `typeName`'s instance `dst` first (enumerations by index;
  where no conversion exists, `coerce` warns and the cast panics). -/
  | convert (dst : RR.Ty)
  /-- `typeName` has no representation (its values carry nothing). -/
  | unit

def castCases (sty : RR.Ty) (typeName : Name) : LowerM CastCases := do
  let sameHead (h : Name) := h == typeName || h == typeName ++ `_impl || typeName == h ++ `_impl
  let tn := match sty with | .named n => n | _ => ""
  let infos := (← get).typeInfos
  let nominal := infos.contains tn
  if nominal then
    let some h ← nominalHead tn | return .same
    if sameHead h then return .same
  else if tn == "bool" && typeName == ``Bool then return .same
  -- The instance of `typeName` to match against: at the discriminant's
  -- type arguments when the parameter counts agree (`Option Nat` cast to
  -- `MyOpt Nat`), otherwise the uniform one.
  let uniform ← uniformType typeName
  if uniform == .unit then return .unit
  if uniform == sty || uniform == RR.Ty.box then return .same
  if nominal then
    let mut cands : Array RR.Ty := #[]
    if let some k := (← get).typeKeys[tn]? then
      if let some (.inductInfo ival) := (← getEnv).find? typeName then
        if ival.numParams == k.getAppNumArgs && ival.numParams > 0 then
          cands := cands.push (← lowerTypeApp typeName k.getAppArgs)
    cands := cands.push uniform
    for dt in cands do
      if let .named dn := dt then
        if (← get).typeInfos.contains dn && (← isomorphic tn dn) then return .view tn dn
  return .convert uniform

/-- The layout of constructor `dc` (layout `dl`, of the instance a cast
value is matched as) over the record of the corresponding constructor `sc`
(layout `sl`) of the value's own type: each field of `dl` is the field of
`sl` it reads natively (`castFieldMap`), at its record position and type (as
`structConv` converts). A field reading nothing here is a placeholder. -/
def viewLayout (sc dc : Name) (sl dl : CtorLayout) : LowerM CtorLayout := do
  let fm := (← castFieldMap sc dc sl dl).getD #[]
  let fields := (List.range dl.fields.size).toArray.map fun j =>
    match fm[j]?.join.join with
    | some k => sl.fields[k]?.join
    | none => none
  return { variant := sl.variant, numParams := dl.numParams, fields }

def lowerLetValue (ctx : CodeCtx) (v : LetValue .pure) (ty : Expr) (rty : RR.Ty) : LowerM RR.Expr := do
  match v with
  | .lit (.nat n) => coerce (← natLiteral n) (.named "Nat") rty
  | .lit (.str s) => coerce (← strLit s) (.named "LStr") rty
  | .lit (.uint8 n) | .lit (.uint16 n) => return .atom (toString n)
  | .lit (.uint32 n) => return .atom (toString n)
  | .lit (.uint64 n) | .lit (.usize n) => return .atom (toString n)
  | .erased => zeroValue rty
  | .proj sn i x _ =>
    match ctx.vars[x]? with
    | some (n, st) =>
      -- A projection of a cast value: as a `cases` (see `castCases`).
      let (e, tn, layout?) ← match ← castCases st sn with
        | .view src dst =>
          let si := (← get).typeInfos[src]?
          let di := (← get).typeInfos[dst]?
          let sc := si.bind (·.ctorOrder[0]?)
          let dc := di.bind (·.ctorOrder[0]?)
          let sl := si.bind fun i => i.ctorOrder[0]?.bind i.ctors.find?
          let dl := di.bind fun i => i.ctorOrder[0]?.bind i.ctors.find?
          let layout ← match sc, dc, sl, dl with
            | some sc, some dc, some sl, some dl => some <$> viewLayout sc dc sl dl
            | _, _, _, _ => pure none
          pure (RR.Expr.var n, src, layout)
        | .convert dty =>
          let .named dn := dty | return ← zeroValue rty
          let di := (← get).typeInfos[dn]?
          pure (← coerce (.var n) st dty, dn, di.bind fun i => i.ctorOrder[0]?.bind i.ctors.find?)
        | .unit => return ← zeroValue rty
        | .same =>
          let .named tn := st | throwError "lean2rr: projection from {st.render}"
          let some info := (← get).typeInfos[tn]? | throwError "lean2rr: projection from non-structure {tn}"
          pure (RR.Expr.var n, tn, info.ctorOrder[0]?.bind info.ctors.find?)
      let some layout := layout? | throwError "lean2rr: bad projection"
      match layout.fields[i]? with
      | some (some (j, ft)) =>
        match e with
        | .var _ => coerce (.field e j) ft rty
        | _ => withVar "pv" (.named tn) e fun v => coerce (.field v j) ft rty
      | _ => zeroValue rty
    | _ => throwError "lean2rr: projection from unknown variable"
  | .const f _ args _ => lowerConstApp ctx f args ty
  | .fvar g args =>
    match ctx.vars[g]? with
    | some (n, t) =>
      let (e, t') ← applyChain (.var n) t ctx args
      coerce e t' rty
    | none => throwError "lean2rr: unbound function variable (internal error)"
  | _ => throwError "lean2rr: impure let value (internal error)"

/-! ## Join-point strategy -/

/-- Number of jumps to each join point. -/
partial def countJumps : Code .pure → Std.HashMap FVarId Nat → Std.HashMap FVarId Nat
  | .jmp j _, m => m.insert j (m.getD j 0 + 1)
  | .let _ k, m => countJumps k m
  | .fun d k _, m | .jp d k, m => countJumps k (countJumps d.value m)
  | .cases c, m => c.alts.foldl (fun m alt => countJumps alt.getCode m) m
  | _, m => m

/-- Does every path through `c` end in a jump to one of `targets` (or in
`unreach`)? Nested join points in `outlined` are functions, so jumping to
them does not count. -/
partial def endsInJumps (c : Code .pure) (targets : FVarIdSet) (outlined : FVarIdSet) : Bool :=
  match c with
  | .let _ k => endsInJumps k targets outlined
  | .fun _ k _ => endsInJumps k targets outlined
  | .jmp j _ => targets.contains j
  | .unreach _ => true
  | .return _ => false
  | .cases cs => cs.alts.all fun alt => endsInJumps alt.getCode targets outlined
  | .jp d k =>
    if !outlined.contains d.fvarId && endsInJumps d.value targets outlined then
      endsInJumps k (targets.insert d.fvarId) outlined
    else endsInJumps k targets outlined
  | _ => false

/-- Join points jumped to from inside the body of join point `inside`. -/
partial def jumpsIn : Code .pure → FVarIdSet → FVarIdSet
  | .jmp j _, s => s.insert j
  | .let _ k, s => jumpsIn k s
  | .fun d k _, s | .jp d k, s => jumpsIn k (jumpsIn d.value s)
  | .cases c, s => c.alts.foldl (fun s alt => jumpsIn alt.getCode s) s
  | _, s => s

/-- Does `c` jump to `j`? -/
partial def hasJumpTo (j : FVarId) : Code .pure → Bool
  | .jmp j' _ => j == j'
  | .let _ k => hasJumpTo j k
  | .fun d k _ | .jp d k => hasJumpTo j d.value || hasJumpTo j k
  | .cases c => c.alts.any (hasJumpTo j ·.getCode)
  | _ => false

/-- Place join point `d` (whose scope is `k`) as deep as possible: into the
single branch, join-point body or continuation containing all its jumps.
Free variables of `d` stay in scope (binders are unique), and code does not
grow. Sunk into the subtree its jumps come from, a join point is more often
structured (J2) instead of outlined: an outlined join point that calls the
enclosing function back makes a loop mutually recursive, which LLVM does not
turn into a loop. -/
partial def sinkInto (d : FunDecl .pure) (k : Code .pure) : Code .pure :=
  let j := d.fvarId
  match k with
  | .let x k' => .let x (sinkInto d k')
  | .fun f k' _ => if hasJumpTo j f.value then .jp d k else .fun f (sinkInto d k')
  | .jp d2 k2 =>
    match hasJumpTo j d2.value, hasJumpTo j k2 with
    | true, true => .jp d k
    | true, false => .jp (FunDecl.mk d2.fvarId d2.binderName d2.params d2.type (sinkInto d d2.value)) k2
    | false, true => .jp d2 (sinkInto d k2)
    | false, false => k
  | .cases c =>
    if (c.alts.filter (hasJumpTo j ·.getCode)).size == 1 then
      .cases ⟨c.typeName, c.resultType, c.discr, c.alts.map fun alt =>
        if hasJumpTo j alt.getCode then
          match alt with
          | .alt ctor ps code _ => .alt ctor ps (sinkInto d code)
          | .default code => .default (sinkInto d code)
          | other => other
        else alt⟩
    else .jp d k
  | _ => .jp d k

/-- Sink every join point of `c` (innermost first). -/
partial def sinkJoinPoints : Code .pure → Code .pure
  | .let x k => .let x (sinkJoinPoints k)
  | .fun d k _ =>
    .fun (FunDecl.mk d.fvarId d.binderName d.params d.type (sinkJoinPoints d.value)) (sinkJoinPoints k)
  | .jp d k =>
    sinkInto (FunDecl.mk d.fvarId d.binderName d.params d.type (sinkJoinPoints d.value)) (sinkJoinPoints k)
  | .cases c =>
    .cases ⟨c.typeName, c.resultType, c.discr, c.alts.map fun
      | .alt ctor ps code _ => .alt ctor ps (sinkJoinPoints code)
      | .default code => .default (sinkJoinPoints code)
      | other => other⟩
  | c => c

/-- Does `c` contain a tail call `let x := f args; return x` of `f` with
`arity` arguments (outside nested join-point bodies, which are checked on
their own when outlined)? -/
partial def hasSelfTailCall (f : Name) (arity : Nat) : Code .pure → Bool
  | .let d k =>
    match d.value, k with
    | .const g _ args _, .return x => (g == f && args.size == arity && x == d.fvarId) || hasSelfTailCall f arity k
    | _, _ => hasSelfTailCall f arity k
  | .fun _ k _ => hasSelfTailCall f arity k
  | .jp d k => hasSelfTailCall f arity d.value || hasSelfTailCall f arity k
  | .cases c => c.alts.any (hasSelfTailCall f arity ·.getCode)
  | _ => false

/-- The bodies of the outlined join points of `c`. -/
partial def outlinedBodies (c : Code .pure) (outlined : FVarIdSet) : Array (Code .pure) :=
  go c #[]
where
  go (c : Code .pure) (acc : Array (Code .pure)) : Array (Code .pure) :=
    match c with
    | .let _ k => go k acc
    | .fun d k _ => go k (go d.value acc)
    | .jp d k => go k (go d.value (if outlined.contains d.fvarId then acc.push d.value else acc))
    | .cases cs => cs.alts.foldl (fun acc alt => go alt.getCode acc) acc
    | _ => acc

/-- Size of a code block (bindings, alternatives and exits), counted up to
`cap`. -/
partial def codeSize (c : Code .pure) (cap : Nat) : Nat :=
  go c 0
where
  go (c : Code .pure) (acc : Nat) : Nat :=
    if acc ≥ cap then acc else
    match c with
    | .let _ k => go k (acc + 1)
    | .fun d k _ | .jp d k => go k (go d.value (acc + 1))
    | .cases cs => cs.alts.foldl (fun acc alt => go alt.getCode (acc + 1)) (acc + 1)
    | _ => acc + 1

/-- Small join points (nested join points included, since sinking nests
them) are duplicated at their jumps (like J1) rather than
outlined: outlining one on a loop's path makes the loop a state machine
(J4) or mutually recursive (J3), and keeps the reuse of cells matched
before the jump from reaching constructions after it. -/
def isSmallJp (d : FunDecl .pure) : Bool := codeSize d.value 41 ≤ 40

/-- Choose a strategy for every join point of a declaration body: the set
of outlined (J3) join points; others are J1 (single jump) or J2. -/
partial def chooseOutlined (body : Code .pure) : FVarIdSet := Id.run do
  let counts := countJumps body {}
  -- All join points with their scope.
  let mut jps : Array (FunDecl .pure × Code .pure) := #[]
  let rec gather (c : Code .pure) (acc : Array (FunDecl .pure × Code .pure)) : Array (FunDecl .pure × Code .pure) :=
    match c with
    | .let _ k => gather k acc
    | .fun d k _ => gather k (gather d.value acc)
    | .jp d k => gather k (gather d.value (acc.push (d, k)))
    | .cases cs => cs.alts.foldl (fun acc alt => gather alt.getCode acc) acc
    | _ => acc
  jps := gather body #[]
  let mut outlined : FVarIdSet := {}
  let mut changed := true
  while changed do
    changed := false
    for (d, k) in jps do
      if outlined.contains d.fvarId then continue
      let single := counts.getD d.fvarId 0 ≤ 1
      -- A J2 join point cannot be the target of a jump from inside an outlined body.
      let jumpedFromOutlined := jps.any fun (d', _) =>
        outlined.contains d'.fvarId && (jumpsIn d'.value {}).contains d.fvarId
      let ok := single || isSmallJp d ||
        (endsInJumps k (({} : FVarIdSet).insert d.fvarId) outlined && !jumpedFromOutlined)
      if !ok then
        outlined := outlined.insert d.fvarId
        changed := true
  return outlined

/-- Whether `x` occurs in `c`. -/
partial def hasFVar (x : FVarId) (c : Code .pure) : Bool :=
  let inArg : Arg .pure → Bool := fun | .fvar y => y == x | _ => false
  let inValue : LetValue .pure → Bool := fun
    | .fvar f args => f == x || args.any inArg
    | .const _ _ args _ => args.any inArg
    | .proj _ _ y _ => y == x
    | _ => false
  match c with
  | .let d k => inValue d.value || hasFVar x k
  | .fun d k _ | .jp d k => hasFVar x d.value || hasFVar x k
  | .jmp _ args => args.any inArg
  | .cases cs => cs.discr == x || cs.alts.any (hasFVar x ·.getCode)
  | .return y => y == x
  | .unreach _ => false

/-- Variables used in a let value. -/
def valueUses (v : LetValue .pure) (acc : Std.HashSet FVarId) : Std.HashSet FVarId :=
  let args (as : Array (Arg .pure)) (acc : Std.HashSet FVarId) :=
    as.foldl (fun acc a => match a with | .fvar y => acc.insert y | _ => acc) acc
  match v with
  | .fvar f as => args as (acc.insert f)
  | .const _ _ as _ => args as acc
  | .proj _ _ y _ => acc.insert y
  | _ => acc

/-- Variables used in `c`. -/
partial def codeUses (c : Code .pure) (acc : Std.HashSet FVarId) : Std.HashSet FVarId :=
  match c with
  | .let d k => codeUses k (valueUses d.value acc)
  | .fun d k _ | .jp d k => codeUses k (codeUses d.value acc)
  | .jmp _ as => as.foldl (fun acc a => match a with | .fvar y => acc.insert y | _ => acc) acc
  | .cases cs => cs.alts.foldl (fun acc alt => codeUses alt.getCode acc) (acc.insert cs.discr)
  | .return y => acc.insert y
  | .unreach _ => acc

/-- Whether `x` is used in `c` or by a join point that `c` jumps to (`jps`:
the bodies of the join points declared outside `c`). -/
partial def usesVar (jps : Std.HashMap FVarId (Code .pure)) (x : FVarId) (c : Code .pure) : Bool :=
  go {} c
where
  go (seen : FVarIdSet) (c : Code .pure) : Bool :=
    if hasFVar x c then true else jumpsUsing seen c
  jumpsUsing (seen : FVarIdSet) (c : Code .pure) : Bool :=
    match c with
    | .let _ k => jumpsUsing seen k
    | .fun d k _ | .jp d k => jumpsUsing seen d.value || jumpsUsing seen k
    | .jmp j _ =>
      match jps[j]? with
      | some b => !seen.contains j && go (seen.insert j) b
      | none => false
    | .cases cs => cs.alts.any (jumpsUsing seen ·.getCode)
    | .return _ | .unreach _ => false

/-- Whether `x` is a field of a constructor application in `c` (or in a join
point that `c` jumps to). -/
partial def usedAsField (env : Environment) (jps : Std.HashMap FVarId (Code .pure)) (x : FVarId)
    (c : Code .pure) : Bool :=
  go {} c
where
  go (seen : FVarIdSet) (c : Code .pure) : Bool :=
    match c with
    | .let d k =>
      (match d.value with
       | .const f _ args _ =>
         env.isConstructor f && args.any fun a => match a with | .fvar y => y == x | _ => false
       | _ => false) || go seen k
    | .fun d k _ | .jp d k => go seen d.value || go seen k
    | .jmp j _ =>
      match jps[j]? with
      | some b => !seen.contains j && go (seen.insert j) b
      | none => false
    | .cases cs => cs.alts.any (go seen ·.getCode)
    | .return _ | .unreach _ => false

/-- Whether `c` returns `x` itself, or passes it to a join point (which may
return it), following jumps to the join points in scope (`jps`). -/
partial def returnedWhole (jps : Std.HashMap FVarId (Code .pure)) (x : FVarId) (c : Code .pure) : Bool :=
  go {} c
where
  go (seen : FVarIdSet) (c : Code .pure) : Bool :=
    match c with
    | .let _ k => go seen k
    | .fun d k _ | .jp d k => go seen d.value || go seen k
    | .jmp j args =>
      args.any (fun | .fvar y => y == x | _ => false) ||
        match jps[j]? with
        | some b => !seen.contains j && go (seen.insert j) b
        | none => false
    | .cases cs => cs.alts.any (go seen ·.getCode)
    | .return y => y == x
    | .unreach _ => false

/-- One pass over `c` for a matched value `x`: whether `c` uses `x` (as
`usesVar`, with `jps` the bodies of the join points declared outside `c`),
and the variables used in `c` outside the alternatives (of `cases` in `c`)
that do not use `x`. The latter are the fields of `x` that must be bound
before `c` when `x` stays live in `c`. Uses in local functions and join
points count (conservatively). A `cases` with one alternative (a structure)
is no branch: its code counts as the rest of `c`, since it is lowered
without `lowerAlt`. The state caches whether a join point's body uses `x`. -/
partial def liveScan (jps : Std.HashMap FVarId (Code .pure)) (x : FVarId) (c : Code .pure) :
    StateM (Std.HashMap FVarId Bool) (Bool × Std.HashSet FVarId) := do
  let inArg : Arg .pure → Bool := fun | .fvar y => y == x | _ => false
  let argUses (as : Array (Arg .pure)) : Std.HashSet FVarId :=
    as.foldl (fun acc a => match a with | .fvar y => acc.insert y | _ => acc) {}
  match c with
  | .let d k =>
    let (m, e) ← liveScan jps x k
    let here := match d.value with
      | .fvar f args => f == x || args.any inArg
      | .const _ _ args _ => args.any inArg
      | .proj _ _ y _ => y == x
      | _ => false
    return (m || here, valueUses d.value e)
  | .fun d k _ =>
    let (m, e) ← liveScan jps x k
    return (m || hasFVar x d.value, codeUses d.value e)
  | .jp d k =>
    let (mj, _) ← liveScan jps x d.value
    modify (·.insert d.fvarId mj)
    let (m, e) ← liveScan jps x k
    return (m || mj, codeUses d.value e)
  | .jmp j as =>
    let f ← match (← get)[j]? with
      | some b => pure b
      | none =>
        let b := match jps[j]? with
          | some body => usesVar jps x body
          | none => false
        modify (·.insert j b)
        pure b
    return (as.any inArg || f, argUses as)
  | .cases cs =>
    let mut m := cs.discr == x
    let mut e : Std.HashSet FVarId := ({} : Std.HashSet FVarId).insert cs.discr
    for alt in cs.alts do
      let (ma, ea) ← liveScan jps x alt.getCode
      m := m || ma
      -- Merge the smaller set into the larger (deep chains stay linear).
      if cs.alts.size == 1 || ma then
        e := if ea.size ≥ e.size then e.fold (·.insert ·) ea else ea.fold (·.insert ·) e
    return (m, e)
  | .return y => return (y == x, ({} : Std.HashSet FVarId).insert y)
  | .unreach _ => return (false, {})

/-- The fields to bind before `c` when `x` stays live in `c` (see
`liveScan`), added to `acc`. -/
def usesWhileLive (jps : Std.HashMap FVarId (Code .pure)) (x : FVarId) (c : Code .pure)
    (acc : Std.HashSet FVarId) : Std.HashSet FVarId :=
  ((liveScan jps x c).run' {}).2.fold (·.insert ·) acc

/-! ## Code -/

/-- Free variable names of an RR expression/block (for outlined join points). -/
partial def rrFreeVars (e : RR.Expr) (bound : Std.HashSet String) (acc : Std.HashSet String) : Std.HashSet String :=
  match e with
  | .var n => if bound.contains n || n.startsWith "L2RUnit" then acc else acc.insert n
  | .atom _ => acc
  | .call _ _ args => args.foldl (fun acc a => rrFreeVars a bound acc) acc
  | .apply f a => rrFreeVars a bound (rrFreeVars f bound acc)
  | .ctor _ _ args => args.foldl (fun acc a => rrFreeVars a bound acc) acc
  | .field e _ => rrFreeVars e bound acc
  | .cast e _ => rrFreeVars e bound acc
  | .lam x _ b => blockFreeVars b (bound.insert x) acc
  | .ite c t f => blockFreeVars f bound (blockFreeVars t bound (rrFreeVars c bound acc))
  | .mtch s arms => arms.foldl (fun acc arm =>
      let bound := arm.binders.foldl (fun b x => match x with | some x => b.insert x | none => b) bound
      blockFreeVars arm.body bound acc) (rrFreeVars s bound acc)
  | .block b => blockFreeVars b bound acc
where
  blockFreeVars (b : RR.Block) (bound : Std.HashSet String) (acc : Std.HashSet String) : Std.HashSet String :=
    let (bound, acc) := b.lets.foldl (fun (bound, acc) (x, _, e) => (bound.insert x, rrFreeVars e bound acc)) (bound, acc)
    rrFreeVars b.result bound acc

mutual
  /-- Lower a code block whose value has Reussir type `retTy`. -/
  partial def lowerCode (ctx : CodeCtx) (outlined : FVarIdSet) (retTy : RR.Ty) (c : Code .pure) :
      LowerM RR.Block := do
    match c with
    | .let d k =>
      let t ← lowerType d.type
      -- J4: a self tail call re-enters the state machine.
      if let some sm := ctx.sm then
        if let .const f _ args _ := d.value then
          if f == sm.self && args.size == sm.arity && t == retTy then
            if let .return x := k then
              if x == d.fvarId then
                let some selfDecl := (← read).decls.find? f | throwError "lean2rr: no declaration {f}"
                let (ps, _) := splitFnType selfDecl.type sm.arity
                let vals ← (args.zip ps).mapM fun (a, p) => do lowerArg ctx a (← lowerType p)
                return .ofExpr (.call sm.fn #[] (vals.push (.ctor sm.mode (some sm.entry) #[])))
      let e ← try lowerLetValue ctx d.value d.type t
        catch ex => throwError "{ex.toMessageData}\n  in let {d.binderName} : {d.type}"
      let x ← fresh "x"
      let b ← lowerCode { ctx with vars := ctx.vars.insert d.fvarId (x, t) } outlined retTy k
      return { b with lets := #[(x, some t, e)] ++ b.lets }
    | .return x =>
      match ctx.vars[x]? with
      | some (n, t) => return .ofExpr (← coerce (.var n) t retTy)
      | none => throwError "lean2rr: return of unbound variable (internal error)"
    | .unreach _ => return .ofExpr (.call "l2r_unreachable" #[retTy] #[])
    | .cases cs => return .ofExpr (← lowerCases ctx outlined retTy cs)
    | .jmp j args =>
      match ctx.jumps[j]? with
      | some (.inline params body) =>
        -- J1: bind the parameters to the arguments, then the body.
        let mut ctx' := ctx
        let mut lets := #[]
        for (p, a) in params.zip args do
          let t ← lowerType p.type
          let x ← fresh "j"
          lets := lets.push (x, some t, ← lowerArg ctx a t)
          ctx' := { ctx' with vars := ctx'.vars.insert p.fvarId (x, t) }
        let b ← lowerCode ctx' outlined retTy body
        return { b with lets := lets ++ b.lets }
      | some (.yield tys) =>
        let vals ← (args.zip tys).mapM fun (a, t) => lowerArg ctx a t
        match vals.size with
        | 0 => return .ofExpr .unitVal
        | 1 => return .ofExpr vals[0]!
        | _ => return .ofExpr (.ctor (← tupleType tys) none vals)
      | some (.call fn captured) =>
        let tys := ctx.jpParams.getD j #[]
        let vals ← (args.zip tys).mapM fun (a, t) => lowerArg ctx a t
        return .ofExpr (.call fn #[] (captured.map .var ++ vals))
      | some (.enter variant captured) =>
        let some sm := ctx.sm | throwError "lean2rr: state-machine jump outside a state machine"
        let tys := ctx.jpParams.getD j #[]
        let vals ← (args.zip tys).mapM fun (a, t) => lowerArg ctx a t
        return .ofExpr (.call sm.fn #[] (sm.params.map .var |>.push (.ctor sm.mode (some variant) (captured.map .var ++ vals))))
      | none => throwError "lean2rr: jump to unknown join point (internal error)"
    | .jp d k =>
      let ptys ← d.params.mapM (lowerType ·.type)
      let ctx := { ctx with jpParams := ctx.jpParams.insert d.fvarId ptys,
                            jpBodies := ctx.jpBodies.insert d.fvarId d.value }
      if outlined.contains d.fvarId then
        -- J3: outline the body into a function over its free variables.
        let pnames ← d.params.mapM fun _ => fresh "p"
        let vars := (d.params.zip (pnames.zip ptys)).foldl (fun m (p, nt) => m.insert p.fvarId nt) ctx.vars
        let bodyCtx := { ctx with vars }
        let body ← lowerCode bodyCtx outlined retTy d.value
        let bound := pnames.foldl (·.insert ·) ({} : Std.HashSet String)
        let free := (rrFreeVars.blockFreeVars body bound {}).toArray.qsort (· < ·)
        let varTys : Std.HashMap String RR.Ty := ctx.vars.fold (fun m _ (n, t) => m.insert n t) {}
        let captured := free.filter varTys.contains
        let fparams := captured.map (fun n => (n, varTys.getD n .unit)) ++ pnames.zip ptys
        if let some sm := ctx.sm then
          -- J4: a variant of the state machine.
          let variant ← fresh "j"
          modify fun s => { s with smArms := s.smArms.push (variant, fparams, body) }
          return ← lowerCode { ctx with jumps := ctx.jumps.insert d.fvarId (.enter variant captured) } outlined retTy k
        let fn ← fresh "jp_"
        modify fun s => { s with fns := s.fns.push (.fn fn fparams retTy body) }
        lowerCode { ctx with jumps := ctx.jumps.insert d.fvarId (.call fn captured) } outlined retTy k
      else if (countJumps k {}).getD d.fvarId 0 ≤ 1 ||
          (isSmallJp d && !endsInJumps k (({} : FVarIdSet).insert d.fvarId) outlined) then
        -- J1, or a small join point that is not J2: its body at each jump.
        lowerCode { ctx with jumps := ctx.jumps.insert d.fvarId (.inline d.params d.value) } outlined retTy k
      else
        -- J2: the scope computes the join point's arguments.
        let resTy ← match ptys.size with
          | 0 => pure RR.Ty.unit
          | 1 => pure ptys[0]!
          | _ => pure (RR.Ty.named (← tupleType ptys))
        let scope ← lowerCode { ctx with jumps := ctx.jumps.insert d.fvarId (.yield ptys) } outlined resTy k
        let r ← fresh "jv"
        let mut lets : Array (String × Option RR.Ty × RR.Expr) := #[(r, some resTy, .block scope)]
        let mut ctx' := ctx
        for h : i in [:d.params.size] do
          let p := d.params[i]
          let x ← fresh "y"
          let e := if ptys.size == 1 then RR.Expr.var r else .field (.var r) i
          lets := lets.push (x, some ptys[i]!, e)
          ctx' := { ctx' with vars := ctx'.vars.insert p.fvarId (x, ptys[i]!) }
        let b ← lowerCode ctx' outlined retTy d.value
        return { b with lets := lets ++ b.lets }
    | .fun d k _ =>
      -- Lambda lifting normally removes local functions; lower defensively.
      let ptys ← d.params.mapM (lowerType ·.type)
      let pnames ← d.params.mapM fun _ => fresh "lp"
      let (_, rt) := splitFnType d.type d.params.size
      let rt ← lowerType rt
      let vars := (d.params.zip (pnames.zip ptys)).foldl (fun m (p, nt) => m.insert p.fvarId nt) ctx.vars
      let bodyCtx := { ctx with vars }
      let body ← lowerCode bodyCtx outlined rt d.value
      let mut lam := RR.Expr.block body
      let mut lt := rt
      for (n, t) in (pnames.zip ptys).reverse do
        lt := .fn t lt
        lam := rawFnValue lt n (.ofExpr lam)
      let fty := lt
      let x ← fresh "f"
      let b ← lowerCode { ctx with vars := ctx.vars.insert d.fvarId (x, fty) } outlined retTy k
      return { b with lets := #[(x, some fty, lam)] ++ b.lets }
    | _ => throwError "lean2rr: impure code (internal error)"

  partial def lowerCases (ctx : CodeCtx) (outlined : FVarIdSet) (retTy : RR.Ty) (cs : Cases .pure) :
      LowerM RR.Expr := do
    let some (scrut0, sty0) := ctx.vars[cs.discr]? | throwError "lean2rr: cases on unbound variable"
    -- A `cases` on a value of statically unknown type: convert it to the
    -- inductive's uniform instance first.
    if sty0 == RR.Ty.box then
      let uty ← uniformType cs.typeName
      let u ← fresh "uv"
      let conv ← coerce (.var scrut0) RR.Ty.box uty
      let ctx' := { ctx with vars := ctx.vars.insert cs.discr (u, uty) }
      return .block ⟨#[(u, some uty, conv)], ← lowerCases ctx' outlined retTy cs⟩
    -- A cast value (see `castCases`): converted first, or matched through
    -- the corresponding constructors of its own type.
    let mut view : Option String := none
    match ← castCases sty0 cs.typeName with
    | .same => pure ()
    | .view _ dn => view := some dn
    | .convert dty =>
      let u ← fresh "cv"
      let conv ← coerce (.var scrut0) sty0 dty
      let ctx' := { ctx with vars := ctx.vars.insert cs.discr (u, dty) }
      return .block ⟨#[(u, some dty, conv)], ← lowerCases ctx' outlined retTy cs⟩
    | .unit =>
      -- No data: the only alternative, its fields carry nothing.
      let some alt := cs.alts[0]? | return .call "l2r_unreachable" #[retTy] #[]
      let ctx' := alt.getParams.foldl (fun c p => { c with vars := c.vars.insert p.fvarId ("L2RUnit::u{}", .unit) }) ctx
      return .block (← lowerCode ctx' outlined retTy alt.getCode)
    let (scrut, sty) := (scrut0, sty0)
    let altFor (ctor : Name) : Option (Alt .pure) := cs.alts.find? fun
      | .alt c _ _ _ => c == ctor
      | _ => false
    let dflt : Option (Code .pure) := cs.alts.findSome? fun
      | .default k => some k
      | _ => none
    match sty with
    | .named "bool" =>
      let branch (ctor : Name) : LowerM RR.Block := do
        match altFor ctor with
        | some alt => lowerAlt ctx outlined retTy alt.getCode
        | none =>
          match dflt with
          | some k => lowerAlt ctx outlined retTy k
          | none => return .ofExpr (.call "l2r_unreachable" #[retTy] #[])
      return .ite (.var scrut) (← branch ``Bool.true) (← branch ``Bool.false)
    | .named tn =>
      let some info := (← get).typeInfos[tn]?
        | throwError "lean2rr: cases on non-nominal type {tn} ({cs.typeName})"
      -- The alternatives' constructors, at each constructor position of
      -- the matched type, and their layouts over its records.
      let (actors, layoutOf) ← match view with
        | none => pure (info.ctorOrder, fun c => info.ctors.find? c)
        | some dn =>
          let some di := (← get).typeInfos[dn]? | throwError "lean2rr: no type {dn}"
          let mut m : NameMap CtorLayout := {}
          for (sc, dc) in info.ctorOrder.zip di.ctorOrder do
            if let (some sl, some dl) := (info.ctors.find? sc, di.ctors.find? dc) then
              m := m.insert dc (← viewLayout sc dc sl dl)
          pure (di.ctorOrder, fun c => m.find? c)
      match info.shape with
      | .struct =>
        let some alt := cs.alts[0]? | throwError "lean2rr: empty cases"
        match alt with
        | .alt ctor ps k _ =>
          let some layout := layoutOf ctor | throwError "lean2rr: bad constructor"
          let mut ctx' := ctx
          let mut lets := #[]
          -- A shared structure that stays live because it is stored or
          -- returned whole binds only the fields used while it is live; the
          -- others are projected in the inner alternatives that use them
          -- (`lowerAlt`), as for the constructors of an enum (below): a
          -- field projected here would be an extra reference whose release
          -- Reussir's token reuse takes for a freed cell.
          let lazyOk := !info.value && view.isNone &&
            (usedAsField (← getEnv) ctx.jpBodies cs.discr k || returnedWhole ctx.jpBodies cs.discr k)
          let early := if lazyOk then usesWhileLive ctx.jpBodies cs.discr k {} else {}
          let used := if lazyOk then codeUses k {} else {}
          let mut pending := #[]
          for h : i in [:ps.size] do
            let p := ps[i]
            match layout.fields[i]? with
            | some (some (j, ft)) =>
              if lazyOk && !early.contains p.fvarId then
                if used.contains p.fvarId then pending := pending.push (p.fvarId, j, ft)
              else
                let x ← fresh "f"
                lets := lets.push (x, some ft, RR.Expr.field (.var scrut) j)
                ctx' := { ctx' with vars := ctx'.vars.insert p.fvarId (x, ft) }
            | _ => ctx' := { ctx' with vars := ctx'.vars.insert p.fvarId ("L2RUnit::u{}", .unit) }
          if !pending.isEmpty then
            let l : LazyMatch := { discr := cs.discr, scrut, ty := tn, variant := layout.variant, nbinders := 0,
                                   fields := pending, pending, struct := true }
            ctx' := { ctx' with lazy := ctx'.lazy.push l }
          let b ← lowerCode ctx' outlined retTy k
          return .block { b with lets := lets ++ b.lets }
        | .default k => return .block (← lowerCode ctx outlined retTy k)
        | _ => throwError "lean2rr: impure alternative"
      | _ =>
        let mut arms := #[]
        for ctor in actors do
          let some layout := layoutOf ctor | continue
          match altFor ctor with
          | some (.alt _ ps k _) =>
            let mut ctx' := ctx
            let mut binders := Array.replicate (layout.fields.filter (·.isSome)).size (none : Option String)
            for h : i in [:ps.size] do
              let p := ps[i]
              match layout.fields[i]? with
              | some (some (j, ft)) =>
                let x ← fresh "f"
                binders := binders.set! j (some x)
                ctx' := { ctx' with vars := ctx'.vars.insert p.fvarId (x, ft) }
              | _ => ctx' := { ctx' with vars := ctx'.vars.insert p.fvarId ("L2RUnit::u{}", .unit) }
            -- An arm in which the matched value stays live because it is
            -- stored whole in a new constructor, or returned whole (`simp`
            -- turns `t@(node l k r)` rebuilt into `t`: a BST insert of a key
            -- already present), binds only the fields needed while it is
            -- live; a field used only in inner alternatives that do not use
            -- the value is bound there, by matching the value again
            -- (`lowerAlt`). Reussir projects a match's fields at the match:
            -- a field of a value that stays live is then an extra reference
            -- (inc and dec), and its release looks like a reusable cell to
            -- Reussir's token reuse, which prefers it to the cell actually
            -- freed and then never reuses anything (TreeMap's `balance`
            -- rebuilt every node of the path; a BST insert with `Nat` keys,
            -- whose comparison is a call before the branch, every node).
            -- Not for values only passed to calls: there reusing the cell
            -- (merge's `go l₁ ys (y :: acc)`) measured slower for mergesort,
            -- whose lists then keep the scattered order of the input cells.
            if !binders.isEmpty && info.shape == .enum &&
                (usedAsField (← getEnv) ctx.jpBodies cs.discr k || returnedWhole ctx.jpBodies cs.discr k) then
              let early := usesWhileLive ctx.jpBodies cs.discr k {}
              let used := codeUses k {}
              let mut fields := #[]
              let mut pending := #[]
              for h : i in [:ps.size] do
                let p := ps[i]
                if let some (some (j, ft)) := layout.fields[i]? then
                  if used.contains p.fvarId then fields := fields.push (p.fvarId, j, ft)
                  if !early.contains p.fvarId then
                    binders := binders.set! j none
                    ctx' := { ctx' with vars := ctx'.vars.erase p.fvarId }
                    if used.contains p.fvarId then pending := pending.push (p.fvarId, j, ft)
              if !fields.isEmpty then
                let l : LazyMatch :=
                  { discr := cs.discr, scrut, ty := tn, variant := layout.variant,
                    nbinders := binders.size, fields, pending }
                ctx' := { ctx' with lazy := ctx'.lazy.push l }
            -- In the arm of a constructor without fields, the matched value
            -- is that constructor, which costs nothing to build (`leaf` used
            -- as the children of a new node).
            let mut pre := #[]
            if binders.isEmpty && hasFVar cs.discr k then
              let x ← fresh "nc"
              pre := #[(x, some sty, RR.Expr.ctor tn (some layout.variant) #[])]
              ctx' := { ctx' with vars := ctx'.vars.insert cs.discr (x, sty),
                                  lazy := ctx'.lazy.map fun l =>
                                    { l with fields := l.fields.filter (·.1 != cs.discr),
                                             pending := l.pending.filter (·.1 != cs.discr) } }
            let body ← lowerAlt ctx' outlined retTy k
            arms := arms.push { ty := tn, ctor := some layout.variant, binders, body := { body with lets := pre ++ body.lets } }
          | _ => pure ()
        if arms.size < info.ctorOrder.size then
          let body ← match dflt with
            | some k => lowerAlt ctx outlined retTy k
            | none => pure (.ofExpr (.call "l2r_unreachable" #[retTy] #[]))
          arms := arms.push { ty := tn, ctor := none, binders := #[], body }
        return .mtch (.var scrut) arms
    | t => throwError "lean2rr: cases on value of type {t.render} ({cs.typeName})"

  /-- Lower the code of an alternative. A lazily matched value (see
  `lowerCases`) whose fields the alternative uses is matched again first.
  When the alternative does not use the value itself, the value dies here:
  this match consumes it and binds every field the alternative uses (also
  those bound before, which are then only borrowed). Otherwise it binds the
  pending fields needed while the value is live. -/
  partial def lowerAlt (ctx : CodeCtx) (outlined : FVarIdSet) (retTy : RR.Ty) (k : Code .pure) :
      LowerM RR.Block := do
    if ctx.lazy.isEmpty then return ← lowerCode ctx outlined retTy k
    let used := codeUses k {}
    for h : i in [:ctx.lazy.size] do
      let l := ctx.lazy[i]
      let live := usesVar ctx.jpBodies l.discr k
      if l.struct then
        -- A structure: project the pending fields this code uses (while
        -- the structure is live, only those needed before it dies).
        let need := l.pending.filter (used.contains ·.1)
        let now := if live && !need.isEmpty then
            let early := usesWhileLive ctx.jpBodies l.discr k {}
            need.filter (early.contains ·.1)
          else need
        if now.isEmpty then continue
        let scrut := match ctx.vars[l.discr]? with
          | some (n, _) => n
          | none => l.scrut
        let mut lets := #[]
        let mut ctx' := ctx
        for (p, j, ft) in now do
          let x ← fresh "f"
          lets := lets.push (x, some ft, RR.Expr.field (.var scrut) j)
          ctx' := { ctx' with vars := ctx'.vars.insert p (x, ft) }
        let rest := l.pending.filter fun q => !now.any (·.1 == q.1)
        ctx' := { ctx' with lazy :=
          if rest.isEmpty then ctx'.lazy.eraseIdx! i else ctx'.lazy.set! i { l with pending := rest } }
        let body ← lowerAlt ctx' outlined retTy k
        return { body with lets := lets ++ body.lets }
      let now := if live then
          let need := l.pending.filter (used.contains ·.1)
          if need.isEmpty then need else
            let early := usesWhileLive ctx.jpBodies l.discr k {}
            need.filter (early.contains ·.1)
        else l.fields.filter (used.contains ·.1)
      if now.isEmpty then continue
      -- The value's current name: the match of an enclosing lazy value may
      -- have bound it again (it is a field of that value).
      let scrut := match ctx.vars[l.discr]? with
        | some (n, _) => n
        | none => l.scrut
      let mut binders := Array.replicate l.nbinders (none : Option String)
      let mut ctx' := ctx
      for (p, j, ft) in now do
        let x ← fresh "f"
        binders := binders.set! j (some x)
        ctx' := { ctx' with vars := ctx'.vars.insert p (x, ft) }
      let rest := l.pending.filter fun q => !now.any (·.1 == q.1)
      ctx' := { ctx' with lazy :=
        if live then ctx'.lazy.set! i { l with pending := rest } else ctx'.lazy.eraseIdx! i }
      let body ← lowerAlt ctx' outlined retTy k
      return .ofExpr (.mtch (.var scrut) #[
        { ty := l.ty, ctor := some l.variant, binders, body },
        { ty := l.ty, ctor := none, binders := #[], body := .ofExpr (.call "l2r_unreachable" #[retTy] #[]) }])
    lowerCode ctx outlined retTy k
end

/-- Can Reussir types `a` and `b` represent the same Lean type? `Box` stands
for any type; arrays compare their elements, instantiations of an inductive
their head. -/
partial def reprCompatible (a b : RR.Ty) : LowerM Bool := do
  if a == b || a == RR.Ty.box || b == RR.Ty.box then return true
  match a, b with
  | .fn a1 b1, .fn a2 b2 => return (← reprCompatible a1 a2) && (← reprCompatible b1 b2)
  | .app "LCell" _, .app "LCell" _ =>
    -- Thunks (or tasks) with compatible values.
    match ← lazyOf? a, ← lazyOf? b with
    | some (_, k1, va), some (_, k2, vb) => return k1 == k2 && (← reprCompatible va vb)
    | _, _ => return false
  | _, _ =>
    if let (some ra, some rb) := (← arrayRepr? a, ← arrayRepr? b) then
      return ← reprCompatible ra.value rb.value
    match a, b with
    | .named an, .named bn =>
      match ← nominalHead an, ← nominalHead bn with
      | some ha, some hb => return ha == hb
      | _, _ => return false
    | _, _ => return false

/-- Whether a `Box` holding a value of type `vt` may be read at type `t`
(itself, or through `unsafeCast` a type that Lean represents alike), so that
the unboxing function to `t` converts it: words (`Nat`, `Int`,
`UInt8/16/32`, `Bool`, enumerations) as words (`wordOf`/`ofWord`), values
of another inductive with the same layout (`isomorphic` and `retypableAux`:
the value as it is), `UInt64` and `Float` (`UInt32` and `Float32`) by their
bits. Other casts convert in typed code, where they are written, but not
through a `Box`: every unboxing function would match (and convert from)
every type its constructors can read, e.g. every structure with one
function field (the dictionaries of uniform code), building wrappers between
unrelated function types. -/
def boxCastCompatible (vt t : RR.Ty) : LowerM Bool := do
  let .named a := vt | return false
  let .named b := t | return false
  if a == b then return true
  let word (n : String) : LowerM Bool := do
    if n ∈ ["Nat", "Int", "u8", "u16", "u32", "bool"] then return true
    return ((← get).typeInfos[n]?.map (·.shape == .enumLike)).getD false
  if (← word a) && (← word b) then return true
  if [("u64", "f64"), ("f64", "u64"), ("u32", "f32"), ("f32", "u32")].contains (a, b) then return true
  let infos := (← get).typeInfos
  if infos.contains a && infos.contains b then
    return (← isomorphic a b) && (← retypableAux vt t #[]).isSome
  return false

/-- Generate the bodies of all `Box → nominal` and `Box → array` converters.
A converter matches every `Box` variant that can hold a value of the
target's Lean type and converts it: for a nominal type, any instantiation of
its inductive (structurally); for an array type, any array representation
with compatible elements (element by element; e.g. an `Array Nat` built by
uniform-representation code is boxed as `RVec<Box>`, but its consumer wants
`LNatArr`). Other variants are unreachable. A boxed unit
is Lean's `box(0)` placeholder and becomes the target's zero. Generating a
conversion may add `Box` variants (for fields), so this iterates until the
variant set is stable. -/
partial def finishUnboxFns : LowerM Unit := do
  let mut done : Std.HashMap String Nat := {}
  repeat
    -- Reference dispatch over the boxed reference types (it can box more).
    finishRefFns
    let nvars := (← get).boxVariants.size
    let nominal := (← get).unboxTargets.map fun t => (s!"l2r_unbox_{t}", RR.Ty.named t)
    let arrays := (← get).unboxArrTargets.map fun (t, f) => (f, t)
    let fns := (← get).fnUnboxTargets.map fun t => (s!"l2r_unbox_fn_{t.enc}", t)
    let pending := (nominal ++ arrays ++ fns).filter fun (f, _) => done.getD f 0 != nvars + 1
    -- The identity of a `Box` (`genBoxAddr`) matches every variant too.
    let boxAddrPending := (← get).boxAddrWanted && (← get).boxAddrDone != nvars
    if pending.isEmpty && !boxAddrPending then break
    if boxAddrPending then genBoxAddr
    for (fname, t) in pending do
      let th? ← match t with
        | .named tn => nominalHead tn
        | _ => pure none
      let tArr := (← arrayRepr? t).isSome
      let mut arms : Array RR.Arm := #[]
      for (vt, vname) in (← get).boxVariants do
        let accept ← match th?, vt with
          | some th, .named vn => pure ((← nominalHead vn) == some th)
          | some _, _ => pure false
          | none, .fn .. =>
            -- A function value of any compatible representation (wrapped).
            pure (t matches .fn .. && (← reprCompatible vt t))
          | none, .app "LCell" _ =>
            -- A thunk or task of the same kind with compatible values.
            match ← lazyOf? t, ← lazyOf? vt with
            | some (_, k1, a), some (_, k2, b) => pure (k1 == k2 && (← reprCompatible a b))
            | _, _ => pure false
          | none, _ => pure (tArr && (← arrayRepr? vt).isSome && (← reprCompatible vt t))
        let accept := accept || (vt != .unit && (← boxCastCompatible vt t))
        if !accept then continue
        let x ← fresh "bx"
        -- Arrays of another representation go through `RVec<Box>` (boxing,
        -- then unboxing each element), so that the conversions generated
        -- stay linear in the number of array types, not quadratic (nested
        -- arrays under polymorphic recursion have many representations).
        let boxArr := RR.Ty.app "RVec" #[RR.Ty.box]
        let viaBoxArr := tArr && vt != t && vt != boxArr && t != boxArr && (← arrayRepr? vt).isSome
        let body ← if !viaBoxArr then tryCoerce (.var x) vt t
          else match ← tryCoerce (.var x) vt boxArr with
            | some b => tryCoerce b boxArr t
            | none => pure none
        if let some body := body then
          arms := arms.push { ty := boxName, ctor := some vname, binders := #[some x], body := .ofExpr body }
      let u ← boxVariant .unit
      unless arms.any (·.ctor == some u) do
        arms := arms.push { ty := boxName, ctor := some u, binders := #[none], body := .ofExpr (← zeroValue t) }
      arms := arms.push { ty := boxName, ctor := none, binders := #[], body := .ofExpr (.call "l2r_unreachable" #[t] #[]) }
      let item := RR.Item.fn fname #[("b", RR.Ty.box)] t (.ofExpr (.mtch (.var "b") arms))
      modify fun s => { s with fns := (s.fns.filter fun | .fn n .. => n != fname | _ => true).push item }
      -- Record the variant count this body was generated against; a later
      -- growth of the variant set makes it pending again.
      done := done.insert fname (nvars + 1)

/-- Target `tg` called with all its arguments. -/
def targetCall (tg : FnTarget) (args : Array RR.Expr) : LowerM RR.Expr := do
  match tg.call with
  | .code fn => return .call fn #[] args
  | .extern orig typeArgs params ret => lowerExternCall orig typeArgs params ret args
  | .ctor c fullRt => ctorBuild c fullRt args
  | .stream fd i streamTy => streamFieldCall fd i streamTy args

/-- Generate `l2r_ap<j>_T`, applying a function value of type `t` to `j`
arguments (see "Function values"): a match on the variant. -/
def genApply (t : RR.Ty) (j : Nat) : LowerM Unit := do
  let (doms, _) := fnChain t
  let resJ := fnResult t j
  let tn := RR.fnTypeName t
  let as := (List.range j).toArray.map fun i => s!"l2ra{i}"
  let argsFrom (k : Nat) : Array (RR.Expr × RR.Ty) :=
    (List.range (j - k)).toArray.map fun i => (RR.Expr.var as[k + i]!, doms[k + i]!)
  -- The value `e` of the first `k` arguments (at `fnResult t k`), applied to
  -- the others.
  let rest (e : RR.Expr) (k : Nat) : LowerM RR.Expr := do
    let (r, rt) ← applyExprs e (fnResult t k) (argsFrom k)
    coerce r rt resJ
  let mut arms : Array RR.Arm :=
    #[{ ty := tn, ctor := some "z", binders := #[], body := .ofExpr (← zeroValue resJ) }]
  let rawBody ← rest (.apply (.var "l2rc") (.var as[0]!)) 1
  arms := arms.push { ty := tn, ctor := some "raw", binders := #[some "l2rc"], body := .ofExpr rawBody }
  for v in (← get).fnVariants.getD t #[] do
    let (binders, body) ← match v with
      | .wrap src =>
        let k := min (fnChain src).1.size j
        let (e, et) ← applyExprs (.var "l2rg") src ((argsFrom 0).extract 0 k)
        pure (#[some "l2rg"], ← rest (← coerce e et (fnResult t k)) k)
      | .part id m =>
        let some tg := (← get).fnTargets[id]? | throwError "lean2rr: unknown function target {id}"
        let captured := (List.range m).toArray.map fun i => RR.Expr.var s!"l2rx{i}"
        let r := tg.params.size - m
        let k := min r j
        let mut cargs := #[]
        for i in [:k] do cargs := cargs.push (← coerce (.var as[i]!) doms[i]! tg.params[m + i]!)
        let body ← if k < r then do
            -- Fewer arguments than the target needs: a partial application.
            let (pv, pt) ← partValue tg (captured ++ cargs)
            coerce pv pt resJ
          else do
            let call ← targetCall tg (captured ++ cargs)
            rest (← coerce call tg.ret (fnResult t k)) k
        pure ((List.range m).toArray.map fun i => some s!"l2rx{i}", body)
    arms := arms.push { ty := tn, ctor := some (fnVariantName v), binders, body := .ofExpr body }
  let name := applyFnName t j
  let params := #[("l2rf", t)] ++ as.zip (doms.extract 0 j)
  let item := RR.Item.fn name params resJ (.ofExpr (.mtch (.var "l2rf") arms))
  modify fun s => { s with fns := (s.fns.filter fun | .fn n .. => n != name | _ => true).push item }

/-- Generate `l2r_fconv_S_T` (see `fnConvFn`). A value that is a wrapped
value `g` of a representation `R` (`w<R>(g)`) is converted from `R`
directly: `g` itself when `R` is `T`, otherwise `l2r_fconv_R_T(g)` (generated
on demand). So a function value that travels through several
representations (a reference read at `Nat → Nat`, `Nat → Box` and
`Box → Box` in a loop) stays one wrapper deep, and coming back to its own
representation gives the value itself (like `lazyConv`'s chains). Other
values are wrapped (`w<S>`). -/
def genFnConv (src dst : RR.Ty) : LowerM Unit := do
  let name := s!"l2r_fconv_{src.enc}_{dst.enc}"
  let wrapped := RR.Expr.ctor (RR.fnTypeName dst) (some (fnVariantName (.wrap src))) #[.var "l2rf"]
  let mut arms : Array RR.Arm := #[]
  for v in (← get).fnVariants.getD src #[] do
    let .wrap r := v | continue
    let some e ← tryCoerce (.var "l2rg") r dst | continue
    arms := arms.push { ty := RR.fnTypeName src, ctor := some (fnVariantName v), binders := #[some "l2rg"], body := .ofExpr e }
  let body : RR.Expr := if arms.isEmpty then wrapped
    else .mtch (.var "l2rf") (arms.push { ty := RR.fnTypeName src, ctor := none, binders := #[], body := .ofExpr wrapped })
  let item := RR.Item.fn name #[("l2rf", src)] dst (.ofExpr body)
  modify fun s => { s with fns := (s.fns.filter fun | .fn n .. => n != name | _ => true).push item }

/-- Generate the application functions requested so far, again for those
whose type gained variants. Whether anything was generated. -/
partial def finishFnValues : LowerM Bool := do
  let mut any := false
  repeat
    let mut progress := false
    for (src, dst) in (← get).fnConvs do
      let nv := ((← get).fnVariants.getD src #[]).size
      if (← get).fnConvDone[(src, dst)]? == some nv then continue
      genFnConv src dst
      modify fun s => { s with fnConvDone := s.fnConvDone.insert (src, dst) nv }
      progress := true
    for (t, j) in (← get).fnApplies do
      let nv := ((← get).fnVariants.getD t #[]).size
      if (← get).fnApplyDone[(t, j)]? == some nv then continue
      genApply t j
      modify fun s => { s with fnApplyDone := s.fnApplyDone.insert (t, j) nv }
      progress := true
    for t in (← get).fnAddrTargets do
      let nv := ((← get).fnVariants.getD t #[]).size
      if (← get).fnAddrDone[t]? == some nv then continue
      genFnAddr t
      modify fun s => { s with fnAddrDone := s.fnAddrDone.insert t nv }
      progress := true
    if !progress then break
    any := true
  return any

/-- The fields of the variants of function type `t`, besides `z`/`raw`. -/
def fnVariantFields (v : FnVariant) : LowerM (Array RR.Ty) := do
  match v with
  | .wrap src => return #[src]
  | .part id m =>
    let some tg := (← get).fnTargets[id]? | throwError "lean2rr: unknown function target {id}"
    return tg.params.extract 0 m

/-- Whether a value of type `t` can hold a task, with the final variants
of function types and `Box` (see `mayHoldTask`). A thunk can through its
value, its computation and, converted from another representation, its
original (a `Box`). -/
partial def holdsTask (t : RR.Ty) (seen : List RR.Ty := []) : LowerM Bool := do
  if seen.contains t then return false
  let seen := t :: seen
  match t with
  | .app "LCell" _ =>
    match ← lazyOf? t with
    | some (_, true, _) => return true
    | some (_, false, vt) =>
      return (← holdsTask vt seen) || (← holdsTask (.fn .unit vt) seen) || (← holdsTask RR.Ty.box seen)
    | none => return false
  | .app "RVec" #[st] => holdsTask st seen
  | .fn .. =>
    for v in (← get).fnVariants.getD t #[] do
      for f in ← fnVariantFields v do
        if ← holdsTask f seen then return true
    return false
  | .named n =>
    if n == boxName then
      for (vt, _) in (← get).boxVariants do
        if ← holdsTask vt seen then return true
      return false
    if let some info := (← get).typeInfos[n]? then
      for c in info.ctorOrder do
        let some l := info.ctors.find? c | continue
        for ft in l.posTys do
          if ← holdsTask ft seen then return true
      return false
    match (← get).tupleTypes.toList.find? (·.2 == n) with
    | some (k, _) =>
      let fields := if k.size == 2 && k[1]! == .named "__elem_box" then #[k[0]!] else k
      for ft in fields do
        if ← holdsTask ft seen then return true
      return false
    | none => return false
  | _ => return false

/-- Generate `l2r_persist_T` (`persistCall`) and the traversals it calls,
for the current variants (replacing earlier ones); `done` holds the names
generated in this round. A type that cannot hold a task gets none, and its
values are not looked at. -/
partial def genPersist (t : RR.Ty) (done : IO.Ref (Std.HashSet String)) : LowerM (Option String) := do
  unless ← holdsTask t do return none
  let name := persistFnName t
  if (← done.get).contains name then return some name
  done.modify (·.insert name)
  let u64 := RR.Ty.named "u64"
  let zero : RR.Block := ⟨#[("z", some u64, .atom "0")], .var "z"⟩
  -- Traverse each of the variables `xs`, then 0; the last traversal is a
  -- tail call (a list is traversed in a loop).
  let each (xs : Array (String × RR.Ty)) : LowerM RR.Block := do
    let mut calls : Array (String × RR.Ty × String) := #[]
    for (x, xt) in xs do
      if let some f ← genPersist xt done then calls := calls.push (x, xt, f)
    if calls.isEmpty then return zero
    let mut lets := #[]
    for (x, _, f) in calls.pop do
      lets := lets.push (← fresh "pp", some u64, RR.Expr.call f #[] #[.var x])
    let (lx, _, lf) := calls.back!
    return ⟨lets, .call lf #[] #[.var lx]⟩
  let arm (ty : String) (ctor : String) (xs : Array (Option (String × RR.Ty))) : LowerM RR.Arm := do
    let body ← each (xs.filterMap id)
    return { ty, ctor := some ctor, binders := xs.map (·.map (·.1)), body }
  let body : RR.Block ← match t with
    | .app "LCell" #[.named z] =>
      let some (_, task, vt) ← lazyOf? t | pure zero
      if task then
        -- A task: wait for it (run it), then its value.
        let get ← lazyGetFn z
        let rest ← each #[("x", vt)]
        pure ⟨#[("x", some vt, .call get #[] #[.var "v"])] ++ rest.lets, rest.result⟩
      else
        -- A thunk: its computation or its value, without forcing it.
        let ft := RR.Ty.fn .unit vt
        let arms := #[
          ← arm z "pending" #[some ("f", ft)],
          ← arm z "done" #[some ("x", vt)],
          ← arm z "conv" #[some ("f", ft), some ("o", RR.Ty.box), none],
          ← arm z "convdone" #[some ("x", vt), some ("o", RR.Ty.box), none],
          { ty := z, ctor := none, binders := #[], body := zero }]
        pure (.ofExpr (.mtch (.call "l2r_lcell_get" #[.named z] #[.var "v"]) arms))
    | .app "RVec" #[_] =>
      let some r ← arrayRepr? t | pure zero
      let go := name ++ "_go"
      let rest ← each #[("x", r.value)]
      let loop : RR.Block := .ofExpr <| .ite (.atom "i < n")
        ⟨#[("x", some r.value, r.load (r.call "get" #[.var "v", .var "i"]))] ++ rest.lets ++
          #[("pl", some u64, rest.result), ("one", some u64, .atom "1")],
          .call go #[] #[.var "v", .atom "i + one", .var "n"]⟩ zero
      let goItem := RR.Item.fn go #[("v", t), ("i", u64), ("n", u64)] u64 loop
      modify fun s => { s with fns := (s.fns.filter fun | .fn n .. => n != go | _ => true).push goItem }
      pure ⟨#[("n", some u64, r.call "size" #[.var "v"]), ("i0", some u64, .atom "0")],
        .call go #[] #[.var "v", .var "i0", .var "n"]⟩
    | .fn .. =>
      -- A function value: the values it captures (a Reussir closure's
      -- cannot be looked at).
      let tn := RR.fnTypeName t
      let mut arms : Array RR.Arm := #[]
      for v in (← get).fnVariants.getD t #[] do
        let fs ← fnVariantFields v
        arms := arms.push (← arm tn (fnVariantName v) ((List.range fs.size).toArray.map fun i => some (s!"c{i}", fs[i]!)))
      arms := arms.push { ty := tn, ctor := none, binders := #[], body := zero }
      pure (.ofExpr (.mtch (.var "v") arms))
    | .named n =>
      if n == boxName then
        let mut arms : Array RR.Arm := #[]
        for (vt, bv) in (← get).boxVariants do
          arms := arms.push (← arm boxName bv #[some ("x", vt)])
        pure (.ofExpr (.mtch (.var "v") arms))
      else if let some info := (← get).typeInfos[n]? then
        if info.shape == .struct then
          let some l := info.ctors.find? info.ctorOrder[0]! | pure zero
          let tys := l.posTys
          let xs := (List.range tys.size).toArray.map fun i => (s!"f{i}", tys[i]!)
          let rest ← each xs
          pure ⟨xs.mapIdx (fun i (x, xt) => (x, some xt, RR.Expr.field (.var "v") i)) ++ rest.lets, rest.result⟩
        else
          let mut arms : Array RR.Arm := #[]
          for c in info.ctorOrder do
            let some l := info.ctors.find? c | continue
            let tys := l.posTys
            arms := arms.push (← arm n l.variant ((List.range tys.size).toArray.map fun i => some (s!"f{i}", tys[i]!)))
          pure (.ofExpr (.mtch (.var "v") arms))
      else
        match (← get).tupleTypes.toList.find? (·.2 == n) with
        | some (k, _) =>
          let fields := if k.size == 2 && k[1]! == .named "__elem_box" then #[k[0]!] else k
          let xs := (List.range fields.size).toArray.map fun i => (s!"f{i}", fields[i]!)
          let rest ← each xs
          pure ⟨xs.mapIdx (fun i (x, xt) => (x, some xt, RR.Expr.field (.var "v") i)) ++ rest.lets, rest.result⟩
        | none => pure zero
    | _ => pure zero
  let item := RR.Item.fn name #[("v", t)] u64 body
  modify fun s => { s with fns := (s.fns.filter fun | .fn n .. => n != name | _ => true).push item }
  return some name

/-- The number of variants of function types and of `Box`: the traversals
of `persistCall` depend on them. -/
def variantCount : LowerM (Nat × Nat) := do
  let st ← get
  return (st.fnVariants.fold (fun acc _ vs => acc + vs.size) 0, st.boxVariants.size)

/-- Generate the traversals `persistCall` requested (again when variants
were added since): a type that cannot hold a task gets a traversal that
does nothing. Whether anything was generated. -/
def finishPersistFns : LowerM Bool := do
  let reqs := (← get).persistReqs
  if reqs.isEmpty then return false
  let vc ← variantCount
  if (← get).persistDone == some (reqs.size, vc.1 + vc.2 * 1000003) then return false
  let done ← IO.mkRef ({} : Std.HashSet String)
  for t in reqs do
    if (← genPersist t done).isNone then
      let name := persistFnName t
      let item := RR.Item.fn name #[("v", t)] (.named "u64") ⟨#[("z", some (.named "u64"), .atom "0")], .var "z"⟩
      modify fun s => { s with fns := (s.fns.filter fun | .fn n .. => n != name | _ => true).push item }
  let vc ← variantCount
  let n := (← get).persistReqs.size
  modify fun s => { s with persistDone := some (n, vc.1 + vc.2 * 1000003) }
  return true

/-- The enums of all function types the generated program mentions. -/
def fnTypeItems : LowerM (Array RR.Item) := do
  let st ← get
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
    let .fn d c := t | continue
    if seen.contains t then continue
    seen := seen.insert t
    let mut variants : Array (String × Array RR.Ty) := #[("z", #[]), ("raw", #[.cls d c])]
    work := (RR.Ty.cls d c).subterms work
    for v in (← get).fnVariants.getD t #[] do
      let fs ← fnVariantFields v
      for f in fs do work := f.subterms work
      variants := variants.push (fnVariantName v, fs)
    items := items.push (RR.Item.enum (RR.fnTypeName t) false variants)
  return items

/-- Types whose values need no heap cell. -/
def isUnboxedTy (t : RR.Ty) : LowerM Bool := do
  match t with
  | .named n =>
    if n ∈ ["Nat", "Int", "u8", "u16", "u32", "u64", "i8", "i16", "i32", "i64", "f32", "f64",
            "bool", "L2RUnit"] then return true
    return ((← get).typeInfos[n]?.map (·.shape == .enumLike)).getD false
  | _ => return false

/-- A constant whose code only builds unboxed values from small literals
and constructors (`Int.ofNat 0`, an enumeration value). It cannot panic,
trace or allocate, so it is recomputed at every use: cheaper than reading a
once-cell (native Lean emits such constants as static data). -/
partial def isCheapConst (c : Code .pure) (fuel : Nat := 8) : LowerM Bool := do
  match c with
  | .let d k =>
    unless ← isUnboxedTy (← lowerType d.type) do return false
    let ok ← match d.value with
      | .lit (.str _) => pure false
      | .lit (.nat n) => pure (n < 2 ^ 63)
      | .lit _ => pure true
      | .erased => pure true
      | .const f _ args =>
        if (← getEnv).isConstructor f then pure true
        -- Total conversions of scalars (`UInt32.ofNat 0`, the default of
        -- `Inhabited UInt32`, a float literal's bits: `foldFloatLits`).
        else if isScalarConversion (((← read).keys.find? f).map (·.decl) |>.getD f) then pure true
        -- Another such constant.
        else if args.isEmpty && fuel > 0 then
          match (← read).decls.find? f with
          | some { params := #[], value := .code b, .. } => isCheapConst b (fuel - 1)
          | _ => pure false
        else pure false
      | _ => pure false
    if ok then isCheapConst k fuel else return false
  | .return _ => return true
  | _ => return false
where
  isScalarConversion (f : Name) : Bool :=
    f ∈ [``UInt8.ofNat, ``UInt16.ofNat, ``UInt32.ofNat, ``UInt64.ofNat, ``USize.ofNat,
         ``UInt8.ofNatLT, ``UInt16.ofNatLT, ``UInt32.ofNatLT, ``UInt64.ofNatLT, ``USize.ofNatLT,
         ``Int8.ofNat, ``Int16.ofNat, ``Int32.ofNat, ``Int64.ofNat, ``ISize.ofNat,
         ``Int8.ofInt, ``Int16.ofInt, ``Int32.ofInt, ``Int64.ofInt, ``ISize.ofInt,
         ``Float.ofBits, ``Float32.ofBits,
         ``Char.ofNat, ``Nat.toUInt8, ``Nat.toUInt16, ``Nat.toUInt32, ``Nat.toUInt64,
         ``Nat.toUSize]

/-- Lower a declaration with code to a Reussir function. -/
def lowerDecl (d : Decl .pure) : LowerM Unit := do
  let .code body := d.value | return
  let body := sinkJoinPoints body
  let (ps, r) := splitFnType d.type d.params.size
  let _ := ps
  let ptys ← d.params.mapM (lowerType ·.type)
  let ret ← lowerType r
  let pnames ← d.params.mapM fun _ => fresh "a"
  -- `IO.Process.output`: generated glue instead of Lean's body (see
  -- `processOutputBody`).
  let orig := ((← read).keys.find? d.name).map (·.decl) |>.getD d.name
  if orig == ``IO.Process.output && d.params.size == 3 then
    let block ← processOutputBody (pnames.zip ptys) ret
    modify fun s => { s with fns := s.fns.push (.fn (fnName d.name) (pnames.zip ptys) ret block) }
    return
  let outlined := chooseOutlined body
  -- J4 when an outlined join point tail-calls the declaration: a loop
  -- passes through it. (Other calls need no state machine; going through
  -- its entry wrapper would only cost an allocation per call.)
  let callsBack := outlinedBodies body outlined |>.any (hasSelfTailCall d.name d.params.size)
  let sm? : Option StateMachine ← do
    if !callsBack || d.params.isEmpty || (← IO.getEnv "L2R_NO_J4").isSome then pure none
    else
      let base := fnName d.name
      pure (some { fn := base ++ "_sm", mode := base ++ "_mode", self := d.name, arity := d.params.size, params := pnames })
  modify fun s => { s with smArms := #[] }
  let ctx : CodeCtx := { vars := (d.params.zip (pnames.zip ptys)).foldl (fun m (p, nt) => m.insert p.fvarId nt) {}, sm := sm? }
  let block ← try lowerCode ctx outlined ret body
    catch e => throwError "{e.toMessageData}\n  while lowering {d.name}"
  if let some sm := sm? then
    let arms := (← get).smArms
    -- A shared enum: Reussir miscompiles `[value]` enums whose arms have
    -- different layouts (translation plan §9); Reussir reuses the cell of
    -- the matched value.
    let mode := RR.Item.enum sm.mode false
      (#[(sm.entry, #[])] ++ arms.map fun (v, fps, _) => (v, fps.map (·.2)))
    let mkArm (v : String) (names : Array String) (b : RR.Block) : RR.Arm :=
      { ty := sm.mode, ctor := some v, binders := names.map some, body := b }
    let matchArms := #[mkArm sm.entry #[] block] ++ arms.map fun (v, fps, b) => mkArm v (fps.map (·.1)) b
    let m ← fresh "m"
    modify fun s => { s with
      typeItems := s.typeItems.push mode
      fns := s.fns
        |>.push (.fn sm.fn ((pnames.zip ptys).push (m, .named sm.mode)) ret (.ofExpr (.mtch (.var m) matchArms)))
        |>.push (.fn (fnName d.name) (pnames.zip ptys) ret
            (.ofExpr (.call sm.fn #[] ((pnames.map .var).push (.ctor sm.mode (some sm.entry) #[])))))
      smArms := #[] }
    return
  -- A constant is cached in a once-cell, unless it is cheap to recompute
  -- or a closed term used only once, by another constant (which runs once;
  -- caching every step of an array literal kept every intermediate array).
  if d.params.isEmpty && !(← isCheapConst body) && !(← read).chainConsts.contains d.name then
    let acc ← cafAccessor (fnName d.name) ret
    modify fun s => { s with fns := s.fns.push (.fn (fnName d.name ++ "_init") #[] ret block) |>.push acc }
  else
    modify fun s => { s with fns := s.fns.push (.fn (fnName d.name) (pnames.zip ptys) ret block) }

end LeanToReussir
