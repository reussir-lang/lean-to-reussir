# Calls and `let`s

Paths are relative to `lean2rr/LeanToReussir/` unless they start with
`runtime/`.

### Calls follow Lean's arities exactly

- **What:** A call with exactly the callee's arity (the number of
  parameters Lean gave it after its optimizations) runs it; fewer
  arguments build a partial application (a `p` variant, nothing runs); more
  arguments run it and apply the result to the rest.
- **Why:** Where work runs is observable: the native build of
  `mkAdder` with a `dbgTrace` before its inner `fun` has arity 2 and prints
  once per call of `mkAdder 3 x`; a translation at arity 1 prints once in
  total.
- **Where:** `Lower/Values.lean`: `lowerConstApp`; `Lower/Decls.lean`:
  `calleeOf`, `partialApp`, `applyChain`; plan
  [§5.2](../../translation-plan.md#52-declarations-calls-arities).
- **Remove only if:** never.

### Lean's `let`s that can have an effect are never dropped, duplicated on a path, or reordered

- **What:** Lowering adds bindings of its own (conversions, placeholders,
  copies of duplicated join points, one per path) but keeps every Lean
  `let` that can have an effect, in order, once per path. The only fusion
  is of effect-free `let`s: `ArrayLits` replaces a run of small `Nat`
  literals and their pushes onto an `Array Nat` by one table call.
- **Why:** A `let` can call a function that panics or traces; Lean's
  passes have already removed dead `let`s.
- **Where:** `Lower/Code.lean`: `lowerCode`; plan
  [§5.4](../../translation-plan.md#54-let-return-literals).
- **Remove only if:** never.

### Effects are kept in order by opaque FFI calls

- **What:** The IO world is only an `L2RUnit` value; what orders effects
  is that IO, `ST.Ref`, panic and trace operations are effectful FFI calls,
  which Reussir and LLVM never merge, drop or reorder. lean2rr relies on
  the same property to place a release after a call
  (`l2r_release_after`).
- **Why:** Nothing else would stop Reussir or LLVM from merging two
  identical `println` calls (probe results, plan
  [§9](../../translation-plan.md#9-open-items)).
- **Where:** `runtime/prelude.rr` (`#[ffi(import)]` functions);
  plan [§5.8](../../translation-plan.md#58-externs-and-runtime-calls)
  ("Effects are never optimized away").
- **Remove only if:** never.

### A run of `let`s is lowered in a loop

- **What:** `lowerCode` lowers a run of `let`s in one loop, each value
  with a map of just the variables it reads; the run's own variables
  collect in a map merged once at the end.
- **Why:** Growing the context's map copied it at every `let`, so a long
  straight-line body (a spliced literal) cost quadratic time (7c4ab5c).
  The output is the same.
- **Where:** `Lower/Code.lean`: `lowerCode` (the `.let` case).
- **Remove only if:** never.

### Constructors implemented by the runtime are calls

- **What:** Constructors of builtin types that carry an `@[extern]`
  (`Int.ofNat` is `lean_nat_to_int`, `Int.negSucc`, `ByteArray.mk`, …) are
  extern calls; `Thunk.mk` and `Task.pure` get glue.
- **Why:** As in Lean's IR; they are not constructors of `Int` (runtime
  request 1, f67bbec; 4674426).
- **Where:** `Lower/Decls.lean`: `calleeOf`; `Lower/LazyGlue.lean`:
  `lazyExtern`.
- **Remove only if:** never.

### Panics continue; `unreachable` stops the program

- **What:** `panic!` prints the message native prints (`PANIC at …`) and
  then `backtrace:` and `(stack trace unavailable)` where native prints the
  frames (unless `LEAN_BACKTRACE=0`, which prints neither; a divergence of
  plan §10), through the current stderr stream, and returns the default
  value;
  `LEAN_ABORT_ON_PANIC` aborts. `unreachable`, and lean2rr's own
  impossibilities (a `Box` unwrap of another variant, a cast with no
  conversion), print `INTERNAL PANIC: unreachable code has been reached`
  and exit 1.
- **Why:** Native behaviour; lean2rr's impossibilities look like Lean's
  own (plan [§5.9](../../translation-plan.md#59-panics-and-unreachable-code)).
- **Where:** `runtime/prelude.rr`: `l2r_panic_text`, `l2r_panic_str`,
  `lean_panic_fn`, `l2r_unreachable`, `l2r_internal_panic`; lean-runtime's
  `io::panic` (`report`, `internal_panic`), through `runtime/leanrt/src/lib.rs`
  ([../externs-ffi/runtime.md](../externs-ffi/runtime.md), switch step 8).
- **Remove only if:** never.
