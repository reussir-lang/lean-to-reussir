# Function values

Paths are relative to `lean2rr/LeanToReussir/`. Plan
[§5.2](../../translation-plan.md#52-declarations-calls-arities) and
[§5.3](../../translation-plan.md#53-closures-function-values).

### Function values are generated enums, not Reussir closures

- **What:** A Lean function value of (lowered, curried) type `T` is a
  value of a generated shared enum `L2RFn_<T>` whose variants say what it
  is: `p<m>_<target>(c₁…cₘ)`, a declaration, extern, constructor or
  standard-stream primitive with its first `m` arguments captured (nullary
  when `m = 0`: no allocation); `raw(A -> …)`, a Reussir closure built by
  glue; `w<S>(g)`, a value of another representation `S` of the same Lean
  type; `z`, the `box(0)` placeholder.
- **Why:** Applying a shared Reussir closure copies it first, and curried
  application allocates a closure per argument. With the enum, the
  dispatch is a `match` and a known target a direct call: 10^8 calls of
  shared function values took 0.09 s this way, 0.55 s with Reussir
  closures; the classic higher-order went from 1.60x to 0.67x native
  (2a3f3c1).
- **Where:** `Lower/FnValues.lean`: `partValue`, `rawFnValue`, `fnChain`;
  `LowerBase.lean`: `FnTarget`, `FnVariant`, `FnCall`; `RR.lean`:
  `fnTypeName`; `Lower/Finish.lean`: `fnTypeItems`.
- **Remove only if:** never (the classic higher-order program is the
  measurement).

### Application functions follow `lean_apply_n`

- **What:** `g a₁ … aⱼ` calls a generated `l2r_ap<j>_T(g, a…)` (at most
  the chain length at a time) that matches the variant: a target whose
  remaining arity is `j` is called directly; with fewer arguments a new
  `p` value is built; with more, the target is called with as many as it
  takes and its result applied to the rest. The application functions and
  the enums are generated at the end, again whenever a type gains a
  variant, until nothing changes.
- **Why:** A target runs exactly when its last argument arrives, Lean's
  runtime rule (`apply.cpp`); the variant records the target's own arity,
  so values of one type can have different arities.
- **Where:** `Lower/Finish.lean`: `genApply`, `finishFnValues`;
  `Lower/FnValues.lean`: `applyCall`; `Lower/Decls.lean`: `applyExprs`,
  `applyChain`; `Emit/Program.lean`: `lowerProgram`.
- **Remove only if:** never.

### A function value at another representation is wrapped once

- **What:** Converting a function value to another representation of the
  same Lean type wraps it in `w<S>`; converting a wrapped value converts
  the value inside from its own representation instead of wrapping again.
- **Why/Where:** see
  [../conversions/wrappers.md](../conversions/wrappers.md#function-values-stay-one-wrapper-deep).
- **Remove only if:** see the linked entry.

### Prelude callbacks get Reussir closures

- **What:** Runtime helpers that take a Reussir closure (`dbgTrace`,
  `timeit`, the constructor callbacks of glue) receive
  `|x| l2r_ap1_…(g, x)`; glue that builds a function value from Reussir
  code uses the `raw` variant.
- **Why:** The prelude cannot name lean2rr's generated enums.
- **Where:** `Lower/ExternCall.lean`: `lowerExternCall`
  (`valueGenericCls`); `Emit/Program.lean`: `valueGenericClosureParams`;
  `Lower/FnValues.lean`: `rawFnValue`.
- **Remove only if:** never.

### Reussir applies only variables and call results

- **What:** Glue binds a complex expression (a constructor, a block) to a
  fresh variable before it applies it or projects a field of it.
- **Why:** Reussir's syntax only applies variables and call results
  (4674426).
- **Where:** `Lower/LazyGlue.lean`: `withVar` (used across the glue,
  e.g. `runIO`, `lazyGet`; also `Lower/Values.lean`,
  `Lower/Process.lean`).
- **Remove only if:** Reussir accepts any expression as a callee.

### The standard streams are records of nullary variants

- **What:** `IO.getStdout` & co. build a Lean `IO.FS.Stream` record whose
  fields are nullary `p0` variants targeting the runtime's stream
  primitives (`FnCall.stream`).
- **Why:** The record is then the only allocation.
- **Where:** `Lower/Externs.lean`: `streamValue`, `streamFieldCall`;
  `LowerBase.lean`: `FnCall`.
- **Remove only if:** never.
