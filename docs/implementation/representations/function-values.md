# Function values

Paths are relative to `lean2rr/LeanToReussir/`. Plan
[§5.2](../../translation-plan.md#52-declarations-calls-arities) and
[§5.3](../../translation-plan.md#53-closures-function-values).

### Function values are generated enums, not Reussir closures

- **What:** A Lean function value of (lowered, curried) type `T` is a
  value of a generated shared enum `L2RFn_<T>` (one per run-time type,
  `RR.Ty.rt`) whose variants say what it is: `p<j>_<target>(c₁…)`, a
  declaration, extern, constructor or standard-stream primitive applied to
  its first `j` Lean arguments, of which it captures those it takes
  (rule 4: not the erased ones; nullary when it captures none: no
  allocation); `raw(A -> …)`, a Reussir closure built by glue; `w<S>(g)`,
  a value of another representation `S` of the same Lean type (named
  `w<S>_<T>` when `T` has phantom domains); `z`, the `box(0)`
  placeholder.
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
  `Lower/FnValues.lean`: `applyCall`; `Lower/Decls.lean`: `applyLean`,
  `applyExprs`, `applyChain`; `Emit/Program.lean`: `lowerProgram`.
- **Remove only if:** never.

### Erased domains of function types are unit or phantom (rule 4)

- **What:** An erased domain (`◾`) of a function type is a unit domain
  when some function value can run its body right after it; otherwise it
  is a *phantom* domain (`RR.Ty.phantom`), which has no parameter at run
  time. The RR type keeps the phantom domain, so that it still has Lean's
  positions; its run-time type (`RR.Ty.rt`, which names the enum, its
  variants and its application functions) does not. Example: Op.run
  `{α : Type} → List α → Nat`, filled with `List.length` and
  `fun xs => …`, is `L2RFn_<List_Box → Nat>`, and the lambda's function is
  `ops_lam(xs)`. A value of `mkF n b : (α : Type) → β`
  (`β := List Nat → Nat`) runs `mkF` when the type is applied, so in a
  program with such a value the domain stays: `Unit → List_Box → Nat`, and
  the other values of the type ignore that unit. (Lean eta-expands
  definitions and lambdas to the arity of their type, so a value that
  completes before a later domain comes from generic code whose result
  type is instantiated at a function type, as `mkF`.)

  The decision (`keptErasedHead`, in `lowerType`) is by the type from
  that domain on. The domain stays when it is the type's last domain; when
  a value that completes at an erased domain of its own type has the same
  skeleton from there (each domain erased, data or `lcAny`, and whether
  the codomain may hide more domains; `eMarks`, `Skel.unify`); or when a
  value that completes there can *become* a value of this type
  (`flowAnalysis`, `reached`). `flowAnalysis` reads mono LCNF once
  (`lowerProgram`): the values created (a declaration, extern or
  constructor applied to fewer arguments than its arity, a local `fun`,
  each with the position where it completes), and the edges between
  function types: a variable of type `S` used at a position of type `T`
  (an argument and its parameter, a constructor argument and its field, a
  returned value and the result type, a jump argument and its parameter,
  a field and the variable bound to it; their domains the other way round;
  for two instances of one inductive, their type arguments and the fields
  of each constructor both ways, as Stage 4 converts such a value field by
  field; for a cast between two inductives, every field of the
  constructors at the same position), and a `Box`: a type used at an
  `lcAny` position is linked to every type an `lcAny` value is used at that
  it can be (function types whose skeletons unify, instances of one
  inductive, or of two in a program that casts; the `lcAny` wildcard
  applies only there). A data type counts when some type reachable from it
  (its type arguments, the fields of its constructors) mentions a function
  type (`mayHoldFn`, a reachability with one visited set: linear also on a
  dense mutual block, `RtErasedDenseMutual`), not only when its own type
  mentions one: `Op3 p.α` with `run : α → Nat → Nat` (tests
  `RtErasedFieldFlow`, `RtErasedFieldFlowBox`, `RtErasedFieldFlowProof`). A
  `cases` or projection on a `Box` unboxes it at the inductive's uniform
  instance first. An `initialize` constant's cell has the type the lowering
  gives it, and the initializer's result is linked to it. The marks are
  closed over the edges (several steps), and over the types after some
  arguments. An unknown type counts as `lcAny`. A value
  that completes at an `lcAny` parameter of uniform code (the lambdas of
  `Id.instMonad`, common) thus keeps no domain unless it reaches an erased
  one (`RtErasedAnyFlow`: `mkK p β b : p.α → β` with `p.α := Type`, seen
  at `Type → Nat → Nat`). Measured: `TypeclassGeneric` 0 skeletons kept of
  23, `RtFnValues` 0 of 21, `RtUniformFnTypes` 0 of 6, `RtDictConst` 0 of
  9, `HigherOrder` 0 of 4, the site's example 0 of 1. `L2R_DEBUG` prints
  these counts; `L2R_DEBUG_RULE4` the marks, edges and boxed types.

  The Lean positions are used where they matter: `applyLean` applies Lean
  arguments along the type (a phantom domain drops its `◾`; a `Box` callee
  is applied as `Box → Box`, which has a domain for every Lean argument);
  `genApply` matches a `p<j>` variant's arguments with its target's Lean
  parameters from `j` (an argument at a parameter the target does not take
  is dropped; a phantom domain gives a placeholder where the target takes
  the parameter), and a `w<S>` variant passes `◾` to `S` at its own type's
  phantom domains; `tryCoerce` needs no conversion at a phantom domain;
  `reprCompatible` takes a phantom domain as a unit one. The types with
  one run-time type share one `l2r_ap<j>_T`, so its parameters have
  run-time types (`Ty.rt`: no phantom domain at any depth). Each arm takes
  an argument at the domain of its variant's own type (the target's type
  for `p<j>`, `dst` for `w<S>`), not at the parameter's run-time type: the
  two are one Reussir type, but a function type in the domain keeps its
  phantom domains (`f : (α : Type) → α → α` is `◾ → Box → Box`), and the
  conversion from the run-time type `Box → Box` wrapped the argument as a
  function whose `◾` is an argument, so the target applied `box(0)` for
  the value (hunt 3; test `RtApplyPhantomParam`).
- **Why:** `◾` carries no information, and the run-time types are those
  of the dependent-types design (`ops_lam(xs)`). Removing a domain must not
  move the point where a body runs (Lean runs a body when its last
  parameter is applied): a value that completes at a phantom domain would
  run at the next argument instead, once per application instead of once
  (map C hazards H3, H4). A function type is built from its codomain's, so
  the decision can depend only on the type from the domain on; a decision
  by skeleton makes `Nat → …` and `lcAny → …` types agree, so their
  wrappers line up (H5). Uniform code applies a boxed function to a type
  argument's `box(0)` like data: the wrapper that views a value as
  `Box → Box` knows its phantom domains (H5). The flow keeps the units
  where they are needed only: a decision by skeleton alone (an `lcAny`
  parameter matching an erased domain everywhere) kept every erased domain
  of most programs.
- **Where:** `ErasedDomains.lean`: `Skel`, `skelOf`, `Skel.unify`,
  `keptErasedHead`, `flowAnalysis` (`flowCode`, `flowLink`,
  `flowLinkFields`, `flowFieldUses`, `mayHoldFn`, `flowThroughBoxes`,
  `reachedMarks`, `layoutFieldTypes`, `keyTy`);
  `LowerBase.lean`: `lowerType`, `LowerCtx.erased`,
  `LowerState.keptErasedOf` (the decisions, cached), `FnTarget` (`keep`,
  `ty`), `FnVariant`; `RR.lean`: `Ty.phantom`, `Ty.rt`, `fnTypeName`;
  `Lower/FnValues.lean`: `addFnVariant`, `applyCall`, `partTy`,
  `partValue`, `rawFnValue`; `Lower/Decls.lean`: `applyLean`;
  `Lower/Finish.lean`: `genApply`, `genFnConv`, `reprCompatible`,
  `fnTypeItems`, `runtimeDomWithin`; `Lower/Conv.lean`: `tryCoerce`;
  `Lower/LazyGlue.lean`: `lazyExternGlue` (a task function whose domain is
  phantom); tests `RtErasedEarly`, `RtErasedUniform`, `RtErasedOps`,
  `RtErasedTypeOnly`, `RtErasedAnyFlow`, `RtErasedFieldFlow*`,
  `RtApplyPhantomParam`.
- **Remove only if:** never (it is rule 4 of the dependent-types design).
  `layoutFieldTypes` must give the field types of the layout the lowering
  uses (rule 1's: a type parameter's field is `lcAny` and a field
  mentioning a parameter has it at `lcAny`, as `nominalType`; a value read
  from such a field at a typed binder is an edge from the uniform field
  type, and one stored there an edge to it).

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
