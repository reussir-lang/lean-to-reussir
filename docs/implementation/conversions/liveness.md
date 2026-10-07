# Helpers for live code only (`conv-liveness`)

The helpers Stage 4 generates at the end match variants: an unboxing
function (`l2r_unbox_…`) has an arm per `Box` variant that can hold a value
of its type, an application function (`l2r_ap<j>_…`) an arm per variant of
its function type, a conversion of function values (`l2r_fconv_S_T`) an
arm per wrapped representation of its source. Each arm converts, which
can request more helpers and register more variants. The optional pass
`conv-liveness` (on by default) generates them for live code only. Paths
are relative to `lean2rr/LeanToReussir/`. Plan
[§5.1](../../translation-plan.md#51-type-translation) ("The uniform type
`Box`") and [§5.3](../../translation-plan.md#53-closures-function-values).

### Helpers are generated only for what live code reaches

- **What:** A type-based reachability (rapid type analysis), computed
  while the helpers are generated. Live code is what the roots reach
  through calls. A function reached is looked at: the functions it calls
  and the identifiers of its atoms are reached, and the variants of `Box`
  and of function-value enums that it builds are *made*. A helper is
  generated only once it is reached, with arms only for made variants
  (an application function keeps `z` and `raw`; an unboxing function keeps
  the boxed-unit arm), and again when a variant it matches is made. The
  bodies generated are looked at in turn, until nothing changes.
  Example: an initializer registers a closure `p0_f` of type
  `Nat → Nat` (it is made), but no live code applies a `Nat → Nat`: no
  `l2r_ap1_…` for it is generated, so `f` is reached only if something
  else calls it. A `Box` variant for `Option String` that only dead code
  boxes gets no arm in `l2r_unbox_T_Option_…`, so the conversion that arm
  would call is never generated.
- **Why:** Without it every helper requested anywhere is generated, with
  an arm for every variant registered anywhere. In a program that can cast
  (one `unsafe` implementation in any library it imports,
  `programCasts`), every unboxing function also gets a cast arm and a
  conversion for every payload of a compatible layout: the helpers grow
  quadratically. One layout per datatype (rule 1) removed the conversions
  between instantiations, but not these: a program importing `Cslib.Init`
  with a one-line `main` (deptypes-cleanup, 2026-10-06) has 226,219
  functions in 380 MB of `.rr` without the pass (111,414 `l2r_conv_…`
  casts between inductives, 10,991 `l2r_fconv_…`, 970 unboxing and 2,242
  application functions) and 28,300 in 29 MB with it (1,636, 661, 80 and
  43), at a peak of 5.7 GB and 5.1 GB. Smaller programs lose about 4 % of
  their functions to it (`RtCastFnWrapLive` 1140 → 1096, `RtPolyRecResult`
  1246 → 1172). Before rule 1 the same program had 990,927 functions in
  1.44 GB without the pass (704,425 `l2r_conv_…`) and 30,418 with it, and
  a program importing `Batteries` 162,096 (180 MB) and 10,743 (10 MB). A
  synthetic program that boxes K structures of one shape and reads each
  back keeps its K² cast arms: every payload is made and every unboxing
  function live, which a type-based analysis cannot tell apart from casts
  (perf-stage3 investigation, 2026-10-04).
- **Where:** `Lower/Live.lean`: `liveFollow` (the scan), `LiveState.add`,
  `exprRefs`/`blockRefs`/`textRefs` (what a body or text refers to),
  `liveSkipBox`/`liveSkipFn` (the arms left out), `liveVersion`;
  `Lower/Finish.lean`: `finishLive` (the fixpoint), `genUnbox`,
  `genApply`, `genFnConv`;
  `Emit/Program.lean`: `lowerProgram`; `LowerBase.lean`: `LiveState`,
  `LiveHelper`; `Opt/ConvLiveness.lean`.
- **Remove only if:** the pass is off (`--disable-opt conv-liveness`):
  every helper requested is generated with every arm. A removed arm
  matches a variant no running code builds, so the program computes the
  same results either way; the one other difference is at translation
  time (an extern that only a removed arm would call is not reported, see
  below).

### The roots are the identifiers of raw text and of the prelude

- **What:** Every identifier of a raw item (the entry point and the
  startup chain, which call `main`, the initializers and the constants;
  the trampolines the runtime calls: `l2r_init_body`, `l2r_main_body`,
  `l2r_stderr_put`, `l2r_task_run_one`, `l2r_task_walk`,
  `l2r_promise_drop`; the conversion counter) and of the prelude is a
  name reached. So are the identifiers of every atom of a function reached
  (`Lower/Process` renders expressions into atoms), and every `T::v` of
  `Box` or of a function-value enum that text names counts as made.
  Variables are never names: lean2rr refers to functions only by calls.
- **Why:** The runtime calls generated code only through the trampolines,
  which are raw text, and builds no `Box` or function value of its own:
  the payloads of `Box` that a program boxes and the `L2RFn_…` enums
  exist only in the generated program (a box construction names its
  payload number: `l2r_any_of<T>(x, n)`),
  the prelude's generic functions move values (cells, references, once
  cells, tasks handed back by address) but never build a variant, and
  `l2r_retype` never reinterprets a `Box` or a function value
  (`retypable`). Taking every identifier of text as a name keeps whatever
  text mentions.
- **Where:** `Lower/Live.lean`: `liveFollow` (raw items), `liveRootText`
  (the prelude, from `Emit/Program.lean`), `textRefs`.
- **Remove only if:** never, while the pass exists: a construction or call
  that the scan misses would lose an arm or a function.

### An application function with variants left out ends in a wildcard

- **What:** When `conv-liveness` leaves variants out of `l2r_ap<j>_T`, its
  match ends in `_ => l2r_unreachable`, whose arguments are released out
  of line first (`l2r_sink<T>(a)` for every argument that is not a
  scalar or unit). The unboxing functions and the conversions of function
  values already end in a wildcard.
- **Why:** Reussir rejects a match that is not exhaustive. rrc copies the
  wildcard into every variant it covers and would release each argument
  in line there, a match over its type's variants (`Box` has one per boxed
  type: issue 22's shape, a cost).
- **Where:** `Lower/Finish.lean`: `genApply` (`skipped`).
- **Remove only if:** the pass is off.

### A helper of a function type is generated again when its type gains a variant

- **What:** A live application function (`l2r_ap<j>_T`) or conversion of
  function values is generated again when its function type gains a
  registered variant, built or not: its version (`liveVersion`) is the
  number of made variants plus the number of registered ones (both only
  grow). The new body has the arm, or the wildcard, for that variant.
- **Why:** A conversion that `tryCoerce` only tries registers its wrapper
  without building it: converting `Nat → (Box → Box)` to
  `Nat → (String → String)` tries the codomain's conversion, which
  registers the wrapper variant of `String → String`. When this happened
  among the helpers, after `l2r_ap1` of `String → String` was generated,
  that function had neither an arm nor the wildcard for a variant its enum
  has, and rrc rejected the match ("non-exhaustive patterns in match").
  The calls that Lean's `cse` merges across types made this reachable
  (test `RtCseUniform`, `cod`: an `Option (Nat → α → α)` made at the
  instance at `lcAny`, read at `Nat` and at `String`).
- **Where:** `Lower/Live.lean`: `liveVersion`; `Lower/Finish.lean`:
  `finishLive`, `genApply`.
- **Remove only if:** the pass is off, or `tryCoerce` stops registering
  the wrappers of conversions it only tries.

### Functions nothing reaches are dropped; the enums keep every variant

- **What:** After the last helper, the functions not reached are dropped
  (`liveDrop`), and the enums of function types are those the kept
  functions, the types and the `Box` variants mention (`fnTypeItems`, run
  after the drop). The `Box` enum and every function-value enum keep all
  the variants registered, built or not, and every type item stays. The
  missing-extern check sees the functions before the drop, so a program
  is refused as before, except for an extern that only an arm left out
  would have called (a function value of an extern that no live code
  builds): that arm is never generated, so the extern is not reported.
- **Why:** Dropping only arms and functions keeps the types consistent
  without a second analysis: a variant nothing builds costs nothing at
  run time. Dropping declarations before lowering hardly helps, since the
  waste is in the helpers.
- **Where:** `Lower/Live.lean`: `liveDrop`; `Emit/Program.lean`:
  `lowerProgram`; `LowerBase.lean`: `dropFns` (keeps the scan's position
  in step when the persist walks are regenerated).
- **Remove only if:** the pass is off.

### The functions generated after the helpers follow them

- **What:** The diagnostics writer (`l2r_stderr_put`), the stream
  contexts (`l2r_std_enter`/`leave`) and the task dispatch
  (`l2r_task_run_one` & co.) are generated once the helpers are, because
  they depend on whether the program has stream cells and on its task
  types. With `conv-liveness`, they are generated again (the same
  functions replaced; their trampolines stay) whenever those change
  afterwards, until nothing changes.
- **Why:** A helper reached only from these functions (the task dispatch
  applies the tasks' closures) is generated only after them, and its arms
  can lower an extern that uses the standard streams or makes a task:
  without the plain translation's eager helpers, that use would come too
  late for them.
- **Where:** `Emit/Program.lean`: `lowerProgram` (`lateKey`).
- **Remove only if:** the pass is off (every helper is then generated
  before them).

### A cast's conversion does not depend on which helpers are live

- **What:** A cast through a `Box` whose conversion needs a function value
  at another representation registers the wrapper it needs, with or
  without the pass, so the cast converts whatever other code is live
  ([box-unboxing.md](box-unboxing.md#other-types-variants-only-in-a-program-that-can-cast)).
- **Why:** Such a cast used to be kept only when its wrapper was
  registered already. With the pass, dead code no longer registered
  wrappers and an unboxing function was generated again only when a
  variant was made, so a cast that converted without the pass panicked
  with it (review CLR-01: `RtCastFnWrapDead`, the wrapper registered only
  by dead code; `RtCastFnWrapLive`, by live code generated later;
  `RtCastFnWrapOrder`, the order that happened to work).
- **Where:** `Lower/Conv.lean`: `boxCastable`, `tryCoerce`;
  `Lower/Finish.lean`: `genUnbox`.
- **Remove only if:** never.
