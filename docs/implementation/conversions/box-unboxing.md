# Unboxing: what a `Box` may hold

Boxing wraps a value in its type's variant. Unboxing must accept every
variant that can hold a value of the target's Lean type, and, in a program
that casts, the variants of types an `unsafeCast` reads. Paths are relative
to `lean2rr/LeanToReussir/`. Plan
[§5.1](../../translation-plan.md#51-type-translation), "The uniform type
`Box`".

### An unboxing function accepts every representation of its Lean type

- **What:** The generated unboxing function to a nominal type matches the
  `Box` variants of every instantiation of the same inductive and converts
  them structurally; to an array type, every array representation with
  compatible elements; to a thunk or task, every cell of the same kind
  with compatible values; to a function type, every compatible function
  representation (wrapped). Arrays of another representation go through
  `RVec<Box>` (boxing each element, then unboxing it). Each function also
  has the boxed-unit arm (the target's zero) and an `unreachable` arm.
- **Why:** An inner `Array.map` result is boxed as `RVec<Box>` while its
  consumer wants `LNatArr` (nested `Array.map` → "INTERNAL PANIC", F03,
  829f20a); thunks and arrays of thunks in `Box` (FN-03, D2; 1fcb07f,
  0cba3ff). Going through `RVec<Box>` keeps the number of conversions
  linear in the number of array types, not quadratic (nested arrays under
  polymorphic recursion have many representations).
- **Where:** `Lower/Finish.lean`: `genUnbox` (one function; driven by
  `finishUnboxFns`, or by `finishLive` with `conv-liveness`, which leaves
  out the variants no live code builds: [liveness.md](liveness.md)),
  `reprCompatible`, `monoCompatible`; `Lower/Conv.lean`: `tryCoerce`.
- **Remove only if:** never.

### Other types' variants only in a program that can cast

- **What:** Besides its own Lean type, an unboxing function accepts the
  variants of types an `unsafeCast` can read (a `[value]` struct as its
  field, `UInt64`/`Float` bits, words, isomorphic inductives) only when
  `LowerCtx.programCasts` holds. Even then, a cast between inductives that
  do not correspond constructor for constructor stays unreachable in a
  `Box` arm (typed code converts it). A cast whose conversion needs a
  function value at another representation converts through a wrapper, as
  any conversion does: it used to be kept only when the wrapper was
  registered already, so whether it converted depended on the order in
  which helpers were generated and, with `conv-liveness`, on which were
  live (review CLR-01; tests `RtCastFnWrapDead`, `RtCastFnWrapLive`,
  `RtCastFnWrapOrder`). The wrappers stay finite: a wrapper is a variant
  `w<S>` of function type `T`, both types the program has, so there are
  at most F² wrappers and conversions for F function types.
- **Why:** Matching every castable type made each unboxing function match
  every type with function fields at the same slots (the dictionaries of
  uniform code), each wrapper adding arms to application functions:
  programs over monad transformer towers grew by a fifth (e8feb4a), which
  is why wrapper casts were once kept only when the wrapper existed (an
  order-dependent result, dropped for CLR-01; with `conv-liveness` only
  live unboxing functions and built variants get arms).
  Accepting inductives with other constructor counts added 3-5% of code
  for casts that hardly ever occur (18fb171). Outside casting programs,
  same-shape boxed types made unboxing quadratic (TY6-02, 5be764c).
- **Where:** `Lower/Conv.lean`: `boxCastable`, `boxCastConv` (probes, and
  rolls back a cast that has no conversion, cutting the emitted functions
  and types back to their sizes:
  [../translator.md](../translator.md#stage-4-finds-emitted-functions-by-name-and-keeps-its-emitted-items-unshared)),
  `programCasts`; `Lower/Finish.lean`: `boxCastCompatible`,
  `genUnbox`. The fact itself:
  [../types/uniform-types.md](../types/uniform-types.md#whether-the-program-can-cast-at-all-is-a-whole-program-fact).
- **Remove only if:** never. The casts left out panic (plan
  [§10](../../translation-plan.md#10-known-divergences-and-unsupported-features),
  "Casts that natively read an address").

### Instantiations that cannot be the target go through a shared one

- **What:** In a program that does not cast, a `Box` variant of another
  instantiation of the target's inductive whose Lean type cannot be the
  target's (`Option Nat` read as `Option String`) is converted through the
  instantiation at the arguments both share, `lcAny` elsewhere
  (`Prod (Array S₁) Nat` read as `Prod (Array S₀) Nat` goes through
  `Prod lcAny Nat`).
- **Why:** Only a value `cse` shared between the two types (`none`,
  `some []`) reaches such an arm. Converting directly, K same-shape
  structures through uniform code made K² conversion functions, each with
  its own generic runtime calls (build time quadratic; round 6 TY6-02,
  5be764c). The arms stay quadratic, but each is a call (Ty6QS80: 200 s,
  157 s without them; most of the rest, 100 s, is one rustc run per
  generic runtime function instantiated at a type, RV6T-03).
- **Where:** `Lower/Finish.lean`: `genUnbox` (`viaShared`).
- **Remove only if:** the build cost is no longer a concern; the result is
  the same either way.

### Unboxing to a word type keeps its own variant in line

- **What:** Unboxing to `Nat`, `Int`, `UInt8/16/32/64`, `Bool` or a float
  is an in-line match on the target's own variant (and the boxed unit),
  with the other variants (another word type read through `unsafeCast`)
  sent to the generated function.
- **Why:** Sending every word unboxing through the generated function cost
  rrc build time on uniform code (Cn3PolyS1: 123 s → 105 s, 2.1 → 1.7 GB;
  72b13f0).
- **Where:** `Lower/Conv.lean`: `unboxMatch` (`slow`), `tryCoerce`.
- **Remove only if:** never.

### The `unreachable` arm releases the `Box` out of line

- **What:** The fallback arm of every unboxing function releases the `Box`
  through `l2r_ptr_addr_rec` (a call that consumes it) before panicking.
- **Why:** rrc expands every release of an enum in line into a match over
  its variants, and `Box` has one per boxed type: each unboxing function,
  inlined wherever it is called, held such an expansion in its
  `unreachable` arm (ae5104d).
- **Where:** `Lower/Finish.lean`: `boxSink`, `genUnbox`. Related:
  [../reussir-workarounds/build-time.md](../reussir-workarounds/build-time.md#issue-22-cost-a-wildcard-arm-over-a-wide-enum-costs-n3-code).
- **Remove only if:** rrc releases wide enums out of line itself.
