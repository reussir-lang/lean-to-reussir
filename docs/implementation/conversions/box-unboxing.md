# Unboxing: what a `Box` may hold

Boxing wraps a value in its type's variant. Unboxing must accept every
variant that can hold a value of the target's Lean type, and, in a program
that casts, the variants of types an `unsafeCast` reads. Paths are relative
to `lean2rr/LeanToReussir/`. Plan
[§5.1](../../translation-plan.md#51-type-translation), "The uniform type
`Box`".

### An unboxing function accepts every representation of its Lean type

- **What:** Unboxing to a nominal type, an array, a thunk or task, a
  reference or a word type accepts that type's own variant only (one type
  per inductive, one per builtin generic type), besides the boxed-unit arm
  (the target's zero) and, in a program that casts, the cast arms below.
  The generated unboxing function to a function type accepts every
  compatible function representation (wrapped). Each function also has an
  `unreachable` arm.
- **Why:** A function type keeps one representation per lowered type
  (`Nat → Nat`, `Box → Box`), so a function value boxed at one is read at
  another. (Before arrays and cells had one representation each, an inner
  `Array.map` result boxed as `RVec<Box>` reached a consumer wanting
  `LNatArr`: F03, 829f20a; and thunks in `Box`: FN-03, D2.)
- **Where:** `Lower/Finish.lean`: `genUnbox` (one function; driven by
  `finishUnboxFns`, or by `finishLive` with `conv-liveness`, which leaves
  out the variants no live code builds: [liveness.md](liveness.md)),
  `reprCompatible`; `Lower/Conv.lean`: `tryCoerce`, `unboxMatch`.
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
- **Where:** `Lower/Conv.lean`: `boxCastable`, `tryCoerce`,
  `castFallback` (a pair `boxCastable` accepts converts, or fails before
  it registers a helper: the arm is then left out, with nothing to undo),
  `programCasts`; `Lower/Finish.lean`: `genUnbox`. The fact itself:
  [../types/uniform-types.md](../types/uniform-types.md#whether-the-program-can-cast-at-all-is-a-whole-program-fact).
- **Remove only if:** never. The casts left out panic (plan
  [§10](../../translation-plan.md#10-known-divergences-and-unsupported-features),
  "Casts that natively read an address").

### Unboxing keeps the target's own variant in line

- **What:** Unboxing to `Nat`, `Int`, `UInt8/16/32/64`, `Bool`, a float or
  a nominal type is in line (`boxUnbox`): the target's own payload, an
  immediate read at the target, and the boxed unit (the target's zero).
  Only in a program that casts (`programCasts`) do the other payloads go
  to the generated function (`l2r_unbox_T`: another word type or an
  object read through `unsafeCast`, the types a cast reads); otherwise
  they are `unreachable`, for a word type as for a nominal type.
- **Why:** Sending every word unboxing through the generated function cost
  rrc build time on uniform code (Cn3PolyS1: 123 s → 105 s, 2.1 → 1.7 GB;
  72b13f0). Without casts the generated function is the same match: one
  type per inductive, so only the target's own payload holds a value of
  it, and an immediate is read at the target whatever word type boxed it,
  as natively; out of line it was a call at every read of a generic
  field, and a copy of the in-line match (review of rule 1, simplicity
  finding 5: a word unboxing outside casting programs had kept an
  out-of-line function until the switch to the one-word box gated it).
- **Where:** `Lower/Conv.lean`: `unboxMatch` (`slow`), `tryCoerce`;
  `LowerBase.lean`: `boxUnbox`.
- **Remove only if:** never.

### The `unreachable` arm releases the `Box` out of line

- **What:** The fallback arm of every unboxing function, and of an in-line
  unboxing without a generated function, releases the `Box` through a
  call that consumes it (`boxSink`: `l2r_any_addr`; in line,
  `l2r_any_drop_raw` of the word) before panicking.
- **Why:** When `Box` was a shared enum, rrc expanded its release in line
  into a match over its variants, one per boxed type: each unboxing
  function, inlined wherever it is called, held such an expansion in its
  `unreachable` arm (ae5104d). The one-word box releases through its drop
  hook (one call), so the call costs the same as an in-line release now.
- **Where:** `LowerBase.lean`: `boxSink`, `boxUnbox`;
  `Lower/Finish.lean`: `genUnbox`. Related:
  [../reussir-workarounds/build-time.md](../reussir-workarounds/build-time.md#issue-22-cost-a-wildcard-arm-over-a-wide-enum-costs-n3-code).
- **Remove only if:** any time (the one-word box): an in-line release of
  the box is one call too.
