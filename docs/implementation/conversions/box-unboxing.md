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
  immediate read at the target (in a program that casts, as native Lean
  reads that word:
  [../representations/box-and-uniform.md](../representations/box-and-uniform.md#in-a-program-that-casts-an-immediate-is-read-as-native-lean-reads-its-word)),
  and the boxed unit (the target's zero).
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

### At a program payload type, only the pointer test stays in line

- **What:** An unboxing at a program payload type (a nominal type, an
  array of a program type, a reference, a closure record: `BoxKind.prog`,
  not a function type) keeps in line only the common case: the box's word
  is a pointer of the type's own number (`l2r_any_raw_is_num(w, n)`, one
  masked compare once LLVM folds it), and the payload is taken
  (`l2r_any_raw_take`). Anything else (an immediate: a nullary variant by
  index, `box(0)` as the zero; another number: unreachable, or in a
  program that casts the cast function) is a call of a function generated
  once per type and kind, which takes the word (`boxUnboxWith`,
  `ownUnboxName`): `l2r_unbox_rest_T(w)`, `l2r_unbox_rest_T_n` (the
  immediates read as natively, in the generated cast function itself,
  `genUnbox`) and `l2r_unbox_rest_T_c` (in a program that casts: anything
  else goes to `l2r_unbox_T`). Its body is the in-line match it replaces,
  minus the pointer test. The functions are kept out of rrc's MLIR inliner
  (`#[transform_anchor]`, `anchoredFns`); LLVM inlines the small ones (an
  enumeration's immediates). A round trip (unboxed and boxed again at once)
  is still folded into the box (`boxUnboxed?`: the block starts with the
  word). The field of a `[value]` struct over a program type takes the
  same form, except in a program that casts, where its fallback is the
  struct's cast function (all in line). `tests/runtime/rr-fingerprint.py`
  counts the functions and their uses as `unbox-fns` and `unbox-sites`,
  not as conversion helpers.
- **Why:** The in-line match is about 17 lines, and there were 2087 sites
  in the benchmark set (2.48 MB, 7.1 % of the `.rr` text) for 338 distinct
  (program, type) pairs; rrc's build time grows with the code it compiles.
  The whole unboxing as one called function was smaller still, but LLVM
  did not inline it where the type's zero is a cached placeholder (a
  record's `box(0)`: the once-cell's code made the function too big), so
  the loops of liasolver over arrays of records called it at every
  element. With the pointer test in line, the remaining calls are on the
  paths of `box(0)` and of errors only (L10's IR: the pointer test of all
  87 sites in line, one masked compare; 35 calls left, all on those
  paths). `.rr` text after `unread-consts`: the 50 distinct files of the
  benchmark set 22.9 → 21.4 MB (−6.6 %), RtIO −13 %, L10 −12 %, cedar −8 %,
  lean-zip −8 %, lean-regex −5 %. rrc's peak memory −1 to −2 % (cedar
  2.37 → 2.34 GB, lean-zip 0.75 → 0.73 GB); its time changed within the
  noise of a loaded machine (lean-zip 36 → 32 s, cedar 100 → 111 s with a
  warm texture cache).
- **Where:** `LowerBase.lean`: `ownUnboxName`, `boxUnboxWith` (`.prog`,
  `outline`, `slowKey`), `boxUnbox`, `LowerState.ownUnboxFns`;
  `Lower/Finish.lean`: `anchoredFns`; `runtime/prelude.rr`:
  `l2r_any_raw_is_num`.
- **Remove only if:** rrc's cost per line of code drops enough that the
  copies cost nothing.

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
  [../reussir-workarounds/build-time.md](../reussir-workarounds/build-time.md#old-issue-22-cost-a-wildcard-arm-over-a-wide-enum-cost-n3-code).
- **Remove only if:** any time (the one-word box): an in-line release of
  the box is one call too.
