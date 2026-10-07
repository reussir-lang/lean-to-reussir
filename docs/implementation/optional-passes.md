# Optional passes

Every optimization is a module of `lean2rr/LeanToReussir/Opt/` registered by
one line in `Opt/Registry.lean` (`optimizations`), and all are on by
default. `lean2rr --list-opts` prints the registry; `--disable-opt NAME`
(or `L2R_DISABLE_OPTS=a,b` for `scripts/l2r.py`) turns one off for a run.
The core translation is correct with all of them off. No pass is switched
per program or benchmark: each restricts itself only through checks it
makes automatically on every program, the "guard" column: what soundness
requires, and for some passes bounds on code size or translation work, or
the shapes where the pass applies at all. Plan
[§1](../translation-plan.md#code-structure-and-passes) ("Code structure
and passes").

## The passes, in installation order

| Pass | What it does | Guard (soundness; other limits) | Details |
|---|---|---|---|
| `field-order` | record fields by decreasing alignment, no padding | none needed: every access goes through the constructor layout | [records](representations/records.md#fields-are-ordered-by-decreasing-alignment) |
| `value-structs` | a structure with one relevant field is a `[value]` struct | not when the field's type is being translated (no type contains itself by value) | [records](representations/records.md#one-field-structures-are-value-structs) |
| `placeholder-cache` | placeholders that would allocate built once, in a once-cell | only heap placeholders; a placeholder is never inspected | [placeholders](representations/placeholders.md#placeholders-that-allocate-are-built-once) |
| `boxed-consts` | a constant whose boxing allocates boxed once, in a once-cell (native Lean's `_boxed_const`) | only a variable bound to a declaration without parameters that runs once (cached) or cannot trace or panic (`cheap-consts`) and whose value is not a literal that boxes as an immediate (`constIsImmediate`), or to a `UInt64` literal from 2^63, at a type whose boxing can allocate (`boxAllocates`), outside the body of a declaration without parameters (`inConstBody`: it runs once); a constant is pure, so one box does as well as a new one | below |
| `float-lits` | float literals folded to their bits at compile time | literal arguments only (the functions are pure and total): a `let` of a literal, a `Bool` discriminant inside an alternative that fixes it, a join point parameter to which every jump passes the same literal; work bound: exponent ≤ 2000, mantissa (or `Float.ofNat`'s argument) at most 4096 bits | below |
| `cheap-consts` | constants of small literals recomputed at each use | `isCheapConst`: unboxed types only, every `Nat`/`Int` small (`Nat` literals and `Nat.succ` < 2^63, `Int.ofNat`/`Int.negSucc` of `int32` values), other constructors, total scalar conversions, other cheap constants; no strings | below |
| `prelude-repr` | `Nat.repr`/`Int.repr` by the runtime's GMP code | none needed: the same strings (unary calls only) | [nat-int](representations/nat-int.md#natrepr-of-0127-shares-one-string-per-number) |
| `jp-sink` | join points moved to the smallest code containing their jumps | moves only, never duplicates; binders are unique | [join points](control-flow/join-points.md#join-points-are-sunk-before-the-choice-jp-sink) |
| `jp-small` | small join points duplicated at their jumps (J1′) | none needed for soundness (a copy runs the same code once per path); code-size bounds: own body ≤ 40, a copy ≤ 480 (join points jumped to once counted at full size), extra copies ≤ 2000 (4000 for a loop's continuation); never a J2 join point | [join points](control-flow/join-points.md#small-join-points-are-duplicated-within-three-bounds-jp-small) |
| `state-machines` | J4 entered without allocation: every variant nullary, values passed in parameter slots | a jump passes placeholders in the slots it does not fill, never live values; a type without a finite placeholder (`zeroFinite`) gets no slot | [state machines](control-flow/state-machines.md#state-machines-entered-without-allocation-state-machines) |
| `lazy-fields` | fields of a live matched value bound where used | shared values matched at their own type; variables another hook bound again are left alone; applies only where the value is stored, returned or passed whole | [cases](control-flow/cases.md#fields-of-a-live-matched-value-are-bound-where-they-are-used-lazy-fields) |
| `nullary-scrutinee` | in a field-less arm, the matched value rebuilt | only arms of constructors without fields that use the value | [cases](control-flow/cases.md#the-matched-value-of-a-nullary-arm-is-rebuilt-nullary-scrutinee) |
| `sink-proj` | structure projections sunk into the branches that use them | the projection is unused later in the block and in the condition, and no binder clashes; applies only where some branches use it while another keeps the structure whole | [cases](control-flow/cases.md#structure-projections-move-into-the-branches-that-use-them-sink-proj) |
| `fresh-rebuild` | an arm returning a fresh matched value returns it rebuilt | the value is freshly built (whole-program analysis); the arm binds every field and only returns it | [cases](control-flow/cases.md#fresh-values-returned-whole-are-rebuilt-fresh-rebuild) |
| `conv-liveness` | unboxing, application and conversion helpers generated only for what live code reaches; unreachable functions dropped | none needed for soundness: an arm left out matches a variant that no live code builds, so no value of it exists at run time; every identifier of raw text, of the prelude and of atoms is a root, every arm of other matches counts, and a variant that text names counts as built | [liveness](conversions/liveness.md) |
| `merge-fns` | generated functions equal up to their own and local names merged: a copy calls the first, calls of a copy call the first | the canonical texts are equal (the same code once names are renamed in binding order, inside atoms too); a copy keeps its name and calls the function its first ends at, never itself; nothing is removed; a function called from one place only stays (LLVM inlines it there), except startup code (`_init`, `l2r_persist_`) | below |

### Functions equal up to names are merged (`merge-fns`)

- **What:** After the other passes over the generated functions, each
  function gets a canonical text: its own name `SELF`, its local names
  (parameters, `let`s, match binders, lambda parameters, and those names in
  atoms) renamed `v0`, `v1`, ... in binding order. Of the functions with one
  text, the first stays; each other one keeps its name and signature and
  its body becomes a call of the first (`fn f(a, b) -> T { g(a, b) }`), and
  every call of it in a function body calls the first. Functions whose
  calls changed are looked at again, so callers merge in the next round
  (`List.reverse` at each type once `List.reverseAux` is), up to 8 rounds.
  A function that is a first already but changes later keeps the
  functions merged into it: its new body computes what the old one did.
  A copy calls the function its first ends at, never itself (two functions
  could otherwise call each other). A function that one place calls
  (besides its own recursive calls) takes no part: LLVM inlines such a
  function into its caller, and merged it would be one function that
  several places call, which LLVM does not inline (mergesort's six
  `splitHalf.go` instances, each inlined into its `mergeSort`, cost
  +2.3 % instructions merged); startup code merges anyway: a constant's
  computation (`_init`) and the persist walks (`l2r_persist_`).
- **Why:** With one layout per inductive, instances of a definition at
  different types are often the same code: `List.reverseAux` at `String`,
  `Nat` and a structure (since the heads pass their boxes on,
  [box-and-uniform.md](representations/box-and-uniform.md#a-value-that-only-goes-back-into-boxes-keeps-its-box)),
  `List.lengthTRAux`, the persist walks of function types that differ
  only in phantom domains. CslInitOnly: `.rr` 32.0 -> 30.7 MB (-4.1 %;
  -6.6 % when functions called from one place merge too), for about 1 %
  more translation time (the functions are bucketed by a hash of their
  canonical form, `canonHash`, which hashes types as rendered, `Ty.rt`;
  texts are built only within a bucket).
- **Where:** `Opt/MergeFns.lean`: `mergeFns` (`keep`), `countCalls`,
  `canonHash`, `canonText`, `renameCalls`; hook `PassConfig.rrPasses`
  (last). Test `RtMergeFns`.
- **Remove only if:** the pass is off (the copies stay whole).

### Constants are boxed once (`boxed-consts`)

- **What:** When a variable bound to a constant is boxed (`boxOf`, the
  box branch of `tryCoerce`), and boxing its type can allocate
  (`boxAllocates`: a `Float`, a `UInt64` or `i64` word, a `[value]`
  struct of one, a value in an `ElemBox`; not an immediate: `UInt8`…
  `UInt32`, `Char`, `Bool`, `Float32`, an enumeration, Lean's `Int8`…
  `Int32`, which Lean erases to `UInt8`…`UInt32`), the box is built
  once and kept in a once-cell, the accessor `l2r_boxed_N` (`boxedConst`;
  one per constant and type, `cafAccessor` without the walk for tasks). A
  constant is a declaration of the program without parameters (a
  constant or closed term cached in a once-cell, or one `cheap-consts`
  recomputes, which cannot trace or panic; not a closed term evaluated
  where it is used, `uncachedConsts`, which a second call would run
  again; not a constant whose value is a literal that boxes as an
  immediate, `constIsImmediate`: `def k : UInt64 := 77` is boxed in line,
  which LLVM folds, where a once-cell read is a load, a test and a copy)
  or a `UInt64`/`USize` literal from 2^63; `lowerCode` records the
  variables bound to one (`closedLetValue`, `LowerState.closedLets`). Not
  in the body of a declaration without parameters (`inConstBody`, set by
  `lowerDecl`): that body runs once, so a once-cell there saves no
  allocation and costs a slot and two functions per constant (a table
  constant of 600 distinct big `UInt64` literals went from 1159 to 2359
  functions).
- **Why:** Native Lean does the same (`ExplicitBoxing`,
  `isExpensiveConstantValueBoxing`: an auxiliary constant
  `_boxed_const_N`). The default of `a[i]!` is a constant
  (`instInhabitedFloat`, a structure's `Inhabited` instance); boxed at
  every read, an `Array Float` read allocated a 16-byte cell per read
  (adversarial review of the dependent-type branch, finding 2: 4 × 40000
  reads, 160046 allocations, natively 11079 with its startup's 11000; with
  the pass 47). A named constant or closed term, or a `UInt64` literal
  from 2^63, pushed or stored n times is one cell, as natively. A `Float`
  literal written in a loop (`a.push 0.25`) is no constant: it is
  computed there, natively too (Lean extracts no closed term for it), and
  boxed at each push on both sides. A constant is pure, so one box does
  as well as a new one; two boxings of one constant are one cell
  (`ptrEq`), as natively within one module (native Lean caches its boxed
  constants per module, `cacheAuxDecl`; lean2rr has one cell per constant
  for the whole program; plan §9, identity). Test `RtDepFloatArrayAlloc` (`.alloc`: `get!`,
  `getD`, `modify`, `set!`, a structure's default, constants and literals
  pushed, at two sizes). A closed term
  evaluated where it is used (`uncachedConsts`) is left out: the box's
  call ran it a second time, and a trace in it printed twice (test
  `RtDepBoxedClosedOnce`).
- **Where:** `Lower/Conv.lean`: `boxOf`, `boxedConst`; `Lower/Code.lean`:
  `closedLetValue`, `constIsImmediate`, the `let` loop of `lowerCode`,
  `lowerDecl`; `LowerBase.lean`: `boxAllocates`, `LowerState.closedLets`,
  `boxedConstFns`, `inConstBody`, `LowerCtx.boxedConsts`;
  `Opt/BoxedConsts.lean`.
- **Remove only if:** the pass is off (each box of a constant is built
  where it is used).

### Float literals are folded to their bits (`float-lits`)

- **What:** A call `Float.ofScientific m s e`, `Float.ofNat n` (or the
  `Float32` ones) on literal arguments is evaluated by lean2rr, with the
  same Lean functions, and replaced by `Float.ofBits` of the bit pattern, a
  total conversion of a literal. Calls with an exponent above 2000 or a
  mantissa (or `Float.ofNat` argument) of more than 4096 bits are left to
  run. An argument is a literal when its variable is one of these:
  - bound by a `let` to a literal (`10`, `Bool.true`);
  - the discriminant of a `cases` on `Bool`, inside an alternative that
    fixes its value: `Bool.true`, `Bool.false`, or a `.default`
    alternative when the other alternatives name exactly one constructor
    (`boolOfAlt?`; Lean's simp leaves no such `.default` today, because
    two equal alternatives remove the `cases`);
  - a parameter of a join point, when every jump to the join point passes
    the same literal at that parameter (`JumpLits`).

  Example. In `match b with | true => x * 2.5 | false => x * 3e2`, the
  literal `2.5` is `Float.ofScientific 25 true 1`. Inside the alternative
  `true` of `cases b`, Lean's simp replaces the constructor `Bool.true` by
  `b` (`Simp.simpCtorDiscr?`: a constructor equal to a discriminant there
  becomes the discriminant). So the mono code has
  `Float.ofScientific 25 b 1`. The pass knows that `b` is `true` in this
  alternative, and folds the call. In the alternative `false`, `3e2`
  (`Float.ofScientific 3 false 2`) becomes `Float.ofScientific 3 b 2` in
  the same way. If `Simp.simpJpCases?` then moves such an alternative into
  a join point of its own, `b` becomes that join point's parameter. In
  `if x && y then a + 0.5 else a * 2e3`, the `else` code is a join point.
  One jump passes `x` from the alternative `false` of `cases x`, the other
  passes `y` from the alternative `false` of `cases y`. Both are `false`,
  so the parameter is `false`, and `2e3` folds.
- **Why:** These are Lean functions, not C: the slow path goes through
  `Float.Model` with bignum arithmetic. lean2rr is compiled from the same
  `Init` code, so the bits are Lean's, subnormals and rounding included
  (adv3 CN3-01, d3e80aa; test `RtFloatLits`). After simp's replacement, a
  literal is no longer a closed term, so it is computed at each iteration
  of a loop (natively too), and a slow-path literal allocates there. The
  discriminant and join point rules fold these calls (test
  `RtFloatLitDiscr`; its `.alloc` file checks that lean2rr's allocations
  do not grow with N). They are sound: an alternative runs only when the discriminant
  has that value. A join point's body runs only after a jump to it, and
  every jump is in its continuation: a join point is not recursive, and a
  jump does not leave its function (LCNF's checker).
  Simp replaces only constructor applications. The `Nat` arguments of
  float literals are raw literals (`.lit`), not constructors, and mono code
  has no `cases` on `Nat`. So simp hides no `Nat` literal argument, except
  an explicit `Nat.zero` inside the alternative `Nat.zero` of a base-phase
  `cases` (the call then runs, with the same result).
  Not folded: a flag that is a parameter of a function, for example in a
  specialization of `List.map` for a closure that captured `b`
  (`if b then xs.map (· + 0.5) else …`). That call runs, as natively.
- **Where:** `Opt/FloatLits.lean`: `foldFloatLitsCore`, `boolOfAlt?`,
  `JumpLits`, `floatLitBits?`, `floatLitMaxExp`, `floatLitMaxBits`; hook
  `PassConfig.monoPasses`.
- **Remove only if:** the pass is off (the program computes the same bits
  at run time).

### Cheap constants are recomputed (`cheap-consts`)

- **What:** A constant whose code only builds unboxed values from small
  literals, constructors and total scalar conversions (`UInt32.ofNat 0`,
  `Float.ofBits`, or another such constant, up to 8 deep) is recomputed at
  every use instead of read from a once-cell. Every `Nat`/`Int` it builds
  must be small (one word): the pass tracks the known values of the
  `Nat`/`Int` variables it binds and accepts `Nat.succ` below 2^63 and
  `Int.ofNat`/`Int.negSucc` of `int32` values only.
- **Why:** It cannot panic, trace or allocate, so the change is
  unobservable, and a once-cell read costs more (a load, a test and the
  count's increment, startup/constants.md; the numbers that follow are
  from before a read became one load): deriv 1.20x → 1.11x
  native (a570011); `instInhabitedUInt32` read on every `get!` of an
  `Array UInt32`: qsort 1.03x → 0.89x (8c58721). A big `Nat`/`Int` is a
  heap number: `def K : Int := 3000000000` recomputed was allocated at
  every use, 7-8x native in a loop (RV8N-01; test `RtNatConst` with
  `nat-alloc-check.sh`).
- **Where:** `Opt/CheapConsts.lean`: `isCheapConst` (`smallCtor`), `isUnboxedTy`; hook
  `LowerHooks.recomputeConst`; `Lower/Code.lean`: `lowerDecl`.
- **Remove only if:** the pass is off (every constant outside closed-term
  chains is then cached).

## Required parts that look like optimizations

Listed in `Opt/Registry.lean` (`required`); `--disable-opt` rejects them.

| Part | Entry |
|---|---|
| `startup-chunks` | [startup/order.md](startup/order.md#the-startup-chain-is-cut-into-chunks-of-128-steps) |
| `loop-state-machines` | [control-flow/state-machines.md](control-flow/state-machines.md#a-loop-through-outlined-join-points-is-one-state-machine) |
| `closed-chains` | [startup/constants.md](startup/constants.md#a-closed-term-used-once-by-another-constant-is-not-cached) |
| `stage3-types` | [types/type-recovery.md](types/type-recovery.md) |
| `outline` | [control-flow/outline.md](control-flow/outline.md) |
| `wildcard-sinks` | [reussir-workarounds/build-time.md](reussir-workarounds/build-time.md#issue-22-cost-a-wildcard-arm-over-a-wide-enum-costs-n3-code) |
| `inline-anchors` | [reussir-workarounds/build-time.md](reussir-workarounds/build-time.md#issue-20-cost-the-inliner-multiplies-conversion-code) |

Stage 2's edits of Lean's pass lists (two passes replaced, `extractClosed`
moved to the end, `inferVisibility` and `toImpure` not run) are required
too: [types/lean-passes.md](types/lean-passes.md).

## Hooks

How a pass plugs in, and what installation order means for each kind of
hook, is in `Opt/Registry.lean`'s module comment and `PassConfig.lean`.
State scoped to the code being lowered (passed down into nested code, not
back up or across sibling branches) goes in `CodeCtx.ext`
(`CodeCtx.getExt?`/`setExt`; `Opt/LazyFields.lean`'s `LazyFieldsState`);
whole-program state in `LowerState.ext` (`Opt/FreshRebuild.lean`'s
`freshDeclsCached`).
