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
| `nat-arrays` | `Array Nat`/`Array Int` as one-word `LNatArr`/`LIntArr` | none needed: every array extern has a `natarr`/`intarr` counterpart | [arrays](representations/arrays.md#array-nat-and-array-int-store-one-word-per-element) |
| `split-map-loops` | a `map` loop that changes the element representation writes a new array | only loops of Lean's exact shape (`loopShape?`, `splitCode` fails otherwise): derived arrays used only at the loop index, entered at index 0, never captured | [arrays](representations/arrays.md#maps-that-change-the-element-representation-write-a-new-array) |
| `uniform-updates` | an update or read of a container whose element type depends on a value (`Array lcAny`) runs on the uniform array, boxing one element, instead of converting the whole array there and back; a cons stored at `List lcAny` built there | an `Array` extern only (they do not depend on their type arguments); only when the call receives a uniform value it would convert, its other arguments need at most a box, and a uniform container result is used only where exactly that type is expected (greatest fixpoint over chains and join points' parameters); constructor applications likewise, without chains | [arrays](representations/arrays.md#updates-of-a-uniform-container-run-on-it-uniform-updates) |
| `placeholder-cache` | placeholders that would allocate built once, in a once-cell | only heap placeholders; a placeholder is never inspected | [placeholders](representations/placeholders.md#placeholders-that-allocate-are-built-once) |
| `float-lits` | float literals folded to their bits at compile time | literal arguments only (the functions are pure and total); work bound: exponent ≤ 2000, mantissa (or `Float.ofNat`'s argument) at most 4096 bits | below |
| `cheap-consts` | constants of small literals recomputed at each use | `isCheapConst`: unboxed types only, every `Nat`/`Int` small (`Nat` literals and `Nat.succ` < 2^63, `Int.ofNat`/`Int.negSucc` of `int32` values), other constructors, total scalar conversions, other cheap constants; no strings | below |
| `prelude-repr` | `Nat.repr`/`Int.repr` by the runtime's GMP code | none needed: the same strings (unary calls only) | [nat-int](representations/nat-int.md#natrepr-of-0127-shares-one-string-per-number) |
| `jp-sink` | join points moved to the smallest code containing their jumps | moves only, never duplicates; binders are unique | [join points](control-flow/join-points.md#join-points-are-sunk-before-the-choice-jp-sink) |
| `jp-small` | small join points duplicated at their jumps (J1′) | none needed for soundness (a copy runs the same code once per path); code-size bounds: own body ≤ 40, a copy ≤ 480 (join points jumped to once counted at full size), extra copies ≤ 2000 (4000 for a loop's continuation); never a J2 join point | [join points](control-flow/join-points.md#small-join-points-are-duplicated-within-three-bounds-jp-small) |
| `state-machines` | J4 entered without allocation: every variant nullary, values passed in parameter slots | a jump passes placeholders in the slots it does not fill, never live values; a type without a finite placeholder (`zeroFinite`) gets no slot | [state machines](control-flow/state-machines.md#state-machines-entered-without-allocation-state-machines) |
| `lazy-fields` | fields of a live matched value bound where used | shared values matched at their own type; variables another hook bound again are left alone; applies only where the value is stored, returned or passed whole | [cases](control-flow/cases.md#fields-of-a-live-matched-value-are-bound-where-they-are-used-lazy-fields) |
| `nullary-scrutinee` | in a field-less arm, the matched value rebuilt | only arms of constructors without fields that use the value | [cases](control-flow/cases.md#the-matched-value-of-a-nullary-arm-is-rebuilt-nullary-scrutinee) |
| `sink-proj` | structure projections sunk into the branches that use them | the projection is unused later in the block and in the condition, and no binder clashes; applies only where some branches use it while another keeps the structure whole | [cases](control-flow/cases.md#structure-projections-move-into-the-branches-that-use-them-sink-proj) |
| `fresh-rebuild` | an arm returning a fresh matched value returns it rebuilt | the value is freshly built (whole-program analysis); the arm binds every field and only returns it | [cases](control-flow/cases.md#fresh-values-returned-whole-are-rebuilt-fresh-rebuild) |

### Float literals are folded to their bits (`float-lits`)

- **What:** A call `Float.ofScientific m s e`, `Float.ofNat n` (or the
  `Float32` ones) on literal arguments is evaluated by lean2rr, with the
  same Lean functions, and replaced by `Float.ofBits` of the bit pattern, a
  total conversion of a literal. Calls with an exponent above 2000 or a
  mantissa (or `Float.ofNat` argument) of more than 4096 bits are left to
  run.
- **Why:** These are Lean functions, not C: the slow path goes through
  `Float.Model` with bignum arithmetic. lean2rr is compiled from the same
  `Init` code, so the bits are Lean's, subnormals and rounding included
  (adv3 CN3-01, d3e80aa; test `RtFloatLits`).
- **Where:** `Opt/FloatLits.lean`: `foldFloatLits`, `floatLitBits?`,
  `floatLitMaxExp`, `floatLitMaxBits`; hook `PassConfig.monoPasses`.
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
  unobservable, and a once-cell read costs more: deriv 1.20x → 1.11x
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
| `wildcard-sinks` | [reussir-workarounds/build-time.md](reussir-workarounds/build-time.md#bug-22-a-wildcard-arm-over-a-wide-enum-costs-n3-code) |
| `inline-anchors` | [reussir-workarounds/build-time.md](reussir-workarounds/build-time.md#bug-20-the-inliner-multiplies-conversion-code) |

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
