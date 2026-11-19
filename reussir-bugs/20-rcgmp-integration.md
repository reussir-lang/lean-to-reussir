# 20. The interface that lean2rr's `Nat` and `Int` on rcgmp need (step D)

**Kind:** missing feature. Reussir's built-in `Nat` and `Int` (rcgmp,
upstream #770 to #803) do not have all that lean2rr needs to put Lean's
`Nat` and `Int` on them. Five patches, 20-a to 20-e, added it. One of
them, 20-b, also fixes erroneous behaviour (a bug) in the same code;
20-c and 20-e are optimizations. A sixth, 20-f, moved the commit of
mlir-rcgmp that Reussir's build fetches to a faster upstream one. Since
2026-10-26 upstream has 20-b's code (#824, #843, with the tests of #845)
and 20-f's pin (#844): 20-f left the series, and 20-b keeps only the
reviewed patch's tests that the pull requests left out. Each patch is
described below with its tests.

**On upstream `36a55a0f` (the series of 2026-11-18)** the series has
five patches of this entry: 20-a (the intrinsics that lean2rr uses),
20-g (the `nonnegative` mark of `Nat` divisions, once a part of 20-a),
20-c (the glue, kept out of upstream's scoped drop lowering), 20-d and
20-e. 20-b (tests) stays parked. Each patch has a measured claim; none
of them is a wall-time claim.

## Summary

**Kind:** missing feature (the interface for lean2rr's `Nat` and `Int` on
rcgmp: lean2rr's clean-integration step D). **Status:** patched (20-a,
20-g, 20-c, 20-d, 20-e), patches 3 to 7 of the series on upstream
`36a55a0f` (Reussir branch `l2r-base13-r4`). 20-b's code is upstream;
its remaining tests are parked
([`patches/parked/`](patches/parked/)). 20-f left the series on
2026-10-26: upstream #844 made the same move.

| Patch | Subject on `36a55a0f` | Commit | Kind | Measured claim (aarch64; details in the patch's section) |
|---|---|---|---|---|
| [20-a](patches/20-a-bigint-lean-division.patch) | `[bigint] expose Lean division modes and power-of-two remainder` | `0212e8f1` | feature | changes no existing code (8 of 8 upstream units byte-identical after it). A `Nat` division in Lean's mode: 11 instructions on the immediate path, 24 in all, against 16 and 74 for the composed form |
| [20-g](patches/20-g-bigint-nat-nonnegative.patch) | `[bigint] divide Nats as nonnegative integers` | `c9e433ea` | optimization | `if b == 0 { 0 } else { a / b }` at `Nat`: 23 to 16 instructions on the immediate path, 81 to 74 in all (`sdiv` to `udiv`) |
| [20-c](patches/20-c-mpz-inline-glue.patch) | `[bigint] emit inlineable acquire and release glue for foreign handles` | `00e367fb` | optimization | 100 copy-on-write copies of a 1000-element `Vec<Nat>`: 100,000 retain calls and 101,000 release calls to 0 and 0; the object's text 4215 to 4779 bytes (+13%) |
| [20-d](patches/20-d-mpz-is-shared.patch) | `[bigint] expose foreign handle sharing through generated glue` | `d5a9f21b` | feature | no performance claim (a debug primitive); one more small function in every unit that uses integers |
| [20-e](patches/20-e-hex-bigint-literals.patch) | `[bigint] pass integer constants and match keys to MLIR in hexadecimal` | `5baeed3b` | optimization (build time) | rrc on one `Nat` literal of 20,000 digits: 8.17 s to 0.07 s; of 40,000 digits: 74.57 s to 0.18 s; the objects are byte-identical |
| [20-b](patches/parked/20-b-mpz-handle-more-tests.patch) | (tests) | - | tests | parked: tests only, so no claim is possible; it found nothing on the new base |

Wall time of lean2rr's programs: timing run 20 (2026-11-18) timed
20-g alone (below: 1.021 over 13 cases, three cases gain 3 to 12%). The
other patches of this entry were not timed alone: 20-a, 20-c and 20-d
are needed to build, and 20-e changes build time only. The instruction counts of 20-c's old section and 20-f's effect on
L11 were measured on the earlier bases.

**Upstream (2026-11-18):** At `36a55a0f`, 20-b's code and 20-f's pin are
upstream as before; the pin is `dee6c102` now (mlir-rcgmp #51 to #53).
Upstream has no `_lean` division, no `floormod2expi` at the language
level and no `Mpz::is_shared` (source read). Reussir's maintainer wrote
on 2026-10-25: "some further changes may be needed: e.g. exposing
`divi_lean/remi_lean` ... Please make those patches sitting on your
tree. do not open PRs on reussir side." His own upstream attempt with
these changes (Reussir #923) was closed unmerged on 2026-11-05. So these
patches stay here. #988 (2026-11-13) changed upstream's `Mpz`: its
`Clone` and `Drop` call `rcgmp_mpz_retain` and `rcgmp_mpz_release`
directly; 20-c replaces those calls with the glue, as before. Upstream
still prints big constants in decimal (20-e), and its `Nat` divisions
do not set `nonnegative` (20-g).

The text from here to the per-patch sections records the state on
`l2r-base12` (history).

**Upstream, earlier base (history, 2026-10-26):** At `95d9a1c8` upstream has 20-b's code, as our
pull requests #824 (`8130286e`: the handle `reussir_rt::rcgmp::Mpz`),
#843 (`20252b29`: the polymorphic FFI spells `Nat` and `Int` as `Mpz`)
and #845 (`95d9a1c8`: the tests of std's collections and of the edge
cases), the reviewed patch split in three with shorter tests and docs
reworded, and 20-f's pin, as #844 (`5aeb834d`). The other patches are
not upstream. Reussir's maintainer asked that the Reussir-side changes
for lean2rr be made first as patches on lean2rr's tree; he takes them
from this directory himself. This entry is written to be read on its own
for that purpose. Under the owner's rule of 2026-10-25 (rcgmp-related
fixes and optimizations may go upstream as pull requests of at most 300
changed lines each), they are prepared as pull request candidates.
(20-a's `nonnegative` part drops if upstream sets the attribute itself.)

| Patch | Step D name | `l2r-base12` commit | Kind | What it adds |
|---|---|---|---|---|
| [20-a](patches/20-a-bigint-lean-division.patch) | R1 | `a2c2647a` | feature (with an optimization) | bigint intrinsics for Lean's division modes and `floormod2expi`; Nat divisions marked `nonnegative` |
| [20-b](patches/parked/20-b-mpz-handle-more-tests.patch) | R2 (rest) | `b2e70249` | tests | the reviewed R2's tests that #824, #843 and #845 left out (R2 itself, a bug fix and feature: `Nat` and `Int` at polyffi type arguments become an owned handle, `reussir_rt::rcgmp::Mpz`, is upstream) |
| [20-c](patches/20-c-mpz-inline-glue.patch) | R2b | `6471a6de` | optimization | `Mpz` clones and drops through compiler-emitted rcgmp glue that inlines into textures |
| [20-d](patches/20-d-mpz-is-shared.patch) | R2c | `90c53269` | feature | `Mpz::is_shared`, through compiler-emitted glue from `rcgmp.mpz.is_unique` |
| [20-e](patches/20-e-hex-bigint-literals.patch) | R3 | `2b2ef6be` | optimization (build time) | big integer constants and match keys reach MLIR in hexadecimal |

Step D's notes and the patches' subject lines use the names R1 to R3.
The patches apply in this order, after 10-a and 07-a (until Phase 2,
after the 8 of the drop series, 10-a and 07-a), with no change of code;
20-c and 20-d change the `Mpz` that 20-b added, now upstream's (#824;
upstream's comments are reworded, the code is the same, so 20-c applies
with one comment merged). 21-a comes after them (on `l2r-base12`, the
patches of the deleted entry 23 too).

## Context

- **rcgmp.** Reussir's arbitrary-precision integers, from the mlir-rcgmp
  dialect (`rcgmp.*` operations) and its C runtime (`rcgmp_mpz_*`, on
  GMP). An integer is one word, a *handle*: a small value is an
  immediate (a tagged word, no allocation), a big one a pointer to a
  counted heap object. Reussir's built-in `Nat` and `Int` are rcgmp
  integers. `core::intrinsic::bigint` in Reussir's core library exposes
  the operations to Reussir code.
- **Polymorphic FFI (polyffi).** An `#[ffi(import)]` function has a body
  in Rust (a *texture*), compiled by rustc once for each instance. A
  generic texture is instantiated at Reussir types; the renderer
  (`crates/reussir-core/src/full/ffi.rs`) writes each Reussir type as a
  Rust type, and the wrapper around the body decides which arguments to
  release after the body. Reussir's std collections (`Vec`, `HashMap`,
  `BTreeMap` and the others) are textures over Rust's own.
- **lean2rr's step D.** lean2rr's `Nat` and `Int` are Reussir's
  built-in integers: the arithmetic inlines on immediates, and the
  runtime's containers hold the same handle. Step D added this
  representation (`--int-backend rcgmp`, the default since 2026-10-25)
  beside lean2rr's own one-word encoding with its own runtime (`leanrt`,
  tagged FFI handles: patch 10-a, [issue 10](10-tagged-ffi-objects.md)),
  which did not need the five patches; clean-integration D8 removed that
  encoding on 2026-10-26, so every lean2rr build needs 20-a and 20-b.

## 20-a (R1): bigint intrinsics for Lean's division modes and `floormod2expi`

**What is missing.** Lean's divisions do not trap on a zero divisor:
`x / 0 = 0` and `x % 0 = x`, for `Nat.div`/`mod`, `Int.tdiv`/`tmod`
(`lean_int_div`/`mod`), `Int.ediv`/`emod`, `Int.fdiv`/`fmod` and the
exact divisions (`0 / 0 = 0`). lean2rr's rewrite of `x % 2^k` needs the
remainder by a power of two. mlir-rcgmp has both: the `divzero<lean>`
mode of `divsi`, `remsi`, `edivsi`, `emodsi`, `floordivsi`, `floormodsi`
and `divsi exact` (inline on immediates, the `rcgmp_mpz_*_lean` runtime
entries on heap values), and `rcgmp.floormod2expi`. Reussir's
`core::intrinsic::bigint` exposes neither. Without the patch, lean2rr's
prelude must test for zero before the trapping operation (two tests on
the immediate path), and it cannot reach the power-of-two remainder.

**The patch.** New intrinsics in `core::intrinsic::bigint`
(`library/core/src/intrinsic/bigint.rr`, `crates/reussir-core/src/intrinsic.rs`),
each lowered to the operation its name spells:

- `divsi_lean`, `remsi_lean`, `edivsi_lean`, `emodsi_lean`,
  `floordivsi_lean`, `floormodsi_lean`, `divsi_exact_lean`, each
  `(T, T) -> T` for T = `Nat` or `Int`: the operation with
  `divzero<lean>`;
- `floormod2expi(x : T, amount : u64) -> T`: `rcgmp.floormod2expi`, x
  modulo 2^amount, rounded toward negative infinity (the low bits of the
  infinite two's complement; never negative).

All consume their operands, as the existing divisions do, so the
ownership analysis and monomorphization's operand check do not change.
The backend (`crates/reussir-backend/src/rcgmp.rs`) gets
`rcgmp::division` and `rcgmp::exact_division` with a
`DivisionMode { lean, nonnegative }`, and `Shift::FloorMod2Exp`.

**Optimization in the same patch.** Every division of `Nat`s (the `/` and
`%` operators at `Nat`, and every division intrinsic at `Nat`, old and
new) sets rcgmp's `nonnegative` attribute (mlir-rcgmp #48, in the pinned
`ca288d5e`). Both operands are then known to be nonnegative, so an
immediate is untagged by a logical shift and divided unsigned (`lshr`
and `udiv` in the LLVM IR, where an `Int` division has `ashr` and
`sdiv`), with no test of the quotient. Every rounding mode agrees on
nonnegative operands. `Int` divisions do not change.

**Tests.** `frontend/bigint_lean_division.rr` (each mode on immediate and
heap operands of every sign, heap by heap, the smallest immediate divided
by -1, whose quotient 2^61 is a heap value, a zero divisor from the
driver so that the runtime paths run, constant operands that fold, and
the `-O` LLVM IR of a `Nat` `/` and a `Nat` `remsi_lean`, unsigned,
against an `Int` `/`, signed); `frontend/bigint_floormod2exp.rr` (amounts
0, within the value, around the 62-bit immediate width and the largest
`u64`, on `Nat`, negative `Int` and heap values; a cross-check against
`floormodsi` by 2^k for k up to 130; an in-place reduction chain); both
under ASan in `sanitizer/bigint-asan.rr`; the new names and the
`nonnegative` `Nat` divisions in `frontend/bigint_intrinsics.rr` (MIR
round trip, MLIR spelling).

**lean2rr.** The prelude's rcgmp blocks call the `_lean` intrinsics for
Lean's divisions and `floormod2expi` for the mod-2^k rewrite.

### 20-a on 36a55a0f: only the intrinsics that have a user

The patch of the final series differs from the text above in two
points (review of 2026-11-18, local notes `port13/reviews/RV2`):

- **Three intrinsics are gone:** `floordivsi_lean`, `floormodsi_lean`
  and `divsi_exact_lean`. Nothing in lean2rr calls them: the prelude
  uses `divsi_lean`, `remsi_lean`, `edivsi_lean`, `emodsi_lean` and
  `floormod2expi`. The backend's `rcgmp::exact_division` went with
  them. The patch is +468/-4 lines now (before: +674/-14).
- **The `nonnegative` mark is a patch of its own, 20-g.** 20-a alone
  changes no existing division.

Checked on this base:

- *Semantics.* A table of 3104 functions against Python integers: the
  `_lean` divisions on `Int` and `Nat`, the trapping divisions and `/`,
  `%` on `Nat`, `floormod2expi`, shifts; operands from 0 to
  ±(2^128 - 1), zero divisors, heap by heap; each case with runtime
  operands, constant operands and mixed. 23,860 checks, 0 failures at
  `-O none`, `-O default` and `-O aggressive` (run on the series before
  the three intrinsics were removed).
- *The fused quotient and remainder of mlir-rcgmp #51* work through the
  intrinsics: `divsi_lean` with `remsi_lean`, and `edivsi_lean` with
  `emodsi_lean`, of the same operands are one runtime call (847 checks,
  0 failures).
- *What it buys* (AArch64 instructions at `-O aggressive`, from the
  entry to the first `ret`, which is the path of immediates, and in the
  whole function; "composed" is `if b == 0 { 0 } else { a / b }` on the
  series):

  | Function | 20-a's intrinsic | composed |
  |---|---|---|
  | `Nat` div | 11 / 24 | 16 / 74 |
  | `Nat` mod | 12 / 25 | 17 / 63 |
  | `Int` div | 15 / 28 | 23 / 81 |
  | `Int` emod | 20 / 33 | 24 / 70 |

  The composed form also calls `rcgmp_mpz_cmp` for a heap divisor
  before it divides. The power-of-two remainder has no composed form
  without a call that builds 2^w.
- *What it costs elsewhere:* nothing. After 10-a, 07-a and 20-a, the 8
  upstream units that the series changes at all (core, std, six integer
  programs) are byte-identical to pristine upstream.

## 20-g: divisions of `Nat`s are marked `nonnegative`

Split from 20-a on 2026-11-18, because it is a second topic: an
optimization of code that exists upstream, not a new intrinsic.

**The cost.** rcgmp's divisions take a `nonnegative` attribute
(mlir-rcgmp #48): both operands are then known to be nonnegative, so an
immediate is untagged by a logical shift and divided unsigned, with no
test of the quotient's sign. Upstream Reussir does not set it, so a
`Nat` division pays the signed path.

**The patch.** Every division of `Nat`s sets the attribute: `/` and `%`
at `Nat`, and every division intrinsic at `Nat` (`edivsi`, `emodsi`,
`floordivsi`, `floormodsi`, `divsi_exact` and the `_lean` ones). `Int`
divisions do not change. `DivisionMode` gets the field `nonnegative`,
and `rcgmp::divsi_exact` a parameter.

**Why it is sound.** A `Nat` cannot be negative in Reussir: `Int as
Nat` and `i64 as Nat` are refused, `Nat` has no negation, and `-` on
`Nat` stops at zero (checked by the review with one program of each).
A negative value can reach such a division only from the foreign side
(a texture that returns a negative `Mpz` at type `Nat`); the result is
then a wrong number, not undefined behaviour of the generated code
(read in mlir-rcgmp's lowering: no `nuw`, `exact` or assume flag).

**Measured** (AArch64 instructions at `-O aggressive`, immediate path /
whole function, the compiler at 20-a against the compiler at 20-g):

| Function | at 20-a | at 20-g |
|---|---|---|
| `if b == 0 { 0 } else { a / b }`, `Nat` | 23 / 81 (`sdiv`) | 16 / 74 (`udiv`) |
| `divsi_lean`, `Nat` | 15 / 28 | 11 / 24 |
| `remsi_lean`, `Nat` | 13 / 26 | 12 / 25 |
| `a % ipowi(2, w)`, `Nat` | 18 / 41 | 15 / 38 |
| the `Int` functions, `floormod2expi` | unchanged | unchanged |

On upstream's benchmark suite with core and std (33 units), 20-g is the
only patch of the series that changes existing code: 6 functions (two
of core's `Nat::div_exact`, and one each in bigint-binomial,
bigint-collatz, bigint-factorial and bigint-fib): `ashr` to `lshr`,
`sdiv`/`srem` to `udiv`/`urem`, and 5 or 6 operations fewer where the
quotient is taken.

**Wall time** (timing run 20, 2026-11-18: lean2rr's port on the final
series against the same with 20-g taken out; direct pairs, median of 9
and min, the two sides in turn; 13 cases of the shared benchmark set
whose code the patch changes; a ratio above 1 means that 20-g gains):

| Case | with 20-g | without | without / with (median) | (min) |
|---|---:|---:|---:|---:|
| Z01d lean-zip decompress | 1528.3 ms | 1715.2 ms | 1.122 | 1.127 |
| L14 higher-order | 1389.8 ms | 1545.7 ms | 1.112 | 1.112 |
| Z01c lean-zip compress | 6750.6 ms | 6983.5 ms | 1.034 | 1.034 |

Geometric mean over the 13 cases: 1.021. No case loses. No measurable
effect on the ten others, the division-heavy L11 bignum (1.000), E01
gcd_batch (0.998) and L12 sieve (1.010) among them.

**Tests.** `frontend/bigint_nat_division.rr` (the `-O` LLVM IR of a
`Nat` `/` and of a `Nat` `remsi_lean` divides the untagged immediates
unsigned, an `Int` `/` signed); the `nonnegative` spelling in
`frontend/bigint_intrinsics.rr`.

## 20-b (R2): `Nat` and `Int` at polyffi type arguments are an owned handle

**Parked since the move to `36a55a0f` (2026-11-17); decided on
2026-11-18: it stays parked.** What is left of
20-b is tests, and the maintainer's port left it out. Its file is in
`patches/parked/`. It applies to the new base and its tests pass there
(7 of 7 `frontend/bigint_ffi*` lit tests and the unit test), but it is
tests only, so it cannot have a measured claim, it found nothing on the
new base, and it edits three upstream test files, which costs a
conflict at every upstream change there. Upstream's own tests cover
most of it; three checks are only in 20-b: `set` on a uniquely owned
vector, growth through reallocation with heap elements, and set
membership of `Int` across signs. Without it, 20-c has no unit-test assertion of the
glue pair (that hunk of 20-c edited a test that 20-b adds); if 20-b
comes back, that hunk comes back with it. An open upstream pull request
(#974) moves `frontend/bigint_ffi_std.rr`, which the tests of 20-b sit
next to.

**Upstream since 2026-10-26.** The patch described here went upstream
split in three pull requests: #824 (the handle), #843 (the spelling at
type arguments and the wrapper's releases) and #845 (the tests of std's
collections and of the edge cases, whose ASan run of the edge test is
part of `bigint-ffi-std-asan.rr`). Their code is the patch's; their
tests are shorter, and #824 rewords the comments of `rcgmp.rs`. The
series keeps, as 20-b (`b2e70249`), only the reviewed patch's tests that
none of them has: the reussir-core unit test of the spellings (a type
argument and a generic instantiated at `Nat` are the owned handle; a
declared `Nat` stays the raw handle, which the wrapper releases), the two
more properties of `frontend/bigint_ffi_generic.rr` (six, not four), and
the membership checks of a Rust set of `Int`s across signs in
`frontend/bigint_ffi_edge.rr`, with its fuller header.

**The bug.** Upstream #795 lets `Nat` and `Int` cross `#[ffi(import)]` as
the raw rcgmp handle, `*mut c_void`, which the wrapper releases after the
body: the body borrows it. The renderer writes them that way at every
position, and the wrapper decides the release from the substituted
parameter type. Both are wrong where a texture keeps an integer as its
own:

- at a type argument, `Vec<Nat>` is `Vec<*mut c_void>`: the vector never
  releases its elements (a leak), and a clone does not retain them;
- a generic parameter `x : T` at T = `Nat` is released after the body,
  although the body stored it (`v.push(x)`) or returned it: the vector or
  the caller then holds a freed handle.

Reussir's own std collections show it at `Nat`: under ASan, a `Vec<Nat>`
of heap values pushed and read back is a heap-use-after-free. The new
tests `bigint_ffi_std.rr` and `bigint_ffi_edge.rr` give wrong results
and uses after free with the compiler of `l2r-base5` (upstream 00906e38
with the first 8 patches). This is erroneous behaviour, a bug by the
[kinds](README.md#kinds); it is in this entry because lean2rr needs the
fix as part of the interface.

**The patch.** A new type, `reussir_rt::rcgmp::Mpz`
(`crates/reussir-rt/src/rcgmp.rs`): a `#[repr(transparent)]` pointer
that owns one nonatomic reference. `Clone` retains it, `Drop` releases
it, `PartialEq` and `Ord` compare the values (`rcgmp_mpz_cmp`), and
`from_raw`, `into_raw` and `as_ptr` convert to and from the raw handle.
So the runtime's `BTreeSet` and `BTreeMap` order `Nat` keys by value, and
its `HashMap` and `HashSet`, which take the digest from Reussir's
hashers, compare them by value. `Mpz` has no `Hash`: a Rust texture that
needs `T: Hash` at `Nat` now fails to compile, where before it hashed the
pointers. Every method that calls the rcgmp runtime is `#[inline]`, so it
is compiled only into the textures that use it: `libreussir_rt` (`.a`,
`.so`, the ASan variant, release and debug) references no rcgmp symbol,
and a program without integers still links without the rcgmp runtime.

The renderer (`full/ffi.rs`) writes `Nat` and `Int` as
`::reussir_rt::rcgmp::Mpz` at every position. An `#[ffi(import)]`
parameter or result keeps the raw handle only where the signature
declares `Nat` or `Int` itself (`boundary_rust_name`,
`raw_rcgmp_handle`); monomorphization (`full/mono.rs`) reads the declared
types next to the substituted ones. So:

- a parameter declared `Nat` is borrowed and released after the body, as
  with #795;
- a generic parameter at `Nat` is the body's own `Mpz`, with no release
  after the body;
- a generic result at `Nat` moves its reference to the caller (the C ABI
  still passes a pointer).

Placeholders (`[:T:]`) and opaque instances (`Vec<Mpz>` and its drop
hook) follow. `docs/design/polymorphic-ffi.md` described both spellings
(upstream has moved its design documents to another repository since).

**Tests.** `frontend/bigint_ffi_std.rr` (std's copy-on-write `Vec`,
`HashMap`, `HashSet`, `BTreeMap`, `BTreeSet`, `VecDeque` and
`BinaryHeap` at `Nat` and `Int` with heap values, std built as a
package) and its ASan twin `sanitizer/bigint-ffi-std-asan.rr`, whose
textures compile against the sanitized runtime's crates (new lit
substitution `%polyffi_asan_libdirs`, from CMake's `REUSSIR_RT_ASAN_DEPS`);
`frontend/bigint_ffi_edge.rr` and its ASan twin (a nested
`Vec<Vec<Nat>>`, unused and twice-used generic parameters, a declared
`Nat` among generic parameters in the packed boundary, a declared `Nat`
result of a generic texture, a closure that moves the handle, one heap
value passed twice, a vector dropped while it holds heap elements, `Int`
order across signs in a `BTreeSet`); `frontend/bigint_ffi_generic.rr`
and its ASan twin (a Rust `Vec<Nat>` with heap and immediate elements:
push, get, set, a copy-on-write clone on the Rust side, growth to 100
elements; a generic texture that returns one argument and drops the
others, at `Nat` and `Int`, also through the four-parameter packed
boundary; a declared `Nat` parameter stored by the body and a declared
`Nat` result; a `BTreeSet<Nat>` that removes equal heap values; the
rendered spellings); a reussir-core unit test of the spellings; a
reussir-rt unit test of the handle's layout and raw round trip.

**lean2rr.** Under rcgmp, lean2rr's typed arrays, cells and once-cells
hold `Nat` and `Int` as type arguments of the runtime's generic textures
(`RVec<Nat>` and others). Without the patch they leak or read freed
values.

## 20-c (R2b): `Mpz` clones and drops through glue that inlines into textures

**The cost.** 20-b's `Mpz` retains and releases through the rcgmp
runtime's C entry points. So every clone and drop of a `Nat` in a Rust
container is a call, also for an immediate, where retain and release do
nothing. lean2rr's typed `Array Nat` pays it at every read, copy and
free: a microbenchmark (push, sum, bump in place and 100 copy-on-write
copies of 100k elements) ran 2.03 times the instructions of lean2rr's
old `Nat`, about 8 instructions per element for each call against 1 for
the old inline bit test.

**The patch.** `Mpz`'s `Clone` and `Drop` call
`__reussir_rcgmp_ffi_acquire` and `__reussir_rcgmp_ffi_release`, plain
`extern "C"` functions that the compiler emits:

- Rendering `Mpz` (`full/ffi.rs`) records a glue entry keyed
  `__reussir_rcgmp` next to the shared-record wrappers. Monomorphization
  turns it into an `FfiRcGlue` pair with those two symbols, as for a
  shared record's `<sym>_ffi_acquire`/`_ffi_release`. It also adds the
  pair to every program that uses `Nat` or `Int` (`uses_bigint`, the
  condition under which rrc links the rcgmp runtime) when no texture
  asked for it, so runtime code outside the textures that holds an
  `Mpz` (lean2rr's runtime keeps big `Nat`s in box cells) always finds
  it.
- Codegen (`ffi_rc_glue`) emits their bodies as `rcgmp.retain` and
  `rcgmp.release`, not `rc.inc`/`rc.dec`: in the home unit, `weak_odr`
  under every policy (one fixed name, the same definition in every
  module). The backend gives every `__reussir_rcgmp_ffi_*` definition
  hidden visibility once the module is linked (`hide_rcgmp_glue` in
  `crates/reussir-backend/src/llvm.rs`), so each module and shared
  library binds its own copy, next to its own view of the rcgmp runtime.

So the rcgmp lowering decides the immediate test (the dialect does not
make its tag an ABI; Rust has no copy of the tag), and LLVM inlines the
glue into the linked texture code where the target attributes allow it,
as for lean2rr's textures, which are compiled for the program's CPU.
reussir-rt has no fallback and no weak symbols, and builds on stable
Rust; a program without integers links without the rcgmp runtime and
GMP. Runtime code outside the textures that holds an `Mpz` in dead code
needs `--gc-sections` (the default of rustc's and rrc's links) to drop
its reference to the glue.

**Measured.** Instruction counts (cachegrind) of 1000 copy-on-write
copies of a 1000-element `Vec<Nat>`, with textures compiled for the host
CPU, as lean2rr does:

| Elements | 20-b alone | with 20-c |
|---|---|---|
| immediates | 30.86 million | 12.85 million |
| heap values | 41.08 million | 26.07 million |

With textures for rustc's generic target, which keeps the glue out of
line: 17.86 and 28.08 million.

**Tests.** `frontend/bigint_ffi_glue.rr` (the glue's MLIR, its MIR round
trip, its hidden `weak_odr` definitions, also in a program without
textures, `bigint_division.rr`, and none in a program without integers,
`ffi_vec_e2e.rr`; at `-O` with the textures' target, no call to the glue
or to rcgmp's retain and release in a `Vec<Nat>` copy-and-drop loop, a
clone or a drop; the program runs); `frontend/bigint_ffi_dynlib.rr` (a
Reussir shared library with `Nat` textures and its own static runtimes,
in a host that links `libreussir_rt.so` before it: it runs and exports
none of the glue); ASan runs of `bigint_ffi_glue.rr` and of
`bigint_ffi_generic.rr` with the glue inlined; the glue pair in the
reussir-core unit test.

**lean2rr.** Its typed arrays of `Nat` read, copy and free elements
without a call for immediates. lean2rr's runtime, outside the textures,
holds big `Nat`s as `Mpz` and uses the glue that every program with
integers gets.

### 20-c on 36a55a0f: the glue and upstream's scoped drop lowering

Upstream's drop series of 2026-11-01 keeps records of foreign releases:
it marks every `_ffi_release` function as a foreign drop
(`reussir.foreign_drop`), collects the FFI symbols of a unit, and gives
each import and each texture its `release_bindings`. A foreign drop
becomes a bridge into the drop worklist. The integer glue of 20-c must
stay out of all three, and the patch on `36a55a0f` does that (the
change is from the maintainer's port, where it was a part of his patch
24-b):

- `crates/reussir-codegen/src/lower/expr.rs`: the integer release glue
  does not get the `reussir.foreign_drop` attribute.
- `lower/mod.rs`: its symbol is not added to the unit's FFI symbols.
- `crates/reussir-core/src/full/mono.rs` (two places): integer
  declarations are filtered out of the `release_bindings` of an
  `FfiImport` and of an `FfiTexture`.

Why: `rcgmp.release` is a leaf (an integer has no members to release),
and the glue's symbol has one fixed name shared by all modules, not one
name for each texture. Without these changes the new lowering treats
the glue as the release binding of one texture.

**The refinement of 2026-11-18** (review `port13/reviews/RV2`, then
`RV6`):

- *The glue is defined in every codegen unit* (`weak_odr`), not only in
  its home unit. Before, with more than one unit, the textures of the
  other units called the glue out of line. The reviewer's program with
  four units: 21 call relocations to the glue before, 3 now, the same 3
  that the one-unit build has (measured with the program compiled for
  the textures' target, `--target-cpu generic --target-features=`).
  lean2rr builds with one unit, so this changes nothing for lean2rr
  today.
- *Hidden visibility through a module attribute.* The unit lists the
  glue in `reussir.hidden_symbols` (next to `reussir.ffi_symbols`), and
  `qualifyFfiSymbols` hides the listed definitions when the module is
  translated, in rrc and in `reussir-translate`. The scan of symbol
  names by prefix in the Rust backend (`hide_rcgmp_glue`) is gone, and
  `crates/reussir-backend/src/llvm.rs` is no longer touched. Test
  `codegen/hidden_symbols.mlir`.
- *The `WrapperDecl` entry: removed, then restored.* Rendering `Mpz`
  records a glue entry next to the shared-record wrappers' (it declares
  nothing in the texture). The first round of the refinement removed it
  as redundant with the rule "every program that uses `Nat` or `Int`
  gets the pair" (`uses_bigint`). The review of that round showed that
  it is not redundant: a generic import whose type parameter appears
  only in the foreign body (`probe<Nat>` with a `Vec<[:T:]>` inside)
  uses no integer in any place that `uses_bigint` looks at. The program
  compiled, and the link failed with `undefined reference to
  __reussir_rcgmp_ffi_acquire`. The entry is back: the owned handle's
  spelling is made at exactly one place, and that place records the
  entry, so every texture that the compiler writes with the handle
  brings the glue. Test `frontend/bigint_ffi_phantom.rr` (it failed to
  link on the round-1 patch; it links and prints 5 now). Not covered,
  as before: a foreign body that writes `::reussir_rt::rcgmp::Mpz` by
  hand in a program without integers.

Other differences from `l2r-base12`'s 20-c: one conflict at the move, in
`render_ty` (`full/ffi.rs`: upstream added arms for pointers and SIMD
types next to the `BigInt` arm; both are kept); the FileCheck names of
the wrappers in `bigint_ffi_glue.rr` end in `.backward` (upstream's
suffix for the drop order); no hunk in `docs/design/polymorphic-ffi.md`,
and no unit-test hunk (see 20-b).

**Measured on this base** (aarch64, `-O aggressive --relocation-mode
pic`, textures compiled for the program's CPU; the calls into the rcgmp
runtime counted with the linker's `--wrap`): 100 copy-on-write copies
of a 1000-element `Vec<Nat>`.

| | retain calls | release calls | free calls | object text |
|---|---|---|---|---|
| upstream `36a55a0f`, immediates / heap values | 100,000 / 100,000 | 101,000 / 101,000 | 0 / 1 | 4215 bytes |
| with 20-c, immediates / heap values | 0 / 0 | 0 / 0 | 0 / 1001 | 4779 bytes (+13%) |

So a call for each element at each clone and each drop becomes a test
of the low bit in the loop; a heap value is freed by one call at its
last release. Executed instructions and wall time were not measured on
this base (the table of the section above is from the earlier base).
The inlining needs textures compiled for the program's CPU, as
lean2rr's are. Cost in every program: with 20-c and 20-d each unit that
uses integers has three small hidden `weak_odr` functions, also
upstream's own benchmark units; no existing function of those units
changes.

**Ownership checked** by the review: no leak and no double free in four
container shapes under both drop orders. Linkage: three codegen units
link with no duplicate symbol; a shared library exports and imports
none of the glue, also with thin and fat LTO; `libreussir_rt.so` has no
reference to the glue.

On the final series (2026-11-18, aarch64): `frontend/bigint_ffi_glue.rr`,
`bigint_ffi_dynlib.rr`, `bigint_ffi_phantom.rr` and
`codegen/hidden_symbols.mlir` pass. The ASan runs cannot run on the
build machine (no sanitizer runtime).

## 20-d (R2c): `Mpz::is_shared`

**What is missing.** lean2rr's `dbgTraceIfShared` (Lean's
`lean_dbg_trace_if_shared`, natively `!lean_is_scalar(a) &&
!lean_is_exclusive(a)`) must say whether a big `Nat` or `Int` held in
runtime code is shared. rcgmp's C API has no query of the count or of
uniqueness; its dialect has `rcgmp.bridge.mpz.is_unique` (a heap handle
with an owned reference; false for an immortal).

**The patch.** Codegen emits a third function next to 20-c's pair, in
the same way (home unit, `weak_odr`, hidden):
`__reussir_rcgmp_ffi_is_unique(handle) -> u8`, 1 for an immediate
(`rcgmp.bridge.mpz.is_immediate`), otherwise `rcgmp.bridge.mpz.is_unique`.
It returns a byte, not an `i1`, as the borrowed comparison entries do, so
that the value at the C ABI is defined. `Mpz::is_shared` is
`is_unique == 0`. So an immediate is never shared, a heap integer is
shared while another reference holds it, and an immortal literal always
is. That is native Lean's answer: a persistent object (count 0) fails
`lean_is_st`, so `lean_is_exclusive` is false, as for Lean's closed
constants. The backend gets the `is_immediate` and `is_unique`
builders; reussir-core names the symbol (`RCGMP_IS_UNIQUE`).

**Tests.** `frontend/bigint_ffi_shared.rr` (an immediate, a unique heap
value, a heap value that the caller still holds, one after a clone in
the texture, an immortal literal, a negative heap `Int`, and `Vec<Nat>`
elements read while the vector holds them; the glue's MLIR; runs with
the glue out of line and inlined) and its ASan twin
`sanitizer/bigint-ffi-shared-asan.rr`; the hidden `weak_odr` definition
in `frontend/bigint_ffi_glue.rr`.

**On `36a55a0f`.** The third function is emitted like 20-c's pair: in
every codegen unit, `weak_odr`, listed in `reussir.hidden_symbols`. The
C driver of `bigint_ffi_glue.rr` also calls the three glue functions on
a heap value: unique, shared after an acquire, unique again after a
release (from the maintainer's port). `frontend/bigint_ffi_shared.rr`
passes on aarch64 (2026-11-18); its ASan twin cannot run on the build
machine. No performance claim: the patch is a feature for a debug
primitive, and it adds one small function to every unit that uses
integers.

Upstream's new `core::object::is_unique` (#983) is a language intrinsic
for rc-managed objects and rejects `Nat` and `Int` today
(`crates/reussir-core/src/semi/ty_eval.rs`: "a built-in integer
handle"). The review sketched an extension of it (about 30 lines) that
could replace this patch with a cleaner interface. Parked: 20-d stays
as it is. Note the two names: the glue function is
`__reussir_rcgmp_ffi_is_unique`; the runtime method, which
`scripts/l2r.py` checks for, is `Mpz::is_shared`.

## 20-e (R3): big integer constants and match keys reach MLIR in hexadecimal

**Back in the series since 2026-11-18**, moved to `36a55a0f` with no
conflict and measured there. The maintainer's port had left it out.
Upstream has not fixed the cost: at `36a55a0f` codegen still prints
each big constant in decimal and parses it. The text above says
"linear" in one place for the hexadecimal parse; the new commit message
says "through shifts".

**Measured on `36a55a0f`** (aarch64; one rrc process, user seconds; a
program with one `Nat` literal of the given length, default level, to
an object):

| Digits | without 20-e | with 20-e |
|---|---|---|
| 5,000 | 0.15 s | 0.04 s |
| 10,000 | 1.04 s | 0.05 s |
| 20,000 | 8.17 s | 0.07 s |
| 40,000 | 74.57 s | 0.18 s |
| 100,000 | not finished: stopped at 300 s of wall time (283 s user); about 19 min by the cube law | 0.85 s |

Two match keys of 10,000 digits: 4.17 s to 0.10 s; of 20,000 digits:
32.9 s to 0.15 s (each key was parsed twice). The review measured three
of the rows again (10,000 digits 1.05 s to 0.03 s, 20,000 digits 8.16 s
to 0.05 s, two keys of 10,000 digits 4.19 s to 0.08 s).

**The same code.** The objects are byte-identical with and without the
patch at 5,000 to 40,000 digits and for both key programs; `--emit
mlir` and `--emit llvm-ir` are byte-identical at 10,000 digits. The
review checked 520 values at the edges of the widths (limbs, sign, the
arm that a `match` selects) at three levels: 0 bad. On upstream's
benchmark suite with core and std, and on 14 lean2rr programs, the
patch changes no code.

**The claim is a build-time claim only.** There is no run-time claim.
What it means for lean2rr: the largest literals of the runtime suite
(`RtNatLitHuge`, 20,000 digits) cost about 8 s each without the patch,
so the suite passes without it; a literal of 100,000 digits is the case
where rrc looks hung. `scripts/l2r.py` does not check for the patch.

**Not covered:** `--emit mlir` prints decimal, so a compile that starts
again from a saved `.mlir` with such a literal pays MLIR's own cubic
parse.

**Tests on this base:** `frontend/bigint_huge_literal.rr` passes;
reussir-core's `literal` tests (28) and reussir-codegen's `hexadecimal`
test pass.

## 20-f: the mlir-rcgmp pin moved to cc73b218 (upstream since #844)

History. At `36a55a0f` upstream pins `dee6c102` (mlir-rcgmp's main on
2026-11-14), which has `cc73b218`'s changes and mlir-rcgmp #51 (a fused
quotient and remainder) to #53.

**Upstream since 2026-10-26:** #844 (`5aeb834d`) made the same move, so
20-f left the series (`l2r-base12`); its file is in git history (commit
`af521c12`, `reussir-bugs/patches/20-f-rcgmp-pin-cc73b218.patch`). It
was commit `a39e59b0` on `l2r-base11`, its subject "rcgmp pin". Not a
Reussir problem: Reussir's build fetches mlir-rcgmp, the dialect and C
runtime of its built-in integers, at the commit that `cmake/RCGMP.cmake`
pins (`GIT_TAG`), and upstream moves that pin from time to time (#804
moved it to `ca288d5e`, for mlir-rcgmp #48). 20-f moves it to
`cc73b218`, mlir-rcgmp's main with #49 (vectorized heap paths of AND, OR
and XOR) and #50 (division without a remainder when only the quotient is
wanted). Only mlir-rcgmp's `runtime/Bitwise.cppm` and
`runtime/Divide.cppm` change between the two commits, with their tests:
no dialect, conversion or C API file, so every rcgmp operation lowers as
before.

**Effect.** lean2rr's L11 (bignum, dominated by quotients): 40.10G
instructions with `ca288d5e`, 33.50G with `cc73b218` (-16%), the count
that lean2rr's earlier leanrt representation of `Nat` reached: GMP's
`mpn_tdiv_qr` no longer computes the divide-and-conquer remainder when
only the quotient is used.

**Tests** (the runtime side, 2026-10-26, on a build configured with
`FETCHCONTENT_SOURCE_DIR_RCGMP` at a `cc73b218` checkout, which is the
same build): the 24 patches before it build unchanged, lean2rr's 28
`Nat` and `Int` runtime tests and their alloc-checks pass.

**Status.** It was a local stand-in until upstream Reussir moved its pin
to `cc73b218` (as it did for #48 in #804); upstream did, in #844.

## Review

On `36a55a0f` (2026-11-18), independent reviews (local notes
`port13/reviews/`): `RV2` for 20-a, 20-c and 20-d (no bug; its findings
are the trimmed intrinsics, the split of 20-g, the glue in every unit
and the hidden-symbols attribute), `RV6` for that refinement (one
regression found and fixed: the `WrapperDecl` entry), `RV5` for 20-e
(approved as ported). On the final series: 26 of the 30 lit tests that
the series adds or changes pass, and 4 are unsupported on the build
machine (the sanitizer twins); `reussir-ut` 97 of 97; cargo tests of
reussir-core (677), reussir-codegen (87) and reussir-backend (29) with
0 failures. Not run: the full lit suite, clang-tidy, the sanitizer
tests; clang-format is not installed there. The text below records the
reviews on the earlier bases.

Each patch was reviewed adversarially (code review and targeted repros,
plain and under ASan). The reviews found no bug in the final versions of
the five patches. The review notes are
local, outside this repository (`stepd-r12/review/`: `r1`, `r1b`, `r2`,
`r2b`, `r2c`, `r3`).

Reussir's C++ unit tests (`reussir-ut`) build and pass with the tests on
(82 of 82 on `l2r-base9` and on `l2r-base12`): 10-a adds an `FFIObjectType` builder that
upstream's `record_drop.cpp` uses
([issue 10](10-tagged-ffi-objects.md#where-in-reussir)). (On `l2r-stepd`,
patch 02-b also updated upstream's `glue_symbols.cpp` for its drain
declaration; 02-b left with Phase 2.)

On `l2r-base12` (2026-10-26) the tests of entry 20's patches and of the
pull requests pass: every `bigint`, `rcgmp` and `polyffi` lit test of a
build with the tests and the ASan runtime (`frontend/bigint_ffi_generic.rr`
and `bigint_ffi_edge.rr` with 20-b's additions, `sanitizer/bigint-ffi-std-asan.rr`
with #845's run of the edge test; TSan and the builds without rcgmp are
unsupported there) and reussir-core's unit test of the spellings
(`bigint_type_arguments_cross_the_ffi_as_owned_handles`).

## Upstream note

Each patch is self-contained and in the order of the series; its commit
message has the motivation, the change and its tests. 20-a's
`nonnegative` marking of `Nat` divisions drops if upstream sets the
attribute itself. 20-b's change of the spelling of `Nat` and `Int` at
polyffi type arguments and generic positions (an owned `Mpz`; positions
declared `Nat` or `Int` keep #795's borrowed raw handle) is upstream
(#824, #843, #845), and what is left of 20-b is tests; 20-f is upstream
(#844). 20-c and 20-d add compiler-emitted glue with fixed names, hidden
and `weak_odr`; they need the `Mpz` of #824, and on `36a55a0f` 20-c
keeps the glue out of the scoped drop lowering's records of foreign
releases. 20-e changes only the text that codegen gives to
MLIR's parser, not the attributes. 20-g drops if upstream sets the
`nonnegative` attribute itself.
