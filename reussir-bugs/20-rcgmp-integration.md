# 20. The interface that lean2rr's `Nat` and `Int` on rcgmp need (step D)

**Kind:** missing feature. Reussir's built-in `Nat` and `Int` (rcgmp,
upstream #770 to #803) do not have all that lean2rr needs to put Lean's
`Nat` and `Int` on them. Five patches, 20-a to 20-e, add it. One of them,
20-b, also fixes erroneous behaviour (a bug) in the same code; 20-c and
20-e are optimizations. Each patch is described below with its tests.

## Summary

**Kind:** missing feature (the interface for lean2rr's `Nat` and `Int` on
rcgmp: lean2rr's clean-integration step D). **Status:** patched (20-a to
20-e), applied in `./reussir`'s series since 2026-10-25 (branch
`l2r-stepd`, commits `c13b1ac3`, `6bd31204`, `cb24040e`, `729ea9fb`,
`e3b96e03`); not upstream.

**Upstream (2026-10-25):** Not upstream at 00906e38. Reussir's
maintainer asked that the Reussir-side changes for lean2rr be made first
as patches on lean2rr's tree; he takes them from this directory himself.
This entry is written to be read on its own for that purpose. Under the
owner's rule of 2026-10-25 (rcgmp-related fixes and optimizations may go
upstream as pull requests of at most 300 changed lines each), its
patches are prepared as pull request candidates, not opened. (20-a's
`nonnegative` part drops if upstream sets the attribute itself.)

| Patch | Step D name | `l2r-stepd` commit | Kind | What it adds |
|---|---|---|---|---|
| [20-a](patches/20-a-bigint-lean-division.patch) | R1 | `c13b1ac3` | feature (with an optimization) | bigint intrinsics for Lean's division modes and `floormod2expi`; Nat divisions marked `nonnegative` |
| [20-b](patches/20-b-mpz-polyffi-handle.patch) | R2 | `6bd31204` | bug fix and feature | `Nat` and `Int` at polyffi type arguments become an owned handle, `reussir_rt::rcgmp::Mpz` |
| [20-c](patches/20-c-mpz-inline-glue.patch) | R2b | `cb24040e` | optimization | `Mpz` clones and drops through compiler-emitted rcgmp glue that inlines into textures |
| [20-d](patches/20-d-mpz-is-shared.patch) | R2c | `729ea9fb` | feature | `Mpz::is_shared`, through compiler-emitted glue from `rcgmp.mpz.is_unique` |
| [20-e](patches/20-e-hex-bigint-literals.patch) | R3 | `e3b96e03` | optimization (build time) | big integer constants and match keys reach MLIR in hexadecimal |

Step D's notes and the patches' subject lines use the names R1 to R3.
The patches apply in this order, after the other 8 patches of the series
(20-c and 20-d change 20-b's `Mpz`).

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
- **lean2rr's step D.** lean2rr represents Lean's `Nat` and `Int` as one
  word with its own runtime (`leanrt`, tagged FFI handles: patch 10-a,
  [issue 10](10-tagged-ffi-objects.md)). Step D adds a second backend,
  `--int-backend rcgmp`, in which `Nat` and `Int` are Reussir's built-in
  integers: the arithmetic inlines on immediates, and the runtime's
  containers hold the same handle. rcgmp is lean2rr's default backend
  since 2026-10-25; the leanrt backend (`--int-backend leanrt`, the
  default until then) does not need the five patches.

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

## 20-b (R2): `Nat` and `Int` at polyffi type arguments are an owned handle

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
hook) follow. `docs/design/polymorphic-ffi.md` describes both spellings.

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

## 20-e (R3): big integer constants and match keys reach MLIR in hexadecimal

**The cost.** Under rcgmp a 100k-digit `Nat` literal took rrc about 17
minutes, all of it in the step from MIR to MLIR, and the time grew with
the cube of the length (20k digits 8 s, 80k digits 527 s). Codegen
printed each `rcgmp.constant` value and each `rcgmp.match` key as a
decimal integer attribute (`bigint_constant`, `narrowest`), and
`rcgmp::match_arms` printed the keys again in decimal to build the arms
attribute. `Attribute::parse` reads decimal text through LLVM's
`StringRef::consumeInteger`: one full `APInt` multiplication per digit,
cubic in the length (also on LLVM's main branch). Hexadecimal text goes
through one shift of the whole value per digit: quadratic, with a small
constant (`mlir-opt` reads one constant of 100k, 200k and 400k hexadecimal
digits in 0.36, 1.31 and 5.18 s). The patch's code comments and commit
message still say "linear" for this parse; they are corrected when the
series is next rebuilt.

**The patch.** `literal::mlir_integer_attr_text`
(`crates/reussir-core/src/literal.rs`) writes the attribute text in
hexadecimal, `0x…` or `-0x…` (malachite's `LowerHex`; writing the text is linear), at the
same narrowest signed width. Codegen uses it for constants and match
keys, and `rcgmp::match_arms` takes the keys' text instead of parsed
attributes. The MLIR attributes do not change: the MLIR of a 10k-digit
literal is identical, and a unit test compares the decimal and
hexadecimal parses (and the arms attribute) at the edges of the widths,
in the immediate range and at a limb, for either sign.

**Measured.** A 100k-digit `Nat` or negative `Int` literal now compiles
to an object at `-O aggressive` in about 0.5 s (before: about 17 min).

**Tests.** `frontend/bigint_huge_literal.rr` (3^104795, 50000 digits, as
a `Nat` constant, a negative `Int` constant and two `Nat` match keys,
generated by `Inputs/bigint_huge_literal.py`; the compile runs under
`timeout 120`, and the program compares every literal with the power
computed at run time); the reussir-codegen unit test;
`mlir_integer_attr_text` cases in reussir-core's literal tests.

**lean2rr.** Under rcgmp a `Nat` literal of any size is a Reussir literal
(a read-only object in the program's data, no parse at run time), so a
program with a long literal reaches this path.

## Review

Each patch was reviewed adversarially (code review and targeted repros,
plain and under ASan). The reviews found no bug in the final versions of
the five patches. The review notes are
local, outside this repository (`stepd-r12/review/`: `r1`, `r1b`, `r2`,
`r2b`, `r2c`, `r3`).

The same series also makes Reussir's C++ unit tests (`reussir-ut`) build
and pass with the tests on (82 of 82): 02-b updates upstream's
`glue_symbols.cpp` and 10-a adds an `FFIObjectType` builder that
upstream's `record_drop.cpp` uses (issues [2](02-native-drop-order.md#patch)
and [10](10-tagged-ffi-objects.md#where-in-reussir)).

## Upstream note

Each patch is self-contained and in the order of the series; its commit
message has the motivation, the change and its tests. 20-a's
`nonnegative` marking of `Nat` divisions drops if upstream sets the
attribute itself. 20-b changes the spelling of `Nat` and `Int` at polyffi
type arguments and generic positions (an owned `Mpz`), not at positions
declared `Nat` or `Int` (#795's borrowed raw handle stays). 20-c and 20-d
add compiler-emitted glue with fixed names, hidden and `weak_odr`; they
need 20-b. 20-e changes only the text that codegen gives to MLIR's
parser, not the attributes.
