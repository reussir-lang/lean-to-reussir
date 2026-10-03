# `Nat` and `Int`

Paths: `runtime/prelude.rr`, `runtime/leanrt/src/`, and
`lean2rr/LeanToReussir/` for lean2rr's files.

### `Nat` and `Int` are one word each, in Lean's own encoding

- **What:** A `Nat` or `Int` is one machine word. An odd word is a small
  value: `lean_box(n) = 2n+1` for a `Nat` below 2^63
  (`LEAN_MAX_SMALL_NAT`), `lean_box((unsigned)(int)i)` for an `Int` in the
  `int32` range (its 32 bits zero-extended, so a `Nat` below 2^31 and the
  `Int` of the same value have the same word). An even word is an owned
  pointer to a big number. The Rust types are `leanrt::nat::LNat`/`LInt`,
  whose `Clone`/`Drop` test the bit.
- **Why:** The earlier two-word `[value] enum { Small, Big(LBig) }` made
  every `Nat` field 16 bytes (native: 8; rbmap and records of `Nat`s now
  0.84x and 0.80x native peak memory, were 1.00x and 1.26x; mem-nat
  a8fc2e2). Lean's exact encoding lets C code written against `lean.h`
  take and return the words unchanged (ffi-c).
- **Where:** `runtime/prelude.rr` (`struct Nat`, `struct Int`, the Nat and
  Int sections); `runtime/leanrt/src/nat.rs`; plan
  [§5.1](../../translation-plan.md#51-type-translation) ("One-word `Nat`
  and `Int`", which also weighs the alternatives).
- **Remove only if:** lean2rr gives up `lean.h` compatibility and Reussir
  gains a native tagged-integer type.

### Reussir counts only the even words (tagged opaque handles, patch 0050)

- **What:** The prelude declares `#[ffi(rust = "::leanrt::nat::LNat",
  tagged)] pub struct Nat;` (and `Int`). With Reussir patch 0050, `rc.inc`
  of a `tagged` handle touches the count, and `rc.dec` calls the drop hook,
  only when the low bit is clear; the nonlinear-FFI instrumentation and
  `rc.assume_unique` skip such handles too. Copying or dropping a small
  value is a bit test, and it is never allocated.
- **Why:** Reussir inserts the reference counting itself and increments
  an opaque handle at its address; a small `Nat` has no address. A clone
  hook would cost a call per copy; lean2rr cannot count `Nat`s itself
  because it cannot change the drop glue Reussir generates for records,
  closures and enums.
- **Where:** `reussir-bugs/patches/0050-*.patch` and
  [local-additions.md](../../../reussir-bugs/local-additions.md#0050-tagged-opaque-handles-one-word-nat-and-int)
  (`BasicOpsLowering.cpp`: `beginRealBoxGuard`); `prelude.rr`: `struct
  Nat`, `struct Int`.
- **Remove only if:** upstream Reussir supports immediates in opaque types
  (then use that).

### Every value has one form (normalization)

- **What:** A `Nat` below 2^63 and an `Int` in `int32` are always small;
  every slow path returns through `LNat::of_big`/`LInt::of_big`, which
  turn an in-range big result back into its word.
- **Why:** Two small words are then equal exactly when the values are,
  and every small value is below every big one, so the fast paths compare
  words and never look at a big number; native Lean keeps the same
  invariant.
- **Where:** `leanrt/src/nat.rs`: `of_big`, `of_u64`, `of_i64`,
  `of_i128`; the prelude fast paths' range checks (`l2r_int_of_i64`,
  `l2r_nat_of_u64`).
- **Remove only if:** never (a correctness invariant).

### Prelude functions take each `Nat` argument as its word once

- **What:** `l2r_nat_raw(n)` (`l2r_int_raw`) turns a handle into its word,
  which then owns the handle's reference. A small word owns nothing; a big
  word reaches exactly one owner on every path: `l2r_nat_of_raw`, a `_raw`
  slow path (which consumes its words), or `l2r_nat_drop_raw`.
- **Why:** No reference counting at all on the small path (Reussir has no
  borrowed parameters, so a handle passed on would be incremented and
  released around each test).
- **Where:** `prelude.rr`: the Nat and Int sections, string positions,
  array indices (`l2r_word_index_ok`), the generated `natarr`/`intarr`
  codecs; `leanrt/src/nat.rs`: the slow paths (`nat_add`, ... every
  small/big combination).
- **Remove only if:** Reussir gets borrowed parameters.

### Fast paths work on the encoded words

- **What:** On two small `Nat` words `x = 2m+1`, `y = 2n+1`: add is
  `x + (y - 1)`, small unless it carries out of the word; sub is
  `x - y + 1` (0 when `x < y`); `&&&`/`|||` act on the words directly,
  `^^^` is `(x ^ y) | 1`; `<`, `≤`, `==` compare the words; mul takes
  factors below 2^31 directly, else checks the high word (`umulh`);
  `/`, `%`, shifts and `pow` decode, compute and range-check. `Int`
  decodes its 32 bits, computes in `i64` (no overflow is possible) and
  re-encodes when the result is in `int32`. Anything else calls
  `leanrt::nat`.
- **Why:** Native Lean's small arithmetic is a tag test and the operation;
  so is this.
- **Where:** `prelude.rr`: `lean_nat_*`, `lean_int_*`, `l2r_int_val`.
- **Remove only if:** the encoding changes.

### `Nat.pow`'s fast path takes exponents below 2^32 only

- **What:** The inline path runs only when the exponent word is below
  2^33 (`y >> 33 == 0`); the slow path panics for a bigger exponent.
- **Why:** Lean panics ("Nat.pow exponent is too big") for an exponent
  above 2^32 - 1 whatever the base; a fast path that returned `1 ^ e` or
  `0 ^ e` first skipped the panic (found by `RtInternalPanic` while
  writing the change).
- **Where:** `prelude.rr`: `lean_nat_pow`; `leanrt/src/nat.rs`:
  `nat_pow`.
- **Remove only if:** never.

### Big numbers are laid out as Lean's `lean_mpz_object`

- **What:** `LBig = reussir_rt::rc::Rc<BigZ>`, allocated as a 24-byte
  `BigObj`: the 32-bit count (Reussir's, at offset 0), `m_cs_sz = 24`,
  `m_other = 0`, `m_tag = LeanMPZ` (250), written into the four bytes that
  are padding to Reussir, then GMP's `mpz_t`, whose limbs GMP allocates.
  The operations are GMP's `mpz_*` functions, in place when the first
  operand is unique.
- **Why:** C code can receive a big `Nat` with no conversion (ffi-c), and
  memory behaves as natively (bignum about 1.1x native, was 1.2-1.3x).
- **Where:** `leanrt/src/big.rs`: `BigObj`, `wrap`, `binop`, `op_ui`;
  `gmp.rs`.
- **Remove only if:** C interop is not needed. Differences from native:
  counts follow Reussir's convention (only Lean's single-threaded
  `m_rc > 0`), and the object comes from `mi_malloc`, so a C-side
  `lean_dec_ref_cold`/`lean_free_object` must go through lean2rr's shim.

### Literals: small below 2^63, big ones parsed from their decimal text

- **What:** A `Nat` literal below 2^63 is `l2r_nat_small(k)` (the word
  `2k+1`; `ArrayLits` recognizes it for literal tables); a bigger one is
  `l2r_nat_of_decimal_lstr(s)`, with `s` the decimal digits in the string
  literal table.
- **Why:** 2^63 is the small range. A nested arithmetic expression per
  limb overflowed rrc's stack at about 20000 digits and cost quadratic time
  (adv2 N1, fbf37e8).
- **Where:** `Lower/Values.lean`: `natLiteral`; `ArrayLits.lean`:
  `smallLit?`; `prelude.rr`: `l2r_nat_small`, `l2r_nat_of_decimal_lstr`;
  `leanrt/src/nat.rs`: `nat_of_decimal`.
- **Remove only if:** the encoding changes; the flat call is cheaper
  anyway. Plan [§5.4](../../translation-plan.md#54-let-return-literals).

### `Nat` and `Int` are FFI-boundary types

- **What:** `isBoundaryTy` counts `Nat`/`Int` as runtime handles: without
  the `nat-arrays` pass `Array Nat` is `RVec<Nat>` (one word per element);
  an `IO.Ref Nat` is a cell holding the handle, like any other reference
  (the prelude's `L2RNatRef`/`L2RIntRef` are gone).
- **Why:** They are counted handles now, which Reussir passes across the
  FFI boundary and keeps in cells (bug 19 only concerns `[value]`
  records).
- **Where:** `LowerBase.lean`: `isBoundaryTy`, `refType`.
- **Remove only if:** `Nat` stops being a counted handle.

### `ptrAddrUnsafe` and casts read a `Nat`/`Int` word as native does

- **What:** `ptrAddrUnsafe` of a `Nat` or `Int` is its word (the boxed
  scalar, or the big number's pointer); `unsafeCast` of a small `Int` to
  `Nat` keeps the word (the `Nat` of its 32 bits).
- **Why:** The representation is native's, so the answers are.
- **Where:** `prelude.rr`: `l2r_addr_nat`, `l2r_addr_int`, `l2r_int_word`,
  `l2r_int_cast_nat`; [identity.md](identity.md).
- **Remove only if:** never.

### Big-number counters for tests

- **What:** Built with `--cfg leanrt_count_bigs` (set through
  `L2R_LEANRT_RUSTFLAGS`, which gives leanrt its own build directory), a
  program prints the big numbers made and freed at exit.
  `tests/runtime/nat-alloc-check.sh` checks with them that every big
  number `RtNatStress` makes is freed exactly once and that `RtNatConst`'s
  big constants are made once, at two sizes.
- **Why:** Ownership of words is manual in the prelude; the counts catch a
  leak or a double free, and a constant rebuilt at every use (RV8N-01).
- **Where:** `leanrt/src/big.rs`: `count`; `scripts/l2r.py`:
  `LEANRT_FLAGS`; `tests/runtime/nat-alloc-check.sh`.
- **Remove only if:** never (test infrastructure; not compiled otherwise).

### `Nat.repr` of 0..127 shares one string per number

- **What:** The runtime keeps a table of the strings of 0 to 127, built on
  first use, and `l2r_nat_repr` returns a new reference to the shared one.
  With the optional pass `prelude-repr`, `Nat.repr`, `Nat.reprFast` and
  `Int.repr` call `l2r_nat_repr`/`l2r_int_repr` (GMP for big numbers).
- **Why:** Natively `Nat.reprFast` reads the closed term `Nat.reprArray`,
  so printing small numbers allocates nothing (adv4 PF4-04, ce60463). The
  Lean code also divides big numbers digit by digit (quadratic), and
  cloned `Nat.reprArray`'s once-cell for every number ≥ 128 (13% of the
  classic Sieve; runtime requests 12 and 27).
- **Where:** `leanrt/src/string.rs`: `repr_small`, `repr_small_init`;
  `leanrt/src/nat.rs`: `nat_repr`, `int_repr`; `prelude.rr`:
  `l2r_nat_repr`, `l2r_int_repr`; `Opt/PreludeRepr.lean`.
- **Remove only if:** the strings are the same either way; the pass and
  the table only save time and allocations. The runtime keeps the
  functions when the pass is off.

### Indices and positions are never big

- **What:** An index that is in bounds (a `Fin`, or after the bounds test
  of `get!`) or a position proved valid converts with
  `l2r_index_of_nat`, whose big case ends the program; a checked index is
  taken as its word once (`l2r_word_index_ok`). Where Lean's C code tells
  "not a scalar" apart from "out of range", the prelude does too: a big
  `Nat` (`lean_string_utf8_extract`), a big `Int` (`Float.scaleB`).
- **Why:** See
  [../ownership.md](../ownership.md#reads-take-their-container-owned-and-in-bounds-indices-end-on-a-big-index).
- **Where:** `prelude.rr`: `l2r_index_of_nat`, `l2r_word_index_ok`.
- **Remove only if:** see the linked entry.
