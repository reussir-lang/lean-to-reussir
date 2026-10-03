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
  a8fc2e2). Lean's encoding of the small values would also let C code
  written against `lean.h` take and return them unchanged (a big number,
  in lean2rr's own layout below, would be converted), but calling a
  program's C is not supported (the C FFI is parked:
  [../externs-ffi/c-ffi.md](../externs-ffi/c-ffi.md)).
- **Where:** `runtime/prelude.rr` (`struct Nat`, `struct Int`, the Nat and
  Int sections); `runtime/leanrt/src/nat.rs`; plan
  [§5.1](../../translation-plan.md#51-type-translation) ("One-word `Nat`
  and `Int`", which also weighs the alternatives).
- **Remove only if:** never for the one word; the exact encoding may
  change if a lean2rr encoding serves better (Lean-layout compatibility
  does not constrain lean2rr's layouts while the C FFI is parked) or
  Reussir gains a native tagged-integer type.

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

### Add and mul test "both small" on the parity of the sum

- **What:** `lean_nat_add` and `lean_nat_mul` compute `s = x + (y - 1)`
  and take the fast path when `s & x & 1` is 1 (both words odd: `s` is
  odd when `x` and `y` have the same parity), not when `x & y & 1` is.
- **Why:** With `x & y & 1`, LLVM pairs `y & 1` with the identical
  low-bit test of Reussir's `rc.inc` of `y` (patch 0050's guard; `y` is
  often a field just read out of a cell that is then released) and keeps
  it in a callee-saved register across the release calls in between. In
  cfold's `constFolding`, which recurses about 2^n deep without a tail
  call (8M frames at n = 23), that one register made the frame 96 bytes
  instead of 80. Measured on perf-cfold (max RSS of the program, KB/1024,
  n = 23): 1074 MB with `x & y & 1`, 946 MB with the parity test, 1000 MB
  before the one-word `Nat` (a684336), 1268 MB native; the regression was
  found by the regress-cc0 run (finding 1, bisected to cc0d43c). Each
  inlined add or mul is 1 to 2 instructions longer (computed before the
  test, the sum becomes `(x + y) - 1`, so the carry check needs a `cmp`
  instead of the flags of `adds`), but whole programs execute no more
  instructions: cfold 0.8% fewer, Bignum, Liasolver and a probe of
  small-`Nat` loops (collatz, sums, a two-field record) the same within
  run-to-run noise.
- **Where:** `prelude.rr`: `lean_nat_add`, `lean_nat_mul`.
- **Remove only if:** Reussir's guard stops sharing the low-bit test, or
  measurement shows the frames unaffected. The other binary operations
  keep `x & y & 1`; the same effect would show there as a larger frame
  of a recursive function using them.

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

### Big numbers are one block: a 16-byte header, then the limbs

- **What:** `LBig` is a pointer to one `mi_malloc` block: the 32-bit
  count (Reussir's, at offset 0), 4 reserved bytes (`flags`, 0), the signed
  size (GMP's convention: the limbs in use, negated for a negative value;
  no zero top limb), the capacity, then the limbs inline (`mi_good_size`
  rounds the capacity up to the allocator's size class). The frequent
  operations (add, sub, mul, div/mod in the four Lean flavours, shifts)
  call GMP's `mpn_*` functions on the limbs; bitwise operations and
  comparisons are loops over them. A result goes into a unique operand
  whose block has room for it (computed in place where GMP allows, else
  in scratch limbs, on the stack up to 32, and copied), else into a fresh
  block; a block grows (`mi_realloc`) only when a result computed in place
  outgrows it (a carry), and a result that leaves most of its block unused
  (more than 32 limbs and three quarters) moves to a block of its size
  (`shrink`; review RVPB-01: `(2^128000 + i) >>> 127872` kept a 2046-limb
  block for a 3-limb result, 18x native peak memory for 5000 of them). The rare
  operations (`pow` of a big base, `gcd`, parsing, printing) give GMP's
  `mpz_*` functions read-only views (`MPZ_ROINIT_N`) and copy the result
  out of a temporary `mpz_t`. A power of two raised to `e` is one shifted
  block (`big::pow2`), and `x ^ e` of a word base reads `x` through a
  view of a stack limb (`big::u64_pow`).
- **Why:** Native Lean's `lean_mpz_object` is a header and an `mpz_t`
  whose limbs GMP allocates separately (glibc's `malloc`): two allocations
  and two frees per big number, two dependent loads to reach the limbs,
  and 56 bytes for a two-limb number (24 + glibc's 32-byte minimum chunk)
  where one block takes 32. lean2rr's layouts serve its own programs
  first; a big number handed to C code would be converted at that boundary
  (the C FFI is parked). Measured on branch perf-big (allocation counts,
  and peak RSS without transparent huge pages): a fresh big number is one
  `mi_malloc` (was an object and one or two glibc calls); a million live
  two-limb numbers peak at 49.5 MB (was 65.2; native 74.3); `fib 20000`
  grows its numbers with 22 `mi_realloc`s (was 443 `realloc`s of GMP's
  limbs). The classic Liasolver makes 21.3M blocks, 0.2M grows and no
  glibc calls (was 16.8M objects, 17.8M `malloc`s and 12.6M `realloc`s);
  its peak RSS and Bignum's stay within a few hundred KB of before (freed
  pages mimalloc purges after a delay), below native's. Reusing an
  operand without room would copy limbs that are about to be overwritten
  (the capacity is the block's usable size, so `mi_realloc` moves it).
  The `mpn` aliasing rules relied on (a result over a source exactly for
  `add`/`sub`/`add_1`/`sub_1`/`mul_1`/`divrem_1`, shifts toward their
  direction, separate memory for `mul`, `sqr`, `tdiv_qr`) are GMP's
  documented ones, also used by its `mpz` code.
- **Where:** `leanrt/src/big.rs`: `Obj`, `alloc`, `reserve`/`grow`,
  `set`/`shrink`, `either`, `add_mag`, `sub_mag`, `mul`, `div`, `bitwise`,
  `view`, `of_mpz`; `gmp.rs`; unit tests `big::tests` (`against_mpz`,
  `mixed_ownership`, `large_mixed` check every operation on unique,
  shared and roomy operands against GMP's `mpz` functions; `retention`
  checks the shrink).
- **Remove only if:** another layout serves lean2rr better. Differences
  from native: counts follow Reussir's convention, the block comes from
  `mi_malloc`, and C code reading a big number through `lean.h` would need
  a converted `lean_mpz_object`.

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
  program prints the big numbers made and freed, and the blocks grown by
  a carry, at exit.
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
  `Nat` (`lean_string_utf8_extract`, where it counts as `SIZE_MAX`, as
  natively since Lean 4.34), a big `Int` (`Float.scaleB`).
  `lean_string_utf8_extract_fast` (`String.extract`, new in Lean 4.34)
  takes its positions, valid by proof, with `l2r_index_of_nat`.
- **Why:** See
  [../ownership.md](../ownership.md#reads-take-their-container-owned-and-in-bounds-indices-end-on-a-big-index).
- **Where:** `prelude.rr`: `l2r_index_of_nat`, `l2r_word_index_ok`,
  `lean_string_utf8_extract`, `lean_string_utf8_extract_fast`; test
  `RtString`.
- **Remove only if:** see the linked entry.
