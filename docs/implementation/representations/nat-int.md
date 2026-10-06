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
  turn an in-range big result back into its word. `LInt::of_big` is the
  one place where a big `Int` handle is made; lean-runtime's rules do not
  normalize (their `Int` may hold any value in either form), and leanrt
  turns every rule's result into a word through `of_int_view`
  (`LInt::of_i64` for a word, `LInt::of_big` for a big number). The
  prelude makes small words only for values it has range-checked
  (`l2r_int_of_i64`) or knows to be in range (`l2r_int_small`); any other
  word is a copy of an existing `Int`. The producers of an `Int` (the
  audit of switch step 10; each normalizes as said):
  - leanrt: `LInt::small` (a value in range), `LInt::of_i64` and
    `int_big_of_i64` (a range test, then `of_big`), `LInt::of_big`, and
    `of_int_view`, through which every slow path returns (`int_neg`,
    `int_add`, `int_sub`, `int_mul`, `int_div`, `int_mod`, `int_ediv`,
    `int_emod`, `nat_to_int`, `nat_neg_succ`); lean-runtime's rules and
    `GInt`'s word methods only give `of_int_view` their results;
  - the prelude's fast paths: `lean_int_neg`, `lean_int_add`, `_sub`,
    `_mul`, `_div`, `_ediv` and `_emod` through `l2r_int_of_i64` (two
    small values in `i64` cannot overflow), `lean_int_mod` and
    `lean_int_emod` through `l2r_int_small` (a remainder by a small
    divisor, or zero) or the dividend's own word (`x % 0`);
  - conversions: `lean_nat_to_int` (`Int.ofNat`, and `unsafeCast` from
    `Nat`, `Lower/Conv.lean`) reuses the word of a small `Nat` below 2^31,
    else `nat_to_int`; `lean_int_neg_succ_of_nat` (`Int.negSucc`, also
    `Int.negOfNat` and so `String.toInt?`); `lean_int8_to_int`,
    `lean_int16_to_int`, `lean_int32_to_int` and `lean_int_to_int` (an
    `int32`), `lean_int64_to_int_sint` and `lean_isize_to_int` (through
    `l2r_int_of_i64`; also `IO.FS.Metadata`'s times, `Lower/Externs.lean`:
    `metadataOf`); `l2r_int_of_word` (`unsafeCast` of a word, its low 32
    bits); `Float.frExp`'s exponent and the shim's clock
    (`l2r_shim_realtime_nanos`, behind `L2RShim`'s `currentTime`) through
    `l2r_int_of_i64`; `L2RShim`'s `signalNext` through `Int.ofNat`;
  - literals: none (Lean's LCNF has no `Int` literal; constants are
    `Int.ofNat`, `Int.negSucc` and `Int.neg` calls, recomputed the same way
    as cheap constants);
  - `zeroValue` (`Lower/Conv.lean`): `l2r_int_small(0)`; a `Box` read at
    `Int` (`genUnbox`): the `Int` variant's handle, a `Nat` through
    `lean_nat_to_int`, a word through `l2r_int_of_word`, the unit through
    `zeroValue`;
  - copies of existing words: an `Array Int`'s elements (`tagvec`), a
    record's or a `Box`'s field, a once-cell's value, a reference's or a
    task's value; arrays of another element type are converted element by
    element (`vecConv`), never retyped between `Nat` and `Int`
    (`retypableAux`).
  In builds with debug assertions, `LInt::of_big` checks that a big
  number is in its one form (no zero top limb, no negative zero: what
  `fits_i64` and its range test read), and `int_view` (every slow path's
  read of a big `Int`, comparisons included) that, and that no big `Int`
  is in the small range; leanrt's unit tests run with them
  (`tests/runtime/leanrt-unit.sh`).
- **Why:** Two small words are then equal exactly when the values are,
  a small value never equals a big one, and every small `Nat` is below
  every big one, so the fast paths compare words and never look at a big
  number; native Lean keeps the same invariant.
- **Where:** `leanrt/src/nat.rs`: `of_big`, `of_u64`, `of_i64`,
  `of_nat_view`, `of_int_view` (lean-runtime's results),
  `big_trimmed`, `big_int_normalized`, `int_view`; the prelude fast paths' range checks
  (`l2r_int_of_i64`, `l2r_nat_of_u64`); unit tests
  `nat::tests::int_results_are_normalized` (every `Int` slow path at the
  range's edges) and `nat::tests::unnormalized_big_int_is_caught`;
  runtime test `RtIntSmallBigEq`.
- **Remove only if:** never (a correctness invariant).

### `Int` equality of a small and a big word needs no call

- **What:** `lean_int_dec_eq` compares two small words directly (as
  before); for a small and a big word it answers `false` at once and
  releases the big one (the pair's one even word); only two big words
  call `leanrt::nat::int_eq`.
- **Why:** By normalization a big `Int` is never in the small range, so it
  never equals a small one. The mixed pair went to `int_eq` and
  lean-runtime's `compare_slow`: in an instruction-count profile of the
  classic programs, 120,000 calls in liasolver, most of them comparisons of a big value with a small one.
  Without the call, liasolver runs 3.1% fewer instructions (switch step
  10, cachegrind, size 16). The order (`<`, `≤`, `compare`) still calls
  leanrt for a mixed pair (the answer is the big number's sign).
- **Where:** `prelude.rr`: `lean_int_dec_eq`; runtime test
  `RtIntSmallBigEq` (86 values at and around the range's edges, from every
  operation and conversion, and the equality and order of every pair:
  with a result left big in the small range, the test fails).
- **Remove only if:** never (speed only, but it depends on normalization
  above; `Nat` equality keeps its call for a mixed pair: its producers
  were not audited).

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
  `leanrt::nat`, which runs lean-runtime's rules (next entry).
- **Why:** Native Lean's small arithmetic is a tag test and the operation;
  so is this.
- **Where:** `prelude.rr`: `lean_nat_*`, `lean_int_*`, `l2r_int_val`.
- **Remove only if:** the encoding changes.

### The slow paths are lean-runtime's rules on lean2rr's numbers

- **What:** Every `leanrt::nat` slow path (`nat_add`, ..., `int_emod`,
  `nat_to_int`, `nat_neg_succ`, `nat_repr`, `int_repr`) views its owned
  words as lean-runtime's `sem::nat::Nat`/`sem::int::Int` (`Small` for an
  odd word, `Big` of a `big::GNat`/`big::GInt` for an even one:
  `nat_view`, `int_view`), calls the rule (`sem::nat::add`, ...), turns the
  result back into a normalized word, and ends the process with the
  rule's `InternalPanic` (`lean_internal_panic`). `GNat` and `GInt` are
  `LBig` as lean-runtime's `BigNat`/`BigInt` traits: each method is one of
  `big.rs`'s operations (the four divisions are `big::div`'s fused `mpn`
  ones, not the traits' default from `tdiv_rem`). When one operand is a
  word and the other big, the rules call `BigInt`'s word methods
  (`add_i64`, `i64_add`, `sub_i64`, `i64_sub`, `mul_i64`, `i64_mul`,
  `tdiv_i64`, `tmod_i64`, `ediv_i64`, `emod_i64`, `div_exact_i64`;
  lean-runtime perf-2, switch step 10), which `GInt` overrides with
  `big::add_limb` (`mpn_add_1`/`mpn_sub_1`), `mul_limb` (`mpn_mul_1`) and
  `div_limb` (`mpn_divrem_1`, `mpn_mod_1`) on the big operand's limbs, in
  its block when it is unique: no block for the word (the trait's
  defaults make one with `from_i64`). The big operand may be any value,
  zero (no limb) included, which `add_limb` and `div_limb` answer apart
  (`mpn_add_1` and `mpn_sub_1` need a limb: a zero operand would give 0
  instead of the word). `big::MAX_BITS`, the
  largest result the rules ask for, is `(INT_MAX - 5) * 64` bits: GMP's
  `mpz_t` (and a block) holds `INT_MAX` limbs, and `mpz_pow_ui`, the one
  operation whose result GMP allocates, asks for at most
  `bit_len(a) * e / 64 + 5` limbs (`mpz/n_pow_ui.c`: the odd part's bits
  times `e`, 5 limbs of margin, and the zero limbs of the power of two).
  The inline fast paths, `LBig`'s layout and its GMP kernels are
  lean2rr's, unchanged.
- **Why:** One runtime for both translators (owner decision; shared-runtime
  step 2): the rules (zero divisors, truncation, rounding, the shift and
  exponent limits and the size of a big result) are written once, in
  lean-runtime, and checked by its 3306 `Nat`/`Int` rows through lean2rr
  (`tests/runtime/rows-check.sh`). They lift Lean's limits where the
  result can be computed (LB-04, LB-11, LB-12; plan §10) and end at once
  with `INTERNAL PANIC: out of memory` above `MAX_BITS`, where native's GMP
  raises SIGFPE (LB-05). The step changed no generated code: the classic
  corpus's `.rr` differs only in the prelude's panic textures and two
  renamed helpers, and the machine code of every Reussir function of
  Cfold, Sieve and Bignum is the same but for the targets of those calls.
- **Where:** `leanrt/src/nat.rs`: `nat_view`, `int_view`, `ok`, the slow
  paths; `leanrt/src/big.rs`: `GNat`, `GInt`, `MAX_BITS`, `bit_len`,
  `trailing_zeros`, `add_limb`, `div_limb`; unit tests
  `nat::tests::lifted_limits`, `big::tests::max_bits`,
  `big::tests::trait_views`, `big::tests::word_methods_match_defaults`
  (every word method against the trait's default, on big operands at the
  word ranges' edges and zero, unique and shared, and words at `i64`'s
  edges); runtime tests `RtLiftedLimits`, `RtInternalPanic`,
  `RtIntSmallBigEq`.
- **Remove only if:** lean2rr stops using lean-runtime.

### A big `Int` in the `i64` range is computed as a word

- **What:** The slow paths of `Int`'s arithmetic and comparisons
  (`int_add`, `int_sub`, `int_mul`, `int_div`, `int_mod`, `int_ediv`,
  `int_emod`, `int_nat_abs`, `int_cmp`, `int_eq`) view each operand with
  `int_view_narrow`: a big number whose value fits `i64` (`big::fits_i64`:
  no limb, or one limb with a magnitude below 2^63, or exactly 2^63 when
  negative) is released and viewed as a word
  (`sem::int::Int::Small`). With both operands words, lean-runtime's rule
  takes its word path (`checked_*` in `i64`, else the `*_small` helpers in
  `i128`), and `of_int_view` normalizes the result once: a word in the
  `int32` range, else a new block. The other paths (`int_neg`, `int_repr`,
  the conversions) keep `int_view`.
- **Why:** lean2rr's big `Int`s are the values outside the `int32` range,
  most of them one limb. Before, a word and such a number took the rule's
  big path: the size test (`bit_len`), the word method (`mul_limb`,
  `add_limb`, `div_limb`) on the limbs, the trim of the result, and the
  range test of `LInt::of_big`, about 160 instructions for a product. The
  rules take either form for any value (`sem::int::Int`), so the results
  are the same. Switch step 12: liasolver 6.5% fewer instructions, its
  runtime library's own instructions 24% fewer. The block of a unique
  operand is no longer reused for the result: a big result is a new
  block, which mimalloc takes from the operand's freed one.
- **Where:** `leanrt/src/nat.rs`: `int_view_narrow` and the slow paths
  above; unit test `nat::tests::narrowed_operands` (every operation on
  operands at the `int32` and `i64` edges and beyond, unique and shared:
  a shared operand keeps its value and gives up one reference); runtime
  test `RtIntWordBand`.
- **Remove only if:** the small `Int` range becomes `i64` (then no big
  number fits `i64`).

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
  2^33 (`y >> 33 == 0`); a bigger exponent goes to lean-runtime's rule
  (`sem::nat::pow`), which computes `0 ^ e` and `1 ^ e` for any exponent
  and a bigger base's power while it fits `big::MAX_BITS`, and ends with
  Lean's `Nat.pow exponent is too big` above it.
- **Why:** Native Lean panics ("Nat.pow exponent is too big") for an
  exponent above 2^32 - 1 whatever the base, which lean-runtime lifts
  where the result can be computed (LB-11); the fast path was written
  when lean2rr reproduced the panic (a fast path returning `1 ^ e` first
  skipped it, found by `RtInternalPanic`), and the hot path stays as it
  is.
- **Where:** `prelude.rr`: `lean_nat_pow`; `leanrt/src/nat.rs`:
  `nat_pow`.
- **Remove only if:** the bound may go (the slow path is right for every
  exponent) once a timing session shows the inline path unaffected.

### Big numbers are one block: a 16-byte header, then the limbs

- **What:** `LBig` is a pointer to one `mi_malloc` block: the 32-bit
  count (Reussir's, at offset 0), 4 reserved bytes (`flags`, 0), the signed
  size (GMP's convention: the limbs in use, negated for a negative value;
  no zero top limb), the capacity, then the limbs inline (the capacity
  is rounded up to the allocator's size class, `alloc::good_size`, see
  [arrays.md](arrays.md#a-blocks-capacity-is-mimallocs-size-class-without-a-call-up-to-64-bytes)).
  The frequent
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
  block (lean-runtime's `nat::pow` asks for `1 << (j e)`, `big::nat_shl`),
  and `x ^ e` of a word base raises a one-limb block (`big::nat_pow`).
  Both start from a one-limb block of the base (`BigNat::from_u64`), freed
  at once: one small block more per big power of a word than before the
  switch to lean-runtime's rules (`big::pow2` and a stack view of the
  limb), since its traits have no word-base power (RtNatStress, before its
  extension in review RST2-01, made 18900 big numbers at size 300, was
  18600; peak memory unchanged; lean-runtime request AR-3 would let the
  backend build them directly).
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
  `Int.repr` call `l2r_nat_repr`/`l2r_int_repr`: the digits are
  lean-runtime's (`sem::repr::decimal_u64_bytes` into a stack buffer for a
  word, as `lean_string_of_usize`; `sem::nat::write_decimal` and
  `sem::int::write_decimal` for a big number, GMP's `mpz_get_str`).
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
  of `get!`) or a position proved valid is never a big `Nat`. A read takes
  it as its word (`l2r_word_index_ok`, `l2r_array_get_word`): a big one
  falls into the read's failing branch, unreachable code
  (`l2r_index_fail`; `leanrt::index_word` inside the string reads
  `get_fast`/`next_fast`); an update converts it with `l2r_index_of_nat`,
  whose big case ends the program. Where Lean's C code tells "not a
  scalar" apart from "out of range", the prelude does too: a big `Nat`
  (`lean_string_utf8_extract`, where it counts as `SIZE_MAX`, as natively
  since Lean 4.34; the `Pos.Raw` reads, `l2r_pos_of_word`), a big `Int`
  (`Float.scaleB`). `lean_string_utf8_extract_fast` (`String.extract`,
  new in Lean 4.34) takes its positions, valid by proof, with
  `l2r_index_of_nat`.
- **Why:** See
  [../ownership.md](../ownership.md#reads-give-their-reference-up-first-for-a-view).
- **Where:** `prelude.rr`: `l2r_index_of_nat`, `l2r_word_index_ok`,
  `l2r_array_get_word`, `l2r_index_fail`, `l2r_pos_of_word`,
  `lean_string_utf8_extract`, `lean_string_utf8_extract_fast`;
  `leanrt/src/lib.rs`: `index_word`; tests `RtString`, `RtArrayReadViews`.
- **Remove only if:** see the linked entry.
