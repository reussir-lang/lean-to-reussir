# `Nat` and `Int`

Paths: `runtime/prelude.rr`, `runtime/leanrt/src/`, and
`lean2rr/LeanToReussir/` for lean2rr's files.

A `Nat` and an `Int` are Reussir's built-in integers (rcgmp), lean2rr's one
representation of them since clean-integration D8 (2026-10-26). Until then
`--int-backend` (scripts: `L2R_INT_BACKEND`) also offered `leanrt`, Lean's
own one-word encoding with leanrt's big numbers, the default until
2026-10-25 (its history entry below); `--int-backend rcgmp` is still
accepted and does nothing, `--int-backend leanrt` and
`L2R_INT_BACKEND=leanrt` are refused with a message.

### History: leanrt's own representation (until 2026-10-26)

- **What:** Until clean-integration D8 a `Nat` or `Int` could also be one
  word in Lean's own encoding (`--int-backend leanrt`, the default until
  2026-10-25): an odd word a small value (`lean_box(n)` for a `Nat` below
  2^63, `lean_box((unsigned)(int)i)` for an `Int` in the `int32` range),
  an even word an owned pointer to leanrt's big number, one `mi_malloc`
  block with a 16-byte header and the limbs inline, computed by GMP's
  `mpn` functions. Reussir counted the handles of the opaque types
  `leanrt::nat::LNat`/`LInt` only for even words (local patch 10-a,
  `tagged`, which the box type `LAny` still uses). The prelude's fast paths
  computed on the words; every slow path was lean-runtime's rule
  (`sem::nat`, `sem::int` over its `BigNat`/`BigInt` traits) on leanrt's
  numbers, which refused every result above `MAX_BITS` (LB-05); a small
  range value was always a word (normalization); test builds counted the
  big numbers (`--cfg leanrt_count_bigs`, `tests/runtime/nat-alloc-check.sh`).
  The prelude kept both representations in blocks marked
  `// @int-backend leanrt` and `// @int-backend rcgmp`, of which lean2rr
  kept the selected one.
- **Why it went:** rcgmp is Reussir's own interface, which its maintainer
  asks lean2rr to use (clean-integration plan, D8): one representation, no
  local encoding of lean2rr's in the prelude, leanrt or the lowering. Every
  runtime test gave native's output under both (combined gate 29).
- **Where:** the last commit with it, dev 3e03d989: `runtime/leanrt/src/`
  `big.rs`, `nat.rs`, `gmp.rs`, the prelude's `@int-backend leanrt` blocks,
  and this file's entries on it (the encoding, normalization, the slow
  paths, the block layout and its GMP kernels, the counters).
- **Remove only if:** never (history).

### Reussir's built-in integers (rcgmp)

- **What:** A `Nat` and an `Int` are Reussir's built-in integers
  (`core::num::Nat`/`Int`, rcgmp: an immediate in [-2^61, 2^61) or a
  counted heap integer; clean-integration step D, the only representation
  since D8).
  - The prelude's Nat and Int sections compose Lean's rules (lean-runtime's
    `sem::nat`, `sem::int`) of Reussir's operators and
    `core::intrinsic::bigint`: `+`, `-` (truncating on `Nat`), `*`,
    comparisons, `& | ^`, `<<`/`>>` (a nonnegative `i64` amount),
    `/`/`%` behind a zero test (`n / 0 = 0`, `n % 0 = n`), `divsi_exact`,
    `edivsi`/`emodsi`, `log2i`, `gcdi`, `absi`, `ipowi`, `as` casts (the low
    bits of the two's complement), `Int::NegSucc`. A value is tested and
    converted with `trunci_overflow`, never by its encoding.
  - `Nat.pow` and `Nat.shiftLeft` test the result's size first, as
    lean-runtime's rules do, against `leanrt::rcgmp::MAX_BITS` (the limit
    of lean-runtime's rules, GMP's: `INT_MAX` limbs less `mpz_pow_ui`'s
    margin of 5 limbs, (2^31 - 6) × 64 bits): above it the process ends
    with native's message (`l2r_internal_panic` codes 6 and 7 for an
    exponent or shift of 2^32 or more, else 4, out of memory).
    `x % 2^w` (`l2r_nat_truncate_bits`) is rcgmp's `floormod2expi`, and
    the divisions are Lean's modes (`divsi_lean`, `remsi_lean`,
    `edivsi_lean`, `emodsi_lean`: quotient 0 and remainder `x` for a zero
    divisor), both through local Reussir patch R1.
  - Index words: the prelude's string and array functions read a `Nat`
    index, position or capacity through its word (`l2r_nat_raw`,
    `l2r_word_index_ok`, ...), defined on an index word: the value below
    2^63, `u64::MAX` from there, owning nothing. The functions that need a
    big position's value (`String.Pos.Raw.next`/`prev`) or the native word
    (`l2r_addr_nat`, `l2r_addr_int`) and `l2r_int_sat_i64` read the
    integer itself (`trunci_overflow`).
  - The index and position reads truncate to `i64` (`trunci_overflow` to
    `(i64, bool)`, the bits then as `u64`): an rcgmp immediate always fits
    `i64`, so their immediate path has no overflow test. The bits equal a
    `u64` truncation's; the flag differs only for a value in [2^63, 2^64),
    which each of these reads treats as one from 2^64 (out of range, the
    big case) or does not read (`memcmp`, `get_byte_fast`: the low 64
    bits). `l2r_nat_sat`, `l2r_replicate_len` and `lean_nat_pow` keep the
    `u64` truncation: they tell [2^63, 2^64) apart.
  - Sizes become a `Nat` through a mask to 61 bits (`l2r_nat_size`): LLVM
    then knows that the value is an rcgmp immediate, so `as Nat` has no
    range test and no promotion call. For `String.utf8ByteSize`,
    `String.length`, the sizes of `Array`, `ByteArray` and `FloatArray`
    (below 2^48: memory), and the results of `String.Pos.Raw.next`,
    `next'` (`next_fast`) and `prev` for a position below 2^60. From 2^60
    a position is past the end of every string, where `next` and `prev`
    give it plus or minus one, computed on the `Nat` (`p + 1`, `p - 1`),
    which a mask would cut (test `RtNatPosEdges`); for `next'` a position
    there is unreachable (its proof keeps it below the size). Run 13's rcgmp profile measured the two changes by
    hand: L17 -801 million instructions (sizes), Z01c -979 million (sizes)
    and -733 million (truncation).
  - Reads at an index word (`_w`): `l2r_nat_index(n)` gives `n`'s value
    below 2^63 and `u64::MAX` from there, and releases `n`;
    `lean_array_fget_w`, `lean_array_get_w`, `lean_byte_array_fget_w`,
    `lean_byte_array_get_w`, `lean_string_utf8_get_w`, `_get_fast_w`,
    `_next_fast_w` and `_at_end_w` read at such a word (`u64::MAX` is out
    of range, unreachable code for `fget`, `get_fast` and `next_fast`). `l2r_nat_index` is one truncation to `i64` and one
    select (`if w { u64::MAX } else { k }`): the flag is set exactly from
    2^63, since rcgmp tests the signed range and a `Nat` is never
    negative. With the earlier conversion (`l2r_pos_of_nat`, removed in
    D8: its tests of bit 63, in `l2r_nat_raw` and on its result), about 5
    more instructions per read stayed after the immediate and big paths
    joined (X07 +25%, L17 +10%, Z01c +6.6% instructions with the lowering's
    `_w` reads). The lowering computes
    the word before it passes the container, so that a big index's release
    never comes between the container's increment and the read's decrement
    (the lowering's entry below). `lean_array_fget_as_w` and
    `lean_array_get_as_w` are the reads at a type
    (`boxWordRead?`) of `lean_array_fget_w` and `lean_array_get_w`.
  - A read whose position or index a proof keeps in range (`get'`,
    `next'`, at an index word or at a `Nat`) tests it inside the read,
    after the read's release decision (`l2r_string_get_fast_k`,
    `l2r_string_next_fast_k`): tested in
    front of it, the unreachable branch's call came between the caller's
    increment of the string and the read's decrement, and LLVM kept both
    (2 stores and about 4 instructions per character of a `String.map`).
    `l2r_index_of_nat` (`fset`, `fswap`) and `String.set` take the index
    with one test: the flag of the truncation to `i64`, set exactly from
    2^63 (through `l2r_nat_raw`, bit 63 was tested twice). Run 14's
    profile: X07 300.1 to 275.1 million instructions (-8.3%), L17 14.76 to
    14.31 G (-3.1%).
  - Updates at an index word: `lean_array_fset_w`, `lean_byte_array_fset_w`
    and `lean_array_fswap_w` are `Array.set`,
    `ByteArray.set` and `Array.swap` at words: a word from 2^63 is
    unreachable code (`l2r_index_of_word`, as `l2r_index_of_nat`), another
    word at or above the size the update's `index_bug`. With `fget_w`, its
    read at a type and `ByteArray`'s `fget_w`, they return only for words
    below the size. After one returned, `l2r_nat_of_index(k)` is the index
    as a `Nat`: the word masked to 60 bits (`k` is below the size, far
    below 2^60, the mask's bound: sizes are bounded by the address space),
    so LLVM knows that the value is an immediate and that a small
    constant added to it stays one (no tag test, no overflow path; the
    61-bit mask of `l2r_nat_size` leaves `i + 1` an overflow path, because
    2^61 is past the immediates). The lowering's entry below
    (`rebindIndex`). The lowering calls these for every `fset`, `fswap`
    and `ByteArray` `fset`, so `l2r_index_of_nat` serves the other
    callers (`FloatArray.set`, `String.extract`'s fast path).
  - Boxes stay Lean's: a `Nat` below 2^63 and an `Int` in the `int32` range
    are immediates (`l2r_any_of_nat`, `l2r_any_of_int`, tested in Reussir
    code); a bigger value is a leanrt cell of kind 1 or 2 that holds an
    rcgmp reference (`leanrt::any::of_mpz`, `mpz_of`; `release_kind`
    releases it). `l2r_any_as_nat`/`_int` decode an immediate in Reussir
    code. The lowering calls these four for the box kinds 1 and 2 (a
    generic texture at `Nat` gets the raw handle, so it cannot test a
    small value).
  - A big value's cell takes the owned handle: `l2r_any_of_nat` and
    `l2r_any_of_int` call the generic `l2r_any_of_big<Nat>`/`<Int>` on
    their heap path, where Reussir passes `reussir_rt::rcgmp::Mpz` (local
    patch R2), and `leanrt::rcgmp::box_owned` puts it in the cell as it is:
    no retain in leanrt and no release after the call. Until 2026-10-25 a
    non-generic texture got the borrowed handle, retained it, and Reussir
    released it after the call (L10, run 14: 2.3% of its instructions,
    rcgmp/leanrt 1.056 to 1.032). Tests `RtNatBoxBig` (with
    tests/runtime/int-backend-check.sh) and `RtBoxBigReuse` (peak memory).
  - leanrt's part is `leanrt::rcgmp`: the box cells
    (of `reussir_rt::rcgmp::Mpz`, the owned handle that local Reussir patch
    R2 renders at polyffi type arguments, re-exported), decimal text
    (`repr`), `replicate_len`. It calls
    rcgmp's public C API only. A generic box texture at `Mpz`
    (`l2r_any_of<Nat>`) ends the program with a message
    (`generic_mpz_box`): it cannot keep small values immediates.
  - rcgmp needs Reussir's local patches R1 and R2:
    `scripts/l2r.py` checks for them (`RCGMP_REUSSIR_PATCHES`). With R2, a
    typed `Array Nat`, a once-cell constant and every generic texture at
    `Nat` hold `Mpz` values, counted by rcgmp's C calls (test
    `RtNatGenericBig`).
  - rrc needs Reussir's core package for `Nat` and `Int`: `scripts/l2r.py`
    builds its interface once per Reussir checkout (`core_interface`) and
    compiles the program in package mode (`--package-name prog --extern
    core=...`).
  - GMP is linked statically, as natively, by its place on the link line:
    `scripts/l2r.py` passes Reussir's integer runtime
    (`libRCGMPRuntime.a`, which calls GMP) with `--link-lib`, under a
    name of its own (`libl2r_rcgmp.a`, `rcgmp_runtime_link`: rustc refuses
    a library named twice), before the toolchain's `libgmp.a` (or
    `L2R_GMP`). rrc links that runtime itself, but after every
    `--link-lib` and followed by `-lgmp`: with GMP's archive first, GNU ld
    took nothing from it, and `-lgmp` resolved the runtime's GMP symbols
    in the first `-L` directory with a libgmp, from a `libgmp.so` where
    there was one (with `L2R_GMP=/usr/lib/aarch64-linux-gnu/libgmp.a` the
    executable needed `libgmp.so.10`; review of D8). `tests/runtime/run.sh`
    fails an executable that needs a `libgmp`.
  - Differences from native Lean (allowed by the functional equivalence
    contract; review R1):
    - `Nat.add`/`mul` and the `Int` operations do not test lean-runtime's
      `MAX_BITS` (only `pow` and `shiftLeft` do, where small operands make
      a huge result; LB-05). A larger sum or product is computed (rcgmp's
      sizes are `size_t`, and it calls GMP's `mpn` functions, so mpz's
      limit of `INT_MAX` limbs, where native's GMP raises `SIGFPE`, does
      not apply), or the process ends as its allocation does: rcgmp's
      heap integer through reussir-rt's hook (`rcgmp_allocate`,
      `__reussir_allocate`: `Panic: allocation failed`, then `abort`) or
      GMP's scratch through GMP's own allocator (`GNU MP: Cannot allocate
      memory (size=N)`, then `abort`), exit 134, never a wrong result.
      Checked on 2026-10-26: `x * (x + 2)` and `x * x` for
      `x = 2^(2^28) + 1` under `ulimit -v` end with each message, exit
      134, and with enough memory give the right value. Reaching
      `MAX_BITS` by a sum or product needs an operand of 2^36 bits (about
      8.6 GB).
    - `Nat.divExact`/`Int.divExact` are computed as `div` (as natively),
      not with rcgmp's exact division, whose immediate path is LLVM's
      `sdiv exact`: poison for a false proof.
    - An immediate of 2^31 or more boxed at another type (a `Nat`, a
      `UInt32`) and unboxed at `Int` gives the `Int` of its low 32 bits,
      normalized: `==` with that value is true and `ptrAddrUnsafe` is its
      `int32` word, where native Lean keeps the raw word (`==` false).
      Only a program that casts gets there.
    - `ptrAddrUnsafe` of a big value is its handle's word (a heap
      address, or rcgmp's immediate for an `Int` below 2^61 in magnitude),
      distinct per value. A boxed big value is one leanrt cell per box: two
      boxes of one integer have different addresses and are both
      exclusive (natively the box is the number object).
    - `dbgTraceIfShared` (a debug message) follows rcgmp's immediates, not
      Lean's: a `Nat` in [2^61, 2^63) is a heap value here and can be
      reported shared (a literal such as 2^61 always is: an immortal object),
      where natively it is a scalar; so can a computed value equal to a big
      literal (`2^70 + k` at `k = 0`, natively a new object); an `Int` with
      |x| in [2^31, 2^61) is an immediate here and never reported, where
      natively it is an object.
    - A boxed `Int` in [2^32, 2^62) or [-2^62, -2^31) is an immediate
      (`2v + 1`, `l2r_int_box_wide`; natively an object, its word an
      address): an `int32` value keeps Lean's scalar, and a box word read
      at `Int` decodes as the `int32` pattern below 2^32 and as `2v + 1`
      from there.
- **Why:** Reussir's maintainer asks lean2rr to use Reussir's interface
  instead of its own encodings (clean-integration plan, step D); rcgmp
  landed upstream on 2026-10-24. The default since 2026-10-25 (combined
  gate 25 green under both representations; timing run 14: per-case
  geomean rcgmp/leanrt 0.990), the only representation since D8.
- **Where:** `runtime/prelude.rr` (the Nat and Int sections);
  `runtime/leanrt/src/rcgmp.rs`, `any.rs` (`of_mpz`, `mpz_of`,
  `release_kind`, `generic_mpz_box`); `scripts/l2r.py` (`INT_BACKEND`,
  which refuses `leanrt`, `core_interface`, `check_rcgmp`,
  `rcgmp_runtime_link`); `tests/runtime/leanrt-unit.sh`, `run.sh` (the
  `libgmp` test).
- **Remove only if:** never while lean2rr builds on Reussir (its own
  interface for big integers).

### The lowering

- **What:** lean2rr's side of Reussir's built-in integers (clean-integration
  step D; plan STEP-D-LOWERING rows 3 to 14, 18, 19).
  - **Options.** None chooses the representation. `--int-backend rcgmp`
    is accepted and does nothing, `--int-backend leanrt` is refused
    (`Main.lean`; scripts/l2r.py refuses `L2R_INT_BACKEND=leanrt`).
    `--rcgmp-type-args` is accepted and ignored: until 2026-10-25 it chose
    the lowering of `Nat` and `Int` at type arguments, and without it a
    lowering for measurements (guard mode) kept them out of type
    arguments, with a check of its own (`Emit/IntBackendCheck`). A `Nat`
    or `Int` at a type argument of a generic FFI function is Reussir's
    owned handle (local patch R2, which scripts/l2r.py requires).
  - **History.** Until D8 (2026-10-26) `--int-backend` also chose leanrt's
    own representation (the default until 2026-10-25): the lowering kept
    both paths (`IntBackend`, the `intBackend` fields of `CliOptions`,
    `PassConfig`, `MonoConfig` and `LowerCtx`), and `filterIntBackend`
    kept the prelude's blocks of the chosen one. D8 removed them (the
    history entry above).
  - **Cost model** (`NatEncoding.lean`). `natIsSmall`, `intIsSmall`
    ([-2^61, 2^61), rcgmp's immediates) and `natSmallBits` (61); every
    literal is free (a read-only object of the program's data). Users:
    `cheap-consts` (any literal is cheap; a computed `Nat.succ`,
    `Int.ofNat`, `Int.negSucc` within the immediates), `constComputes`
    (Mono: a literal never computes), `mod-pow2` (a literal divisor `2^k`
    from `k = 61`). A wrong answer costs time, never a result.
  - **Literals.** A `Nat` literal of any size is Reussir's literal,
    `{ let nl4 : Nat = 18446744073709551616; nl4 }` (no `l2r_nat_small`,
    no decimal text in the string table); a placeholder of `Nat` or `Int`
    is `{ let z : Nat = 0; z }`.
  - **Boxes.** The box kinds stay 1 and 2. `natIntBoxFns?` (LowerBase)
    gives the prelude's non-generic functions: `boxValue` calls
    `l2r_any_of_nat`/`_int`, `boxUnboxWith` `l2r_any_as_nat`/`_int` (in a
    program that casts, `l2r_any_raw_take_nat`/`_int` on the box's word
    when it is an immediate, and when it is a cell of the number's kind
    after the number test; any other word goes to the cast's slow path),
    `boxTake` (`boxDispatch`, the generated unbox of a program that casts)
    `l2r_any_raw_take_nat`/`_int`. No array
    element is read at `Nat` or `Int` through its word (`boxWordRead?`:
    the prelude's `_as<T>` reads take only `u64`). `boxUnboxed?` folds
    `l2r_any_as_nat(b)` boxed again to `b`. `boxAllocates` is true at
    `Nat` and `Int` (a value outside the immediates gets a new leanrt cell
    per boxing), so `boxed-consts` boxes a constant of those types once,
    except one whose value the box holds as an immediate
    (`constIsImmediate`: `constNumValue?` evaluates the constant's code of
    literals, `Int.ofNat`, `Int.negSucc`, `Int.neg`, `Int.add`, `Int.sub`,
    `Int.mul`, `Int.pow`; `natBoxIsImmediate`: a `Nat` below 2^63;
    `intBoxIsImmediate`: an `Int` in the `int32` range or in [2^32, 2^62)
    or [-2^62, -2^31), the rule of the prelude's `l2r_any_of_int` and
    `l2r_int_box_wide`), which is boxed in line (review of step D:
    `def k5 : Nat := 5` stored in a `List` had a once-cell; test
    `RtNatBoxedConsts`, checked by `int-backend-check.sh`).
    `Lower/Live` counts `l2r_any_of_nat` as payload `b1` and
    `l2r_any_of_int` as `b2`.
  - **`Nat` and `Int` at the FFI's type arguments.** `isFfiTypeArgTy`
    (LowerBase) is `isBoundaryTy`: a once-cell of a computed `Nat`
    constant (`onceCell`), a polymorphic extern's value at `α := Nat`
    (`lowerExternCall`), the typed arrays (`ArrayKinds.ptrKind?`) and the
    typed cells (`CellKinds.cellKind?`) of `Nat` and `Int` hold Reussir's
    owned handles. Thunks and tasks hold boxes.
  - **Reads at an index word.** `bindReadIndex` (`Lower/ExternCall.lean`)
    calls the prelude's `_w` twin of a read at a `Nat` index or position
    (`wordReadSym?`: `Array` `fget`/`get!` and their `_borrowed` symbols,
    `ByteArray` `fget`/`get!`, `String.Pos.Raw.get`, `get'`, `next'`,
    `atEnd`), with the word computed first:

    ```
    let x750 : u32 = {
        let ix749 : u64 = l2r_nat_index(a747);
        lean_array_fget_w<u32>(a745, ix749)
    };
    ```

    where the default lowering binds `let ix749 : Nat = a747;` and calls
    `lean_array_fget<u32>(a745, ix749)`. Every `Nat` argument of such a
    read is converted, a variable or not (a string position is a `Nat`
    here: `String.Pos.Raw` has one field). The `Nat` read kept the index
    until after the read, so the heap path of its conversion and the
    release of a big index (a call) sat between the caller's increment of
    the container and the read's decrement, and LLVM kept both: a load,
    an add and a store of the count before each read, and a store after
    it (Z01c's eight `ByteArray` reads of `ugetUInt64LE`, unrolled into
    the hash loop). With the word, the read follows the increment
    directly and the pair cancels. A read of an array of boxes at a type
    (`boxWordRead?`) becomes `lean_array_fget_as_w`/`lean_array_get_as_w`
    (`boxWordReadAs`; `boxWordReadBack?` maps them back). Reads without
    a twin keep the `Nat` (`FloatArray`, `get!` of a string, `next`,
    `prev`, `isValid`, `get_byte_fast`); an index that is already a word
    (`uget`, `USize`) is unchanged. Instruction counts (cachegrind, the
    SVE-free builds of the profile, on top of the prelude's own change):
    Z01c -2.07 billion (-9.8%), L17 -0.47 billion (-2.8%), X07 +11
    million (+3.9%). X07's partition loop had no count traffic before,
    and its read is as short as before (LLVM threads the select of
    `l2r_nat_index` on the immediate path), but the big index's path
    now rejoins before the loop's later uses of the index, so LLVM no
    longer knows there that the index is an immediate: `i + 1` tests the
    tag of its result again, and the swap path tests the index's tag
    once more and copies two registers (2.6 + 8.7 million). The
    variants tried against it were worse: the big case of
    `l2r_nat_index` out of line (a cold call; the read stays short, but
    X07 +13.7 million, Z01c and L17 32 and 56 million above the select),
    and converting only where the container is retained around the read
    does not tell X07 from Z01c (both containers are used after the
    read). rcgmp has no test of an immediate that Reussir code could use
    to keep the big path apart; after a proved access the code uses the
    word's value instead (`rebindIndex`, below).
    `tests/runtime/int-backend-check.sh` checks the shape on
    `RtNatIdxWord`: every `_w` read called, each after its
    `l2r_nat_index`, and no read at a `Nat` that has a twin. A read whose
    `Nat` arguments are not exactly one would keep the `Nat` read without
    a message, and RtNatIdxWord's output is the same either way.
  - **The index after a proved access** (`rebindIndex`). The updates at a
    proved index get index words too (`wordUpdateSym?`: `Array.set`,
    `ByteArray.set`, `Array.swap` call `lean_array_fset_w`,
    `lean_byte_array_fset_w`, `lean_array_fswap_w`, one word per `Nat`
    argument). An access at a `Nat` index that a proof keeps below the
    size (`boundedIndexSyms`: `a[i]'h` and its `_borrowed` symbol,
    `ByteArray.get`, those three updates) returns only when each word is
    below the size, so after it the index is the word. When the index is a
    variable that the code after the access uses (`indexWordsWanted`:
    `hasFVar` on the `let`'s continuation), the let-run (`Lower/Code`)
    asks `bindReadIndex` for the word instead of its block
    (`LowerCtx.hoistIndexWords`, `LowerState.indexWords`), binds it before
    the access's `let`, and after the `let` binds `l2r_nat_of_index` of the
    word and maps the variable to it for the rest of the code (the run's
    later `let`s and the continuation):

    ```
    let ix750 : u64 = l2r_nat_index(a748);
    let x751 : u32 = lean_array_fget_w<u32>(a746, ix750);
    let ib752 : Nat = l2r_nat_of_index(ix750);
    ...
    let x766 : Nat = lean_nat_add(ib752, x765);
    ```

    The rebinding needs the access to run whenever the `let` completes
    (`evalsBoundedAccess`: the call itself, or one in the arguments, fields,
    casts, scrutinees, conditions or block `let`s of the value); otherwise
    the word is still bound first and nothing is rebound. An index that
    nothing after the access uses keeps the read's block. A join point's
    body copied to a jump after the access (J1) reads the rebinding, which
    holds there; a body lowered once (J2, J3, a state machine's arm) reads
    the variable, which Reussir then keeps. For every `Nat`: from 2^63 the
    word is `u64::MAX` and the access is unreachable code, a word in
    [size, 2^63) is the runtime's `index_bug`, and both end the program, so
    the rebinding runs only for an index below the size, which the mask
    keeps (test `RtNatIdxRebind`: arithmetic on the index after the access
    past the immediates, big indices of `get!`, `set!`, `swapIfInBounds`
    made from it). The variable itself kept the access's big path, which
    rejoins after it (a `Nat` in [2^61, 2^63) is a heap value with a valid
    word), so every later use tested its tag again (X07's +3.9% above).
    With the rebinding `i + 1` after `a[i]` is one add (no tag test, no
    overflow path), a later access at it has no tag test, a copy of it no
    count, and a loop whose indices all come from accesses (X07's
    partition loop, entered with the indices `qsort.sort` read) carries
    known immediates. Instruction counts (cachegrind, the SVE-free builds,
    the bench set's arguments, outputs identical), before and after, the
    leanrt representation of the time for reference: on top of run 14's
    prelude reads (dfb62b22), X07 275.1 to 217.9 million (-20.8%; leanrt
    253.2) and Z01c 153.3 to 137.8 billion (-10.1%; leanrt 150.6); on dev
    1886d7bf, X07 300.1 to 217.9 million, Z01c 153.5 to 137.8 billion, L12
    9.94 to
    9.67 billion (-2.8%; leanrt 10.51), L08 6.22 to 6.01 (-3.3%; leanrt
    5.93), L18 6.25 to 6.16 (-1.5%; leanrt 6.33), X12 and E05 -0.2%, E08
    unchanged. L07, L13, E03, X08, X09 and L17 have no such access whose
    index is used again (`get!`, `set!`) and get the same generated code.
    `tests/runtime/int-backend-check.sh` checks the shape on
    `RtNatIdxRebind`, translated with the default passes and with
    `compact-arrays` off: each rebinding right after its access, the
    variable not read again in the rest of its block (nested blocks
    included), each kind rebound (the read at a type in the second
    translation), and no update at a `Nat`. The baselines of
    `paynothing-check.sh` for `Unionfind` and `RtLazyFields` were
    refreshed with the rebinding: their functions' shapes changed, their
    counts and allocations did not.

    One use keeps the variable (`loopCarriedAdds`, `CodeCtx.loopAdds`): a
    loop-carried increment, `let z := Nat.add y l` (or `Nat.add l y`) with
    `l` bound to a `Nat` literal, `y` the declaration's own parameter at a
    position `k` and `z` the argument at position `k` of a self tail call
    (`let r := f args; return r`, also a state machine's re-entry), reads
    `y`'s name from before its first rebinding (`CodeCtx.indexOrig`):

    ```
    let ix749 : u64 = l2r_nat_index(a747);
    let x750 : u32 = lean_array_fget_w<u32>(a745, ix749);
    let ib751 : Nat = l2r_nat_of_index(ix749);
    ...
    let x765 : Nat = lean_nat_add(a747, x764);
    let x766 : Tuple742 = qpartition_loop(a743, a744, a745, a746, x765);
    ```

    Every other use keeps the rebinding, and so does an increment that is
    not loop-carried: passed at another position, to a call that is not a
    tail call, or of an index that is not a parameter. In a loop the next
    iteration's index is the increment, so the increment is on the loop's
    critical path: on the tagged parameter it is one add and an overflow
    branch (`adds x, x, #4`), on the rebinding four instructions more
    (`asr`, `lsl`, `and`, `add`, recomputing the tagged value from the
    word), one cycle against about four per iteration. X07's partition loop
    is that chain (a read, a compare, the increment): 17.91 to 16.23 ms of
    kernel time (-9.4%; median of 15 interleaved runs of the bench-flag
    builds pinned to one core; leanrt 16.08 in the analysis), while its
    instructions rise from 216.3 to 234.9 million (+8.6%; cachegrind, the
    SVE-free builds). Elsewhere in the bench set: lean-regex Z03d 5.057 to
    4.922 s (-2.7%), Z03l 1.708 to 1.643 s (-3.8%), Z03b 1.004 to 0.997 s
    (-0.7%), X12 -0.4%, E05 -0.4%, Z01c 6.925 to 6.937 s (+0.2%, within
    its noise; the same without its four increments in state machines;
    instructions +0.03%). The
    parameter stays live across the access, so the increment keeps its tag
    test and its count's increment, which never runs (after the access the
    index is an immediate): instructions rise, the time falls. Applied to
    every increment of a rebound index (not only the loop-carried ones),
    Z01c ran 4.3% longer (hand-edited `.rr` of the wall-time analysis,
    2026-10-26); without the rebinding at all, X07 took 19.9 ms. The names
    from before a rebinding are not used in an outlined join point's body
    or a local function (`indexOrig` is empty there): they may not be
    captured. A join point's parameter is never loop-carried in LCNF (a
    jump occurs only in the join point's continuation, not in its body).
    `tests/runtime/int-backend-check.sh` checks the shape on `RtNatIdxLoop`
    (every loop-carried increment of its loops reads the parameter, and
    `crossed` and `nonTail`, whose increments are not loop-carried, read
    the rebinding) and allows the loop-carried increments in
    `RtNatIdxRebind`'s check.
- **Why:** upstream Reussir (without local patch R2) renders a built-in
  integer at a polyffi type argument as the raw handle and releases it after the call (its `rcgmp_handle`
  comes from the substituted parameter type): `l2r_once_put<Nat>` stored a
  handle that the wrapper then released, `l2r_array_push<Nat>` the same,
  and `l2r_once_get`/`l2r_view_take` copied without a retain (review
  R1-01 of step D: a big closed term and a typed `Array Nat` printed wrong
  sums, exit 0; test `RtNatGenericBig`). A declared `Nat` parameter is
  fine (#795: a borrowed handle). The boxes keep native's words, so casts
  and `ptrAddrUnsafe` of small values stay native's (`RtBoxPassOnCast`,
  `RtCastBoxImm`).
- **Where:** `lean2rr/Main.lean` (options); `NatEncoding.lean`;
  `Mono.lean` (`constComputes`);
  `LowerBase.lean` (`isFfiTypeArgTy`,
  `cellStorage`, `onceCell`,
  `natIntBoxFns?`, `boxValue`, `boxTake`, `boxUnboxWith`, `boxUnboxed?`,
  `boxAllocates`, `arrayPtrKindOf`, `boxWordReadAs`);
  `Lower/ExternCall.lean` (`bindReadIndex`, `wordReadSym?`,
  `wordUpdateSym?`, `boundedIndexSyms`, `boundedWordAccesses`);
  `Lower/Code.lean` (`indexWordsWanted`, `evalsBoundedAccess`, the
  let-run's rebinding, `loopCarriedAdds`; `LowerCtx.hoistIndexWords`,
  `LowerState.indexWords`, `CodeCtx.loopAdds`, `CodeCtx.indexOrig`);
  `ArrayKinds.lean` (`ptrKind?`);
  `CompactArrays.lean`, `Opt/SplitMapLoops.lean`; `CellKinds.lean`,
  `TypedCells.lean`, `Lower/Externs.lean`
  (`refElemTy`); `Lower/Values.lean` (`natLiteral`); `Lower/Conv.lean`
  (`zeroTry`); `Lower/Live.lean`; `Opt/CheapConsts.lean`;
  `Opt/ModPow2.lean` (`minLitExp`). Tests:
  `RtNatImmEdges`, `RtNatDivZero`, `RtNatLitHuge`, `RtNatGenericFfi`,
  `RtNatGenericBig`, `RtNatIdxWord`, `RtNatIdxRebind`,
  `tests/runtime/int-backend-check.sh`.
- **Remove only if:** never while lean2rr builds on Reussir's built-in
  integers. `Nat` and `Int` at type arguments need Reussir's local patch R2
  (scripts/l2r.py requires it). Guard mode (rows 10, 11, 19 of the plan: a
  lowering without `--rcgmp-type-args` that kept them out, on a Reussir with
  R2 that it did not use, and its check) existed until 2026-10-25, for
  measurements.

### Bit tests and float conversions by rcgmp (`prelude-int-ops`)

- **What:** The optional pass `prelude-int-ops` (`Opt/PreludeIntOps.lean`,
  a pass over the mono code after Stage 3, after `float-lits`) replaces
  three Lean definitions by the prelude's functions on Reussir's
  integers:

  | Lean | Lean's code | prelude |
  |---|---|---|
  | `Nat.testBit m i` | `1 &&& (m >>> i) != 0` | `l2r_nat_test_bit`: `testbiti`, reads bit `i` of `m` in place; `i` of 2^64 or more is `false` |
  | `Float.ofNat n`, `Nat.toFloat n` | `Float.ofScientific n false 0` | `l2r_float_of_nat`: `sitofp` |
  | `Float.ofInt i`, `Int.toFloat i` | `Float.ofNat` of `i.natAbs`, negated | `l2r_float_of_int`: `sitofp` |

  Example (`x.testBit i`, a `BitVec`'s `getLsbD`): Lean's mono code
  `let b := Nat.testBit._l2r.0 x i` becomes `let b := L2RNat.testBit x i`,
  and the `.rr` has `l2r_nat_test_bit(x, i)` instead of a call of the
  translated `Nat.testBit` (`lean_nat_shiftr`, `lean_nat_land`,
  `lean_nat_dec_eq`).
  - **Shapes.** None of the three definitions is `@[inline]` and none is
    small: LCNF inlines a definition without the attribute only when its
    code has at most `compiler.small` = 1 binding, and these have 3 to 5.
    `Nat.toFloat` and `Int.toFloat` are abbreviations, so they are calls
    of `Float.ofNat`/`Float.ofInt` by then, and so is `OfNat Float n`'s
    instance. What reaches lean2rr is therefore a full call of the
    definition's instance, or the instance as a function value (a
    partial application, `xs.map Float.ofNat`), never the inlined
    `Nat.land 1 (Nat.shiftRight m n)` and `Nat.decEq` (checked on a
    probe program and on Z03b's `.rr`, where `Regex.Data.BitMatrix.get`
    calls `Nat.testBit`). The pass rewrites each full call to the extern
    and replaces the instance's own code by one call of it
    (`Nat.testBit._l2r.0 m n := L2RNat.testBit m n`), so a function value
    runs the prelude function too; `Float.ofInt`'s code (with its own
    `Float.ofNat` calls) goes the same way.
  - **Externs.** `L2RNat.testBit`, `L2RFloat.ofNat`, `L2RFloat.ofInt` are
    added as `mod-pow2` adds `L2RNat.truncateBits`: a definition in the
    environment whose value is the Lean definition (not an axiom:
    `programCasts` reads one as a possible cast) with `@[extern]` naming
    the prelude function, and an extern declaration of the program, only
    when a call or an instance was rewritten. One already in the
    environment must be that extern at that type, else lean2rr stops
    (internal error).
  - **Same results.** `testbiti` reads the bit Lean's definition tests.
    `sitofp` gives the nearest double, ties to even, an infinity of the
    sign past the largest finite one; Lean 4.34's `Float.ofScientific`
    (its `Float.Model` path from 2^53) gives the same bits for every value
    (judged 2026-10-25 with 381 inputs; test `RtFloatOfNatInt`: ties at
    2^53, 2^54, 2^64, 2^100 and 2^200, one decided by a bit 147 places
    below the halfway point, the largest finite double and
    `(2^54 - 1) * 2^970`, which goes up to an infinity, and the
    negatives).
  - `L2R_DEBUG=1` prints, per definition, the calls and instances
    rewritten (`lean2rr: prelude-int-ops: Nat.testBit: 2 call(s) and 1
    instance(s) rewritten to l2r_nat_test_bit`).
- **Why:** `m >>> i` makes a new number for a big `m` at every test (Z03b,
  the regex backtracker's bit matrix of states times positions); from
  2^53 on, `Float.ofScientific` builds `Float.Model` values with bignum
  arithmetic in time quadratic in the number's bits. Cachegrind
  instructions (SVE-free builds, with the pass against without it):
  Z03b 19.16 → 18.88 G (−1.5 %; the rest of its gap to the leanrt
  representation of the time was `|||` on big numbers); a loop of `toFloat`
  on small, 2-limb and negative 2-limb values 4.17 G → 80.1 M (100000
  rounds, about 41700 → 800 per round), on small values only 41.5 → 17.5 M
  (a million
  rounds); `testBit` at every bit of a 9512-bit number, 20 times, 142.6 →
  7.8 M.
- **Where:** `lean2rr/LeanToReussir/Opt/PreludeIntOps.lean`;
  `Opt/Registry.lean`; `runtime/prelude.rr` (`l2r_nat_test_bit`,
  `l2r_float_of_nat`, `l2r_float_of_int`). Tests: `RtNatTestBit`,
  `RtFloatOfNatInt` (each with a `.l2r-debug` check that the rewrite
  runs).
- **Remove only if:** Lean inlines these definitions (then the pass must
  match the inlined code), or Reussir lowers Lean's code to the same
  operations.

### A case split is a Reussir `match` (`int-match`)

- **What:** The optimization `int-match` (on by default) lowers Lean's
  case splits on a `Nat` or `Int` to a Reussir `match` on the built-in
  integer, which Reussir compiles to one `rcgmp.match` over integer
  intervals.
  - **Stage 2 keeps the `cases`.** lean2rr's copy of `toMono` (`toMonoK`,
    `keepIntCases`) leaves a `cases` on `Nat` (`Nat.zero`, `Nat.succ p`)
    or `Int` (`Int.ofNat m`, `Int.negSucc m`) a `cases`, its fields at
    `Nat`, where Lean's `casesNatToMono` writes `zero := 0; isZero :=
    Nat.decEq n zero; cases isZero | false => p := Nat.sub n 1 …` and
    `casesIntToMono` `Int.decLt i 0` and `Int.natAbs`. Lean's mono passes
    and lean2rr's handle it as a `cases` on any inductive (Lean's own base
    phase has them; `elimDeadBranches` knows `Nat` values as constructor
    chains). A `Nat.succ` value is still `Nat.add x 1`.
  - **The `match`.** `lowerCases` (Lower/Code) sends a `cases` on a
    `Nat` or `Int` scrutinee to `lowerIntMatch`; `Lower/IntMatch.lean`
    finds the arms (`natArms`, `intArms`):

    ```
    def fib : Nat → Nat                  fn l_fib___l2r_0_(a1 : Nat) -> Nat {
      | 0 => 0                               match a1 {
      | 1 => 1                                   0 => { … },
      | n+2 => fib n + fib (n+1)                 1 => { … },
                                                 Nat::Succ(Nat::Succ(f2)) => { … }
                                             }
                                         }
    ```

    `Nat.zero` is the literal arm `0`, `Nat.succ p` the arm `Nat::Succ(p)`:
    Reussir computes `p` in the selection (an immediate's tagged bits
    minus 4; a heap value's difference), with no test of `n == 0` and no
    `Nat.sub`. A `cases` on a field that is the field's only use, at the
    start of its arm (after `let`s of literals), joins the outer `match`:
    its zero is a literal (`1` above; `0` under `Int::OfNat`, `-1` under
    `Int::NegSucc`), its `succ` a pattern inside the outer constructors
    (`Nat::Succ(Nat::Succ(q))`, `Int::OfNat(Nat::Succ(k))`), its default
    `Nat::Succ(_)` (`RR.Arm.wrap`: the constructors around the arm's own
    pattern). The arm's binder is `_` where the code does not use it.
  - **Chains of literal tests.** Lean compiles `match n with | 0 => … |
    5 => … | _ => …` to tests `Nat.decEq n k` (`Nat.beq n k` for `==`;
    `Int.decEq i k` on an `Int`), not to a `cases`. In `lowerCode`'s run
    of `let`s, a test of a `Nat` or `Int` against a literal whose result
    only its `cases` reads starts a chain (`chainArms`). A literal is a
    `let` of one, or of `Int.ofNat`, `Int.negSucc` or `Int.neg` of
    literals, or a read of a constant that computes one (`litValue?`,
    `litConst?`: Lean extracts a `Nat` literal from 2^63 on, and an `Int`
    literal such as `-7` as `Int.neg (Int.ofNat 7)`, as closed terms). The
    chain has an arm per literal while the `false` branch, after `let`s of
    literals, is another such test of the same variable, then that branch
    as the default `_`, or the arms of a `cases` on the same variable
    there. Literal `let`s between the tests go into the later arms that
    use them, with the `let`s these read in turn (`-6` computed in place
    is `Int.neg` of `Int.ofNat` of `6`: `IntArm.fullCode`); those only
    the tests read are left out. The arms keep the
    order of Lean's tests, and Reussir's first matching arm wins (a literal
    tested first goes to its arm also when a later `Nat::Succ` arm covers
    it). A literal tested again stops the chain.
  - **Coverage.** A literal arm that an earlier arm covers is left out,
    and so is a default whose position is covered (Reussir warns about an
    arm no value reaches); arms that do not cover every value (Lean's
    `elimDeadBranches` removed an alternative, no default) end with
    `_ => l2r_unreachable`.
  - **The scrutinee in an arm.** An arm that names the scrutinee reads it
    through a binding Reussir makes of the whole scrutinee (#803): in a
    literal arm the constant, in `_`, `Int::OfNat(m)`, `Int::OfNat(_)` and
    a last arm without a binder (Reussir makes it the `default`) the value
    itself, but in an arm that selects the scrutinee minus a bound
    (`Nat::Succ(p)`, `Int::NegSucc(m)`, `Nat::Succ(_)` before other arms,
    …) a value rebuilt from that difference (`p + 1`, an allocation for a
    heap value; Reussir's tests SUMTO, GUARDED). Where such an arm names it, the
    `match` is on a copy (`let ns3 : Nat = n; match ns3 { … }`): the arm
    reads `n` itself, which Reussir retains before the `match` (a test of
    the tag for an immediate) and releases in the arms that do not use it.
- **Why:** The owner and Reussir's maintainer want lean2rr to use
  Reussir's own `Nat` where Reussir has a construct for it (clean
  integration, step D, D7a). One `rcgmp.match` selects the arm by the
  tagged bits and gives the arm its binder; Lean's form is a test and a
  `Nat.sub` (a monus with its own fast path) per split, and a chain of
  literal tests is one test per literal. Instruction counts (cachegrind,
  2026-10-25, with the pass against `--disable-opt int-match`): a
  loop through `n+1` −7.9%, `sumTo` −3.1%, a countdown above 2^64 −2.5%,
  `fib` (`0`, `1`, `n+2`) +6.6%, Ackermann +7.6%, six literal arms +10%;
  of the shared benchmarks E01 −3.0%, X14, X13, L04, L11 unchanged, X04
  +1.7%, L08 +2.2%. The increases come from rcgmp's selection among
  immediates: it computes the arm's index and the binder's offset with
  conditional selects and then switches on the index, a few instructions
  more than one comparison for two or three arms, and it computes the
  binder also on paths that do not use it (Lean's `Nat.sub` moves into
  the branch that uses it).
- **Where:** `TypedToMono.lean` (`keepIntCases`, `toMonoK`);
  `Opt/IntMatch.lean` (`install`: Stage 2's `toMono` and
  `PassConfig.intMatch`); `PassConfig.lean`,
  `LowerBase.lean` (`LowerCtx.intMatch`), `Emit/Program.lean`;
  `Lower/IntMatch.lean` (`IntMatchInfo`, `intMatchInfo`, `litValue?`,
  `litConst?`, `litEqTest?`, `litTest?`,
  `natCasesOn?`, `natArms`, `intArms`, `chainArms`); `Lower/Ctx.lean`
  (`CodeCtx.intInfo`); `Lower/Code.lean` (`lowerCases`, the chain in
  `lowerCode`'s run of `let`s, `lowerIntMatch`); `RR.lean` (`Arm.wrap`);
  `Outline.lean` (`variantTable`: the binders of `Nat::Succ`,
  `Int::OfNat`, `Int::NegSucc` are `Nat`s); `Opt/MergeFns.lean` (the
  hash reads `wrap`). Tests: `RtNatMatch`, `RtIntMatch`,
  `RtIntMatchNoExtract`,
  `tests/runtime/int-match-check.sh` (the shapes; none with the pass off).
- **Remove only if:** lean2rr stops using Reussir's built-in integers, or
  Reussir rebuilds no value from a `match` (then the copy goes).

### `x % 2^w` is the low `w` bits of `x`, without `2^w` (`mod-pow2`)

- **What:** The optional pass `mod-pow2` (`Opt/ModPow2.lean`, after Stage 3)
  rewrites `Nat.mod x p` where `p` is bound in the same declaration to
  `Nat.pow 2 w`, to `Nat.shiftLeft 1 w`, or to the literal `2^k` with
  `k ≥ 61` (rcgmp's immediates end at 2^61: `minLitExp`, `natSmallBits`;
  also a read of a constant whose
  code is that literal: Lean folds `2 ^ 64` to a literal, which Stage 2
  extracts as a closed term).
  The call becomes `L2RNat.truncateBits x w` (with a `let` of the literal
  `k`), an extern the pass adds (`@[extern "l2r_nat_truncate_bits"]`, in
  the environment a definition whose value is the rule,
  `fun x w => Nat.mod x (Nat.pow 2 w)`, and a declaration of the program;
  not an axiom: the whole-program check `programCasts` reads an axiom of
  the program as a possible cast, which turned Cedar's casts on). The
  `L2R*` namespaces are lean2rr's: a `L2RNat.truncateBits` already in the
  environment that is not that extern at `Nat → Nat → Nat` (a program's
  own definition of the name) is an internal error, never called in its
  place. The `let` of `p`, and that of the literal 2 or 1 it took,
  go when nothing else uses them. The prelude's `l2r_nat_truncate_bits`
  is rcgmp's `floormod2expi` (local Reussir patch R1: immediates in line,
  the low limb of a big `x` for `w` below 62), and a `w` of 2^64 or more
  keeps `x`. Example: `BitVec.ofNat w x` (every `BitVec` `+`, `*`,
  `<<<`, `1#w`) was `let p := Nat.pow 2 w; Nat.mod x p` and is now
  `L2RNat.truncateBits x w`.
- **Why:** `Nat.pow 2 w` made a number of `w / 64 + 1` limbs on every wide
  `BitVec` operation (zeroed, then the top bit set), and the division then
  compared it with `x`. lean-regex's backtracker (Z03b) sets one bit of a
  vector of states times positions per step (`b ||| (1#w <<< i)`: three
  truncations): 42% of its instructions were the `memset` of these powers
  after the runtime's fixes of its bitwise operations and divisions
  (leanrt's own numbers, before D8).
  Natively GMP does the same work (`mpz_pow_ui`, 41% of native's
  instructions there). Cachegrind (SVE-free builds), Z03b: on dev 09c72f68
  (with the boxed error messages of `flatten-structs`) 65.76 → 38.58
  billion instructions (−41.3%); on the runtime's branch with its fixes of
  `big::bitwise` and `big::div` (f458773c) 27.94 → 14.09 billion (−49.6%).
  Cedar (Z06g, whose `Int64` arithmetic goes through `BitVec.ofNat 64`)
  the same; the other measured programs (L08, X12, L15, E05, L10, L11,
  E09) have no such call and the same code. The value is `x % 2 ^ w` for
  every `x` and `w`.
  Natively `2 ^ w` ends the process from `w = 2^32` (`Nat.pow exponent is
  too big`), and in lean2rr without the pass above `MAX_BITS` bits;
  the truncation needs no power, so it gives the value there too, as
  lean-runtime lifts native's limits where the result can be computed
  (LB-11). A literal divisor below 2^61 is an immediate, whose `%` rcgmp
  computes in line; the rule leaves it.
- **Where:** `Opt/ModPow2.lean` (`rewrite`, `dropUnused`, `literalPows`,
  `truncDecl`); `Opt/Registry.lean` (`mod-pow2`); `prelude.rr`:
  `l2r_nat_truncate_bits`; runtime test `RtNatModPow2` (with
  `RtNatModPow2.l2r-debug`: calls rewritten, and `program casts: no`).
- **Remove only if:** Lean computes `BitVec.ofNat` without `2 ^ w`; else
  never (speed only).

### Literals: Reussir's own literal of any size

- **What:** A `Nat` literal of any size is Reussir's literal
  (`natLiteral`): `{ let nl4 : Nat = 18446744073709551616; nl4 }`. rcgmp
  makes a value outside the immediates a read-only object of the
  program's data (one of its immortal integers), so a literal costs no
  allocation and no parse at run time.
- **Why:** Reussir's interface for its integers (clean-integration step
  D). Until D8 (2026-10-26) the leanrt representation built a literal
  below 2^63 with `l2r_nat_small(k)` (the word `2k+1`) and a bigger one
  with `l2r_nat_of_decimal_lstr(s)`, parsed at run time from its decimal
  digits in the string literal table: a flat call, because a nested
  arithmetic expression per limb overflowed rrc's stack at about 20000
  digits and cost quadratic time (adv2 N1, fbf37e8).
- **Where:** `Lower/Values.lean`: `natLiteral`; tests `RtNatLitHuge`,
  `RtNatConst`. Plan [§5.4](../../translation-plan.md#54-let-return-literals).
- **Remove only if:** never while lean2rr uses Reussir's integers.

### `Nat` and `Int` are FFI-boundary types

- **What:** `isBoundaryTy` counts `Nat`/`Int` as runtime handles: a `Box`
  holds the handle like any other value, and a once-cell holds it directly
  (the prelude's `L2RNatRef`/`L2RIntRef` are gone).
- **Why:** They are counted handles now, which Reussir passes across the
  FFI boundary and keeps in cells (the old Reussir bug with cells, fixed
  upstream in #666 and #681, only concerned `[value]` records).
- **Where:** `LowerBase.lean`: `isBoundaryTy`, `refType`.
- **Remove only if:** `Nat` stops being a counted handle.

### `ptrAddrUnsafe` and casts read a `Nat`/`Int` word as native does

- **What:** `ptrAddrUnsafe` of a `Nat` below 2^63 or an `Int` in the
  `int32` range is native's boxed scalar (`2n + 1`, the `int32` word); of
  another value its handle's word (a heap integer's address, or rcgmp's
  odd immediate for an `Int` below 2^61 in magnitude, never equal to an
  `int32` word), read as a number and never decoded. `unsafeCast` of an
  `Int` in the `int32` range to `Nat` gives the `Nat` of its 32 bits (the
  same word natively), of another its magnitude.
- **Why:** The answers are native's where a program can depend on them
  (scalars), and distinct per value elsewhere, so `ptrEq` stays a valid
  shortcut (review R1-06).
- **Where:** `prelude.rr`: `l2r_addr_nat`, `l2r_addr_int`, `l2r_int_word`,
  `l2r_int_cast_nat`; [identity.md](identity.md).
- **Remove only if:** never.

### Heap integers alive at exit are counted in tests

- **What:** The allocation counter of the tests
  (`tests/runtime/alloccount`) also wraps rcgmp's allocation hooks in
  lean2rr's builds (`rcgmp_allocate`, `rcgmp_dealloc`, which reussir-rt
  defines) and prints the heap integers made less those freed at exit
  (`alloccount: rcgmp live L`). `tests/runtime/alloc-check.sh`'s optional
  bound `live OFFSET` lets that count change by at most `OFFSET` between a
  test's two sizes, and fails a lean2rr run without the line:
  `RtNatStress` (`live 0`, 0 at both sizes: every big number a round
  makes is freed exactly once) and `RtNatConst` (`live 0`, 2 at both
  sizes, its two computed constants; its allocation bound, FACTOR 0, also
  catches a big constant made at every use).
- **Why:** Reference counts of heap integers cross the prelude, leanrt's
  boxes and Reussir's glue; a leak or a double free changes the count
  with the size, exactly, where the allocation counts and the peak memory
  do not show one small number per round (until D8,
  `nat-alloc-check.sh` read leanrt's own counters, which rcgmp's integers
  do not pass through). Shown to fail: a box of a big number whose cell
  is never released (`release_kind`) gives `RtNatStress` 1000 -> 4000,
  and a build without the wraps fails it for the missing line.
- **Where:** `tests/runtime/alloccount/alloccount_rcgmp.c`
  (`__wrap_rcgmp_allocate`, `__wrap_rcgmp_dealloc`, strong `__real_`
  declarations, so a link without the hooks fails instead of calling
  null; the hooks' object is always loaded, because rustc's symbols.o
  references `__reussir_allocate`, defined beside them), linked only
  into lean2rr's builds; `alloccount.c` (the line, through a weak
  reference to the count, null in native builds); `alloccount.sh`
  (`ALLOCCOUNT_RCGMP_SYMS`, `AC_RRC`, `alloccount_live`),
  `tests/runtime/alloc-check.sh`, `RtNatStress.alloc`, `RtNatConst.alloc`.
- **Remove only if:** never (test infrastructure; not in programs).

### `Nat.repr` of 0..127 shares one string per number

- **What:** The runtime keeps a table of the strings of 0 to 127, built on
  first use, and `l2r_nat_repr` returns a new reference to the shared one.
  With the optional pass `prelude-repr`, `Nat.repr`, `Nat.reprFast` and
  `Int.repr` call `l2r_nat_repr`/`l2r_int_repr`: the digits of a word are
  lean-runtime's (`sem::repr::decimal_u64_bytes` into a stack buffer, as
  `lean_string_of_usize`), those of a bigger value rcgmp's
  (`leanrt::rcgmp::repr`: `rcgmp_mpz_to_decimal`).
- **Why:** Natively `Nat.reprFast` reads the closed term `Nat.reprArray`,
  so printing small numbers allocates nothing (adv4 PF4-04, ce60463). The
  Lean code also divides big numbers digit by digit (quadratic), and
  cloned `Nat.reprArray`'s once-cell for every number ≥ 128 (13% of the
  classic Sieve; runtime requests 12 and 27).
- **Where:** `leanrt/src/string.rs`: `repr_small`, `repr_small_init`;
  `leanrt/src/rcgmp.rs`: `repr`; `prelude.rr`: `l2r_nat_repr`,
  `l2r_int_repr`, `l2r_u64_repr`, `l2r_i64_repr`; `Opt/PreludeRepr.lean`.
- **Remove only if:** the strings are the same either way; the pass and
  the table only save time and allocations. The runtime keeps the
  functions when the pass is off.

### Indices and positions are never big

- **What:** An index that is in bounds (a `Fin`, or after the bounds test
  of `get!`) or a position proved valid is never a big `Nat`. A read takes
  it as its word (`l2r_nat_index`, the reads at a word `_w`): a word from
  2^63 is out of range, the read's failing branch, unreachable code (for
  the string reads `get'`/`next'`, a word from 2^60, tested inside the
  read: `l2r_string_get_fast_k`, `l2r_string_next_fast_k`,
  `leanrt::unreachable_code`); an update converts it with
  `l2r_index_of_nat` or `l2r_index_of_word`, whose big case ends the
  program. Where Lean's C code tells "not a scalar" apart from "out of
  range", the prelude does too: a big `Nat` (`lean_string_utf8_extract`,
  where it counts as `SIZE_MAX`, as natively since Lean 4.34, through
  `l2r_index_sat`; the `Pos.Raw` reads), a big `Int` (`Float.scaleB`,
  `l2r_int_sat_i64`). `lean_string_utf8_extract_fast` (`String.extract`,
  new in Lean 4.34) takes its positions, valid by proof, as words whose
  big case is unreachable code.
- **Why:** See
  [../ownership.md](../ownership.md#reads-give-their-reference-up-first-for-a-view).
- **Where:** `prelude.rr`: `l2r_nat_index`, `l2r_index_of_nat`,
  `l2r_index_of_word`, `l2r_index_sat`, `l2r_word_index_ok`,
  `l2r_string_get_fast_k`, `l2r_string_next_fast_k`,
  `lean_string_utf8_extract`, `lean_string_utf8_extract_fast`;
  `leanrt/src/lib.rs`: `unreachable_code`; tests `RtString`,
  `RtArrayReadViews`, `RtNatPosEdges`, `RtNatIdxWord`.
- **Remove only if:** see the linked entry.
