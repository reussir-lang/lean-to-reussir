# `Nat` and `Int`

Paths: `runtime/prelude.rr`, `runtime/leanrt/src/`, and
`lean2rr/LeanToReussir/` for lean2rr's files.

lean2rr has two representations of `Nat` and `Int`, chosen by
`--int-backend` (scripts: `L2R_INT_BACKEND`): `rcgmp`, Reussir's built-in
integers, the default since 2026-10-25 (the sections headed
"`--int-backend rcgmp`"), and `leanrt`, Lean's own one-word encoding with
leanrt's big numbers, the default until 2026-10-25 (the other sections
describe it, or what both representations share). `--int-backend leanrt`
still selects leanrt everywhere (lean2rr, scripts/l2r.py, the test
scripts); its code goes in a later, separate step (clean-integration plan,
D8).

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

### The encoding is known in one place

- **What:** A small set of named helpers builds, tests and decodes the
  words:

  | Helper | Gives |
  |---|---|
  | `l2r_nat_raw(n)`, `l2r_nat_of_raw(w)`, `l2r_nat_drop_raw(w)` | the word of a handle (the word then owns the reference), the handle of a word, the release of a word |
  | `l2r_nat_word_is_small(w)` | whether a word is a small value (`w & 1`) |
  | `l2r_nat_word_val(w)` | the value of a small word (`w >> 1`) |
  | `l2r_nat_val_is_small(v)`, `l2r_nat_small_word(v)`, `l2r_nat_small(v)` | whether a `u64` value has a small word (below 2^63), that word (`2v+1`), its handle |
  | `l2r_nat_of_u64(v)` | the `Nat` of any `u64` (small or big) |
  | `l2r_int_raw`, `l2r_int_of_raw`, `l2r_int_drop_raw`, `l2r_int_word_is_small` | as for `Nat` |
  | `l2r_int_word_bits(w)`, `l2r_int_word_val(w)` | the 32-bit pattern of a small word (the boxed scalar), its signed value |
  | `l2r_int_val_is_small(v)`, `l2r_int_small_word(v)`, `l2r_int_small(v)`, `l2r_int_of_i64(v)` | the `int32` range test, the word, the handle; the `Int` of any `i64` |

  They are at the start of the prelude's Nat and Int sections. The rest
  of the prelude (strings, arrays, `Float.scaleB`, `ptrAddrUnsafe`, the
  fixed-width integers) and every call that lean2rr generates use only
  these helpers and the functions of the two sections (`lean_nat_*`,
  `lean_int_*`, `l2r_nat_low`, `l2r_word_index_ok`, `l2r_int_word`, ...).
  They never use a bit operation on a `Nat` or `Int` word.

  The other functions of the two sections compute on the words directly:
  for example `x + (y - 1)` (the word of a sum), `x - y + 1`,
  `(x ^ y) | 1`, comparisons of words, and the tests `x & 1` and
  `(x >> 32) == 0`. They are the code of the representation, as the
  helpers are.

  Two other places know the representation:
  - leanrt has its own copy in `leanrt::nat`: `is_small`,
    `nat_of_small_word`, `small_word`, `int_of_small_word`, `LNat::small`,
    `LInt::small`, and the small ranges. The rest of leanrt
    (`index_word`, `any::of_nat`, `any::of_int`) uses them. A box holds a
    small `Nat` or `Int` as its own word (an immediate): `leanrt::any`
    knows this (`of_nat`, `nat_of_word`, `nat_of_ref`, and the `Int`
    forms). The prelude's texture `l2r_view_take_as` calls `nat_of_ref`
    and `int_of_ref`.
  - lean2rr's own rules know only which values are small, not the words.
    `NatEncoding.lean` has `natIsSmall` (below 2^63) and `intIsSmall` (the
    `int32` range), by backend (`--int-backend`), and `natLiteral`, the
    optimizations `cheap-consts` and `mod-pow2` and `constComputes` (Mono)
    use them. lean2rr emits only helper calls:
    `l2r_nat_small(k)` for a literal, `l2r_nat_small(0)` and
    `l2r_int_small(0)` for placeholders, `l2r_int_word`, `l2r_int_of_word`,
    `lean_usize_of_nat`, `lean_usize_to_nat` and `l2r_int_cast_nat` for
    casts, `l2r_addr_nat` and `l2r_addr_int` for `ptrAddrUnsafe`,
    `l2r_nat_sat` for a priority.
- **Why:** A later change of the representation (for example, `Nat` and
  `Int` on Reussir's coming builtin big integer) then changes the helpers,
  the other functions of the two sections, `leanrt::nat` and the two
  definitions of `NatEncoding.lean`, and nothing else.
  The functions of the two sections keep their bit operations. They call
  only the helpers that were functions before (`l2r_nat_small`,
  `l2r_nat_of_u64`, `l2r_int_small`, `l2r_int_of_i64`, `l2r_int_word_val`),
  because of Reussir's MLIR inliner (`reussir-default-inliner`). It
  inlines a callee only if the callee has at most 256 operations, and it
  counts a callee after the inlining into it but before the folding. Each inlined helper
  brings its own constants (the `1` of `w & 1`), so a helper call can add
  an operation where the written-out expression shares a constant. The
  functions of the two sections are inlined into most program functions.
  With more helper calls in them, a program function could cross the
  limit and stop being inlined into its callers. As written, these
  functions have the same operations as before the helpers.
  The helper calls in the other sections add at most two operations to a
  string or array function. Result: the machine code of every Reussir
  function of L11, E01, E09, X04, X13 and L10 is the same as before, except
  `IO.Error.toString`. That function is in every program (the message of
  an uncaught `IO.Error`) and it is cold. Its callees `fopenErrorToString`
  and `otherErrorToString` (string operations) now go past the limit, so
  they are not inlined into its 8 call sites. The text is 16 KB smaller
  in each program.
- **Where:** `runtime/prelude.rr`: the first blocks of the Nat and Int
  sections; `runtime/leanrt/src/nat.rs`: the block above `is_small`;
  `runtime/leanrt/src/any.rs`: `of_nat`, `nat_of_ref`;
  `lean2rr/LeanToReussir/NatEncoding.lean`.
- **Remove only if:** never (an organization rule). Lean's own copy of its
  closed-term extraction (`ExtractClosedK.lean`: a literal of 2^63 or more
  is extracted) keeps Lean's rule, which does not depend on lean2rr's
  representation.

### `--int-backend rcgmp`: Reussir's built-in integers (the default)

- **What:** With `--int-backend rcgmp` (clean-integration step D; scripts:
  `L2R_INT_BACKEND=rcgmp`), a `Nat` and an `Int` are Reussir's built-in
  integers (`core::num::Nat`/`Int`, rcgmp: an immediate or a counted heap
  integer). The prelude keeps both representations in marked blocks: a
  line `// @int-backend leanrt` or `// @int-backend rcgmp` opens a block,
  `// @int-backend end` closes it, blocks never nest, and lean2rr keeps
  only the selected backend's blocks (before prelude-liveness). Every
  function keeps its name and signature in both, so the lowering and the
  rest of the prelude call the same functions. The leanrt blocks are
  today's code unchanged.
  - The rcgmp Nat and Int sections compose Lean's rules (lean-runtime's
    `sem::nat`, `sem::int`) of Reussir's operators and
    `core::intrinsic::bigint`: `+`, `-` (truncating on `Nat`), `*`,
    comparisons, `& | ^`, `<<`/`>>` (a nonnegative `i64` amount),
    `/`/`%` behind a zero test (`n / 0 = 0`, `n % 0 = n`), `divsi_exact`,
    `edivsi`/`emodsi`, `log2i`, `gcdi`, `absi`, `ipowi`, `as` casts (the low
    bits of the two's complement), `Int::NegSucc`. A value is tested and
    converted with `trunci_overflow`, never by its encoding.
  - `Nat.pow` and `Nat.shiftLeft` test the result's size first, as
    lean-runtime's rules do, against `leanrt::rcgmp::MAX_BITS` (leanrt's
    `big::MAX_BITS`, the same GMP below rcgmp): above it the process ends
    with native's message (`l2r_internal_panic` codes 6 and 7 for an
    exponent or shift of 2^32 or more, else 4, out of memory).
    `x % 2^w` (`l2r_nat_truncate_bits`) is rcgmp's `floormod2expi`, and
    the divisions are Lean's modes (`divsi_lean`, `remsi_lean`,
    `edivsi_lean`, `emodsi_lean`: quotient 0 and remainder `x` for a zero
    divisor), both through local Reussir patch R1.
  - Index words: the prelude's string and array functions read a `Nat`
    index, position or capacity through its word (`l2r_nat_raw`,
    `l2r_word_index_ok`, ...). The rcgmp block defines those helpers on an
    index word: the value below 2^63, `u64::MAX` from there, owning
    nothing. The functions that need a big position's value
    (`String.Pos.Raw.next`/`prev`), Rust's decoding of a word (the
    `get_fast`/`next_fast` textures) or the native word (`l2r_addr_nat`,
    `l2r_addr_int`) and `l2r_int_sat_i64` have rcgmp versions of their own.
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
    `_next_fast_w` and `_at_end_w` read at such a word (in the rcgmp
    blocks, as the lowering calls them only under rcgmp, so the leanrt
    prelude is unchanged; they use no encoding of the leanrt backend;
    `u64::MAX` is out of range, unreachable code for `fget`, `get_fast` and
    `next_fast`). `l2r_nat_index` is one truncation to `i64` and one
    select (`if w { u64::MAX } else { k }`): the flag is set exactly from
    2^63, since rcgmp tests the signed range and a `Nat` is never
    negative. With `l2r_pos_of_nat` instead (its tests of bit 63, in
    `l2r_nat_raw` and on its result), about 5 more instructions per read
    stayed after the immediate and big paths joined (X07 +25%, L17 +10%,
    Z01c +6.6% instructions with the lowering's `_w` reads). There is no
    leanrt `l2r_nat_index` and no leanrt `_w` read. The lowering computes
    the word before it passes the container, so that a big index's release
    never comes between the container's increment and the read's decrement
    (the lowering's entry below). `lean_array_fget_as_w` and
    `lean_array_get_as_w` (in the rcgmp blocks too) are the reads at a type
    (`boxWordRead?`) of `lean_array_fget_w` and `lean_array_get_w`.
  - Boxes stay Lean's: a `Nat` below 2^63 and an `Int` in the `int32` range
    are immediates (`l2r_any_of_nat`, `l2r_any_of_int`, tested in Reussir
    code); a bigger value is a leanrt cell of kind 1 or 2 that holds an
    rcgmp reference (`leanrt::any::of_mpz`, `mpz_of`; `--cfg leanrt_rcgmp`
    makes `release_kind` release it). `l2r_any_as_nat`/`_int` decode an
    immediate in Reussir code. The lowering calls these four for the box
    kinds 1 and 2 under rcgmp (a generic texture at `Nat` gets the raw
    handle, so it cannot test a small value).
  - leanrt's part is `leanrt::rcgmp` (`--cfg leanrt_rcgmp`): the box cells
    (of `reussir_rt::rcgmp::Mpz`, the owned handle that local Reussir patch
    R2 renders at polyffi type arguments, re-exported), decimal text
    (`repr`), `replicate_len`. It calls
    rcgmp's public C API only. A generic box texture at `Mpz`
    (`l2r_any_of<Nat>`) ends the program with a message
    (`generic_mpz_box`): it cannot keep small values immediates.
  - The backend needs Reussir's local patches R1 and R2:
    `scripts/l2r.py` checks for them (`RCGMP_REUSSIR_PATCHES`). With R2, a
    typed `Array Nat`, a once-cell constant and every generic texture at
    `Nat` hold `Mpz` values, counted by rcgmp's C calls (test
    `RtNatGenericBig`).
  - rrc needs Reussir's core package for `Nat` and `Int`: `scripts/l2r.py`
    builds its interface once per Reussir checkout (`core_interface`) and
    compiles the program in package mode (`--package-name prog --extern
    core=...`).
  - Differences from the leanrt backend (allowed by the functional
    equivalence contract; review R1):
    - `Nat.add`/`mul` and the `Int` operations do not test lean-runtime's
      `MAX_BITS` (only `pow` and `shiftLeft` do, where small operands make
      a huge result). An allocation failure ends through Reussir's
      allocation panic or rcgmp's `abort`, not `INTERNAL PANIC: out of
      memory` (in both backends GMP's own `mpz_pow_ui` aborts).
    - `Nat.divExact`/`Int.divExact` are computed as `div` (as natively and
      in the leanrt backend), not with rcgmp's exact division, whose
      immediate path is LLVM's `sdiv exact`: poison for a false proof.
    - An immediate of 2^31 or more boxed at another type (a `Nat`, a
      `UInt32`) and unboxed at `Int` gives the `Int` of its low 32 bits,
      normalized: `==` with that value is true and `ptrAddrUnsafe` is its
      `int32` word, where the leanrt backend keeps the raw word (`==`
      false, as natively). Only a program that casts gets there.
    - `ptrAddrUnsafe` of a big value is its handle's word (a heap
      address, or rcgmp's immediate for an `Int` below 2^61 in magnitude),
      distinct per value. A boxed big value is one leanrt cell per box: two
      boxes of one integer have different addresses and are both
      exclusive (natively the box is the number object).
    - `dbgTraceIfShared` (a debug message) follows rcgmp's immediates, not
      Lean's: a `Nat` in [2^61, 2^63) is a heap value here and can be
      reported shared (a literal such as 2^61 always is: an immortal object),
      where natively it is a scalar; an `Int` with |x| in [2^31, 2^61) is an
      immediate here and never reported, where natively it is an object.
    - A boxed `Int` in [2^32, 2^62) or [-2^62, -2^31) is an immediate
      (`2v + 1`, `l2r_int_box_wide`; natively an object, its word an
      address): an `int32` value keeps Lean's scalar, and a box word read
      at `Int` decodes as the `int32` pattern below 2^32 and as `2v + 1`
      from there.
- **Why:** Reussir's maintainer asks lean2rr to use Reussir's interface
  instead of its own encodings (clean-integration plan, step D); rcgmp
  landed upstream on 2026-10-24.
- **Where:** `runtime/prelude.rr` (the `@int-backend` blocks);
  `runtime/leanrt/src/rcgmp.rs`, `any.rs` (`of_mpz`, `mpz_of`,
  `release_kind`, `generic_mpz_box`); `scripts/l2r.py` (`INT_BACKEND`,
  `core_interface`, `check_rcgmp`);
  `tests/runtime/leanrt-unit.sh` (its rcgmp build).
- **Remove only if:** the rcgmp backend is dropped. It is the default
  since 2026-10-25 (combined gate 25 green under both representations;
  timing run 14: per-case geomean rcgmp/leanrt 0.990). The leanrt blocks,
  `big.rs`, `gmp.rs` and `nat.rs` go only when the leanrt representation
  is retired (clean-integration plan, D8), not with the change of the
  default.

### `--int-backend rcgmp`: the lowering

- **What:** lean2rr's side of the switch (clean-integration step D; plan
  STEP-D-LOWERING rows 3 to 14, 18, 19). `--int-backend leanrt` (the
  default until 2026-10-25) translates every program to the same `.rr` as
  before step D (the prelude after its leanrt blocks are kept).
  - **Options.** `--int-backend rcgmp|leanrt` (`Main.lean`; scripts:
    `L2R_INT_BACKEND`) and `--rcgmp-type-args` (Reussir's local patch R2
    is there: a `Nat` or `Int` at a type argument of a generic FFI function
    is an owned handle). Both are in `PassConfig` (`intBackend`,
    `rcgmpTypeArgs`), set before the optional passes are installed, in
    `MonoConfig.intBackend` and in `LowerCtx` (`intBackend`,
    `natIntTypeArgs`: true under leanrt or with `--rcgmp-type-args`).
  - **Defaults.** Since 2026-10-25 `rcgmp` is the default of
    `--int-backend` (`CliOptions`, `PassConfig`, `MonoConfig`, `LowerCtx`,
    `Opt.config`) and of `L2R_INT_BACKEND` (scripts/l2r.py, run.sh and the
    check scripts: unset or empty is `rcgmp`); before, it was `leanrt`.
    scripts/l2r.py always passes `--int-backend`, and under rcgmp also
    `--rcgmp-type-args` (unless `L2R_RCGMP_TYPE_ARGS=0`). lean2rr's own
    `--rcgmp-type-args` stays off unless given, so `lean2rr` called
    without options lowers in the guard mode below, which needs no patch
    R2. The check scripts that call lean2rr directly pass what
    scripts/l2r.py passes (`int_flags`); those that test one
    representation name it.
  - **Prelude blocks.** `filterIntBackend` (`NatEncoding.lean`) keeps the
    chosen backend's blocks and drops the marker lines, right after the
    prelude is read (`Main.pipeline`), so Stage 1's list of prelude
    functions, the lowering's signatures and prelude-liveness see one
    definition of each function. A block opened inside a block, an `end`
    outside one, an unknown backend or a block left open stops lean2rr.
  - **Cost model.** `natIsSmall b`, `intIsSmall b` (rcgmp: [-2^61, 2^61),
    rcgmp's immediates), `natLitFree b` (rcgmp: every literal, a read-only
    object of the program's data) and `natSmallBits b` (61 under rcgmp).
    Users: `natLiteral`, `cheap-consts` (any literal is cheap; a computed
    `Nat.succ`, `Int.ofNat`, `Int.negSucc` within the immediates),
    `constComputes` (Mono: a literal never computes), `mod-pow2` (a literal
    divisor `2^k` from `k = 61`). A wrong answer costs time, never a
    result.
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
    the prelude's `_as<T>` reads have no rcgmp path). `boxUnboxed?` folds
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
    `RtNatBoxedConsts`, checked by `int-backend-check.sh`). Only under
    rcgmp: under leanrt boxing never allocates, and the constant is not
    evaluated.
    `Lower/Live` counts `l2r_any_of_nat` as payload `b1` and
    `l2r_any_of_int` as `b2`.
  - **No `Nat` or `Int` at the FFI's type arguments** (without
    `--rcgmp-type-args`). `isFfiTypeArgTy` (LowerBase) is `isBoundaryTy`
    minus the types that mention `Nat` or `Int`; `cellStorage` uses it,
    so a once-cell of a computed `Nat` constant (`onceCell`) and a
    polymorphic extern's value at `α := Nat` (`lowerExternCall`) go
    through an `ElemBox` record, which holds the integer as a field.
    `ArrayKinds.ptrKind?` gives `Nat` and `Int` no pointer kind
    (`natInt`; also in the whole-program check, the typed `map` loops
    and the lowering's `arrayPtrKindOf`), so an `Array Nat` holds boxes
    and an `Array (Array Nat)` is of kind `A(box)`. `CellKinds.cellKind?`
    gives them no cell kind either (`typed-cells`: a reference of `Nat`
    keeps its cell of boxes; the glue `l2r_rc_set_ref<T, R>` passes the
    old value to the texture `l2r_release_value_then<T, R>`). Thunks and
    tasks hold boxes anyway.
  - **The check.** `Emit/IntBackendCheck.lean` (`intBackendCheck`, run
    by `Main.pipeline` on the finished program under rcgmp without
    `--rcgmp-type-args`) stops lean2rr with an internal error at any call
    of a generic FFI function of the prelude whose type argument mentions
    `Nat` or `Int` (also through a plain generic prelude function that
    passes the type parameter on, `ffiTypeParams`: `lean_array_fget_as<T>`
    calls `l2r_view_take_as<T>`), and at any `RVec`, `LRef` or `LCell` of
    them, in the generated items and in the prelude's text. Test hook:
    `L2R_TEST_NAT_TYPE_ARGS=1` lowers as with `--rcgmp-type-args` but
    keeps the check on (`tests/runtime/int-backend-check.sh`).
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
    to keep the big path apart. Under leanrt nothing changes (the `.rr`
    is byte-identical). `tests/runtime/int-backend-check.sh` checks the
    shape on `RtNatIdxWord`: every `_w` read called, each after its
    `l2r_nat_index`, and no read at a `Nat` that has a twin. A read whose
    `Nat` arguments are not exactly one would keep the `Nat` read without
    a message, and RtNatIdxWord's output is the same either way.
- **Why:** Reussir renders a built-in integer at a polyffi type argument
  as the raw handle and releases it after the call (its `rcgmp_handle`
  comes from the substituted parameter type): `l2r_once_put<Nat>` stored a
  handle that the wrapper then released, `l2r_array_push<Nat>` the same,
  and `l2r_once_get`/`l2r_view_take` copied without a retain (review
  R1-01 of step D: a big closed term and a typed `Array Nat` printed wrong
  sums, exit 0; test `RtNatGenericBig`). A declared `Nat` parameter is
  fine (#795: a borrowed handle). The boxes keep native's words, so casts
  and `ptrAddrUnsafe` of small values stay native's (`RtBoxPassOnCast`,
  `RtCastBoxImm`).
- **Where:** `lean2rr/Main.lean` (options, `filterIntBackend`, the check);
  `NatEncoding.lean`; `PassConfig.lean`, `Opt/Registry.lean` (`config`);
  `Mono.lean` (`MonoConfig.intBackend`, `constComputes`);
  `LowerBase.lean` (`LowerCtx.intBackend`, `natIntTypeArgs`,
  `mentionsNatInt`, `isFfiTypeArgTy`, `cellStorage`, `onceCell`,
  `natIntBoxFns?`, `boxValue`, `boxTake`, `boxUnboxWith`, `boxUnboxed?`,
  `boxAllocates`, `arrayPtrKindOf`, `boxWordReadAs`);
  `Lower/ExternCall.lean` (`bindReadIndex`, `wordReadSym?`);
  `ArrayKinds.lean` (`ptrKind?`);
  `CompactArrays.lean`, `Opt/SplitMapLoops.lean`, `MonoRetype.lean`
  (`natIntKinds`); `CellKinds.lean`, `TypedCells.lean`, `Lower/Externs.lean`
  (`refElemTy`); `Lower/Values.lean` (`natLiteral`); `Lower/Conv.lean`
  (`zeroTry`); `Lower/Live.lean`; `Opt/CheapConsts.lean`;
  `Opt/ModPow2.lean` (`minLitExp`); `Emit/IntBackendCheck.lean`. Tests:
  `RtNatImmEdges`, `RtNatDivZero`, `RtNatLitHuge`, `RtNatGenericFfi`,
  `RtNatGenericBig`, `RtNatIdxWord`, `tests/runtime/int-backend-check.sh`; run.sh's
  `int:NAME` items of an expectation line's `[OPT,…]` prefix and
  `NAME.int-backend`.
- **Remove only if:** the rcgmp backend is dropped; the leanrt paths go
  when the leanrt representation is retired (clean-integration plan, D8;
  rcgmp is the default since 2026-10-25). With an owned handle at type arguments
  (`--rcgmp-type-args`: Reussir's local patch R2, which scripts/l2r.py
  requires for rcgmp) typed arrays, typed cells and once-cells hold `Nat`
  and `Int` directly and the check is off; the guard and the check (rows
  10, 11, 19) stay as a lowering option (for measurements) until it is
  dropped.

### `--int-backend rcgmp`: bit tests and float conversions by rcgmp (`prelude-int-ops`)

- **What:** Under `--int-backend rcgmp` the optional pass
  `prelude-int-ops` (`Opt/PreludeIntOps.lean`, a pass over the mono code
  after Stage 3, after `float-lits`) replaces three Lean definitions by
  the prelude's rcgmp functions:

  | Lean | Lean's code | prelude (rcgmp block) |
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
  - **leanrt.** The pass does nothing. The leanrt block's
    `l2r_nat_test_bit` is Lean's definition, the same three operations
    with the same `m >>> i`, so the rewrite would add nothing there; the
    leanrt block has no float conversions. The `.rr` of every program
    under leanrt is the same as without the pass.
  - `L2R_DEBUG=1` prints, per definition, the calls and instances
    rewritten (`lean2rr: prelude-int-ops: Nat.testBit: 2 call(s) and 1
    instance(s) rewritten to l2r_nat_test_bit`).
- **Why:** `m >>> i` makes a new number for a big `m` at every test (Z03b,
  the regex backtracker's bit matrix of states times positions); from
  2^53 on, `Float.ofScientific` builds `Float.Model` values with bignum
  arithmetic in time quadratic in the number's bits. Cachegrind
  instructions under rcgmp (SVE-free builds, with the pass against
  without it): Z03b 19.16 → 18.88 G (−1.5 %; the rest of its gap to
  leanrt is `|||` on big numbers); a loop of `toFloat` on small, 2-limb
  and negative 2-limb values 4.17 G → 80.1 M (100000 rounds, about 41700
  → 800 per round), on small values only 41.5 → 17.5 M (a million
  rounds); `testBit` at every bit of a 9512-bit number, 20 times, 142.6 →
  7.8 M.
- **Where:** `lean2rr/LeanToReussir/Opt/PreludeIntOps.lean`;
  `Opt/Registry.lean`; `runtime/prelude.rr` (the rcgmp block's
  `l2r_nat_test_bit`, `l2r_float_of_nat`, `l2r_float_of_int`). Tests:
  `RtNatTestBit`, `RtFloatOfNatInt` (each with a `.l2r-debug` check that
  the rewrite runs under rcgmp and not under leanrt).
- **Remove only if:** Lean inlines these definitions (then the pass must
  match the inlined code), or Reussir lowers Lean's code to the same
  operations.

### `--int-backend rcgmp`: a case split is a Reussir `match` (`int-match`)

- **What:** Under `--int-backend rcgmp` the optimization `int-match`
  (on by default; nothing under leanrt) lowers Lean's case splits on a
  `Nat` or `Int` to a Reussir `match` on the built-in integer, which
  Reussir compiles to one `rcgmp.match` over integer intervals.
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
  2026-10-25, rcgmp with the pass against `--disable-opt int-match`): a
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
  `PassConfig.intMatch`, only under rcgmp); `PassConfig.lean`,
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
  `tests/runtime/int-match-check.sh` (the shapes; none with the pass off;
  leanrt's `.rr` unchanged).
- **Remove only if:** the rcgmp backend is dropped, or Reussir rebuilds
  no value from a `match` (then the copy goes).

### Reussir counts only the even words (tagged opaque handles, patch 10-a)

- **What:** The prelude declares `#[ffi(rust = "::leanrt::nat::LNat",
  tagged)] pub struct Nat;` (and `Int`). With Reussir patch 10-a, `rc.inc`
  of a `tagged` handle touches the count, and `rc.dec` calls the drop hook,
  only when the low bit is clear; the nonlinear-FFI instrumentation and
  `rc.assume_unique` skip such handles too. Copying or dropping a small
  value is a bit test, and it is never allocated.
- **Why:** Reussir inserts the reference counting itself and increments
  an opaque handle at its address; a small `Nat` has no address. A clone
  hook would cost a call per copy; lean2rr cannot count `Nat`s itself
  because it cannot change the drop glue Reussir generates for records,
  closures and enums.
- **Where:** `reussir-bugs/patches/10-a-tagged-ffi-objects.patch` and
  [issue 10](../../../reussir-bugs/10-tagged-ffi-objects.md)
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
    `lean_int16_to_int` and `lean_int32_to_int` (an `int32`),
    `lean_int64_to_int_sint` and `lean_isize_to_int` (through
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
  - copies of existing words: a record's or a `Box`'s field (an
    `Array Int`'s elements are boxes), a once-cell's value, a reference's
    or a task's value.
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
  array indices (`l2r_word_index_ok`); `leanrt/src/nat.rs`: the slow paths (`nat_add`, ... every
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
- **Where:** `prelude.rr`: `lean_nat_*`, `lean_int_*`, `l2r_int_word_val`.
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
  raises SIGFPE (LB-05). Below it, an allocation that fails ends the same
  way: the blocks, and the scratch limbs and the decimal text of
  `Nat.repr`/`Int.repr` (`big::zeroed`, `nat::big_decimal`; review HB-02:
  those two aborted without a message). The step changed no generated code: the classic
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

### The `Nat` and `Int` slow paths are `#[cold]`: the small path falls through

- **What:** The `leanrt::nat` slow paths that the prelude calls only
  after a small-word test are `#[cold]` (and `#[inline(never)]`, as
  before): `nat_add`, `nat_sub`, `nat_mul`, `nat_div`, `nat_mod`,
  `nat_cmp`, `nat_eq`, `nat_land`, `nat_lor`, `nat_xor`, `nat_shiftl`,
  `nat_shiftr`, `nat_log2`, `nat_pow`, `nat_sat_u64`,
  `nat_replicate_len`, `nat_low_u64`, `nat_to_int`, `nat_neg_succ`;
  `int_neg`, `int_add`, `int_sub`, `int_mul`, `int_div`, `int_mod`,
  `int_ediv`, `int_emod`, `int_cmp`, `int_eq`, `int_nat_abs`,
  `int_is_neg`, `int_low_twos`. Not the ones called for every value
  (`nat_gcd`, `nat_repr`, `int_repr`).
- **Why:** Reussir's language has no branch hint, so the prelude's
  `if` cannot say which arm is likely. rustc puts `cold` on the
  declaration of each slow path in the textures that call it, and LLVM
  infers `cold` for the texture (`l2r_nat_add_raw`, ...). LLVM then
  takes the branch to the call as unlikely, as native Lean's
  `LEAN_LIKELY(lean_is_scalar(..))` makes it: the small path falls
  through and the call is laid out after the loop. E08 (matrix_uint64)'s
  product loop: 14.2 taken branches an iteration before, 10.1 after
  (native 6.0; callgrind, about the same instruction count). Most of the
  rest are the guards of Reussir's `rc.inc` of a tagged handle, which
  have no weights. Wall time (median of 9, interleaved, pinned; dev
  5604d38f): E08's kernel 33.1 ms before, 27.3 ms after (native 28.4);
  E01 (gcd_batch)'s kernel 24.4 ms, 23.5 ms (native 25.2); L11 (bignum,
  big numbers on the slow paths) 2276 ms both (native 2287). The `Int`
  ones (dev 9dabadcc): X13 (tak)'s `tak` 5.3 taken branches a call
  before, 3.7 after (44.0 and 42.7 instructions); its kernel 20.05 ms,
  19.84 ms (native 22.32; faster in 9 of 9 paired rounds); E06
  (expr_eval)'s kernel 29.66 ms, 29.50 ms; L10 (liasolver) 683 ms,
  682 ms; L15 (monadic-interp) 1081 ms, 1079 ms; E01 unchanged.
- **Where:** `leanrt/src/nat.rs`: the slow paths, and the comment above
  them.
- **Remove only if:** Reussir's language gets branch hints that the
  prelude uses instead.

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
  low-bit test of Reussir's `rc.inc` of `y` (patch 10-a's guard; `y` is
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

### A bitwise operation runs one loop per operation over slices that do not overlap

- **What:** `big::bitwise` (`Nat`'s `&&&`, `|||`, `^^^` on big numbers)
  writes into the longer operand's block when it is unique, else into the
  shorter one's when it is unique and has room, else into a fresh block,
  each with its own loop for each of the three operations (`bits_into` for
  a result in an operand's block: `r[i] op= y[i]`; a zip of three slices
  for a fresh block, its limbs written as `MaybeUninit`). The two blocks
  of `bits_into` are different: a unique operand is never the other
  operand (that would be a second reference).
- **Why:** The former single loop selected the operation per limb and
  could write over one of its sources, so LLVM either kept it scalar
  (9 instructions a limb without SVE) or vectorized it behind a runtime
  overlap test that fails when the result is in a source's block, the
  usual case (`b ||| (1 <<< i)` into a unique `b`: a wide `BitVec`'s
  `set`). Now that test compares two different blocks and passes, and the
  loop runs vectorized (NEON, 8 limbs an iteration, with or without
  SVE). Z03b (lean-regex's backtracker, whose
  visited set is a `BitVec` of states times positions) spent 47% of its
  instructions in the loop.
- **Where:** `leanrt/src/big.rs`: `bitwise`, `bits_into`; unit tests
  `big::tests::against_mpz` and `mixed_ownership` (every branch, against
  GMP's `mpz_and`, `mpz_ior`, `mpz_xor`).
- **Remove only if:** GMP's `mpn_and_n`/`mpn_ior_n`/`mpn_xor_n` are used
  instead (unrolled scalar code, about 3.5 instructions a limb).

### A division by a bigger divisor returns the dividend or zero at once

- **What:** For the truncated division (`Nat./`, `Nat.%`, `Int.tdiv`,
  `Int.tmod`), and for the Euclidean one (`Int.ediv`, `Int.emod`) of a
  non-negative `a`, `big::div` first compares the magnitudes (the limb
  counts, then `mpn_cmp` for equal counts). When `|a| < |b|` the
  remainder is `a` itself (`b` is dropped) and the quotient zero (in an
  operand's block when one is unique, `zero`). A negative `a` under
  `ediv`/`emod` (one away from those) and `|a| >= |b|` take the general
  path.
- **Why:** The general path computes the remainder in scratch limbs (on
  the heap, zeroed, beyond 32 limbs), copies `a` into them, then copies
  them into a result block (an operand's when one is unique, else a fresh
  one): two copies, and up to two allocations, to give back `a`. Every
  wide `BitVec` operation that makes a value computes `x % 2^w`
  (`BitVec.ofNat`), mostly for an `x < 2^w`. Z03b's `b ||| (1#w <<< i)` did so once per bit set:
  about a third of its instructions after the bitwise loop's
  vectorization. With `mod-pow2` (below) these `x % 2^w` make no division;
  the early return stays for every other division.
- **Where:** `leanrt/src/big.rs`: `div`; unit tests
  `big::tests::against_mpz` and `mixed_ownership` (the four divisions on
  operands of equal and of different lengths, signed, unique, shared and
  roomy, against GMP's `mpz` divisions).
- **Remove only if:** never (the result is the same; the test is a
  limb-count comparison, and `mpn_cmp` only for equal counts).

### `x % 2^w` is the low `w` bits of `x`, without `2^w` (`mod-pow2`)

- **What:** The optional pass `mod-pow2` (`Opt/ModPow2.lean`, after Stage 3)
  rewrites `Nat.mod x p` where `p` is bound in the same declaration to
  `Nat.pow 2 w`, to `Nat.shiftLeft 1 w`, or to the literal `2^k` with
  `k ≥ 63` (`k ≥ 61` under `--int-backend rcgmp`, whose immediates end
  at 2^61: `minLitExp`, `natSmallBits`; also a read of a constant whose
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
  computes two small words in line (the word `2v+1` keeps its low `w + 1`
  bits; `w ≥ 63` keeps `x`); the rest is `leanrt::nat::nat_truncate_bits`:
  a big `w` (2^63 or more) keeps `x`; a big `x` goes to
  `big::nat_truncate_bits`, which returns `x` itself when it has at most
  `w` bits, zero in `x`'s block for `w = 0`, and else the `w / 64` low limbs
  and the masked next one, in `x`'s block when it is unique, in a new block
  when it is shared. Example: `BitVec.ofNat w x` (every `BitVec` `+`, `*`,
  `<<<`, `1#w`) was `let p := Nat.pow 2 w; Nat.mod x p` and is now
  `L2RNat.truncateBits x w`.
- **Why:** `Nat.pow 2 w` made a number of `w / 64 + 1` limbs on every wide
  `BitVec` operation (zeroed, then the top bit set), and the division then
  compared it with `x`. lean-regex's backtracker (Z03b) sets one bit of a
  vector of states times positions per step (`b ||| (1#w <<< i)`: three
  truncations): 42% of its instructions were the `memset` of these powers
  after the runtime's fixes of its bitwise operations and divisions.
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
  too big`), and in lean2rr without the pass above `big::MAX_BITS` bits;
  the truncation needs no power, so it gives the value there too, as
  lean-runtime lifts native's limits where the result can be computed
  (LB-11). A literal divisor below 2^63 is a small word, whose `%` the
  prelude computes in line (LLVM makes it an `and`); the rule leaves it.
- **Where:** `Opt/ModPow2.lean` (`rewrite`, `dropUnused`, `literalPows`,
  `truncDecl`); `Opt/Registry.lean` (`mod-pow2`); `prelude.rr`:
  `l2r_nat_truncate_bits`, `l2r_nat_truncate_bits_raw`;
  `leanrt/src/nat.rs`: `nat_truncate_bits`; `leanrt/src/big.rs`:
  `nat_truncate_bits`; unit tests `nat::tests::truncate_bits` (small and
  big `x` and `w`, `w` of 2^32, 2^63 and 2^64 + 1), `big::tests::against_mpz`
  and `big::tests::mixed_ownership` (against GMP's `mpz_fdiv_r_2exp`,
  unique, shared and roomy, `w` at the limb edges, around the bit length,
  2^40 and 2^64 - 1); runtime test `RtNatModPow2` (with
  `RtNatModPow2.l2r-debug`: calls rewritten, and `program casts: no`).
- **Remove only if:** Lean computes `BitVec.ofNat` without `2 ^ w`; else
  never (speed only).

### A truncated quotient uses GMP's quotient-only division

- **What:** `big::div` computes the truncated quotient (`Nat./`,
  `Int.tdiv`) by a divisor of two limbs or more with `mpz_tdiv_q` on
  read-only views of the operands (`view`), and copies the result into an
  operand's block when one is unique (`either`), else into a fresh one.
  The other divisions keep `mpn_tdiv_qr` (the remainders, and `Int.ediv`,
  which needs to know whether the remainder is zero when the dividend is
  negative); a one-limb divisor keeps `mpn_divrem_1`.
- **Why:** `mpz_tdiv_q` (through `mpn_div_q`) computes an approximate
  quotient and corrects it; `mpn_tdiv_qr` also forms the remainder, a
  further multiplication of the divisor's size. Native Lean's `Nat./` and
  `Int.tdiv` use `mpz_tdiv_q` (`mpz::operator/=`), its `Int.ediv`
  `mpz_tdiv_qr`. The classic Bignum (L11: Newton square roots, `n! /
  (n-1)!`, Int divisions of big operands) made 27% more of GMP's
  multiplications than native, all inside divisions by multi-limb
  divisors (callgrind: 361 K multiplications from those divisions, native
  134 K).
- **Where:** `leanrt/src/big.rs`: `div`; unit tests `big::tests`
  (`large_mixed`: `int_tdiv` against `mpz_tdiv_q` for operands of 1 to 70
  limbs, signed, unique, shared and roomy, and `(a * b) / b == a`;
  `nat::tests` against `u128` arithmetic).
- **Remove only if:** GMP's `mpn_tdiv_qr` gains a quotient-only mode.

### Literals: small below 2^63, big ones parsed from their decimal text

- **What:** A `Nat` literal below 2^63 (`natIsSmall`) is
  `l2r_nat_small(k)` (the word `2k+1`); a bigger one is
  `l2r_nat_of_decimal_lstr(s)`, with `s` the decimal digits in the string
  literal table.
- **Why:** 2^63 is the small range. A nested arithmetic expression per
  limb overflowed rrc's stack at about 20000 digits and cost quadratic time
  (adv2 N1, fbf37e8).
- **Where:** `Lower/Values.lean`: `natLiteral`; `NatEncoding.lean`:
  `natIsSmall`; `prelude.rr`: `l2r_nat_small`, `l2r_nat_of_decimal_lstr`;
  `leanrt/src/nat.rs`: `nat_of_decimal`.
- **Remove only if:** the encoding changes; the flat call is cheaper
  anyway. Plan [§5.4](../../translation-plan.md#54-let-return-literals).
  Under `--int-backend rcgmp` every literal is Reussir's own (see the
  lowering's entry above).

### `Nat` and `Int` are FFI-boundary types

- **What:** `isBoundaryTy` counts `Nat`/`Int` as runtime handles: a `Box`
  holds the handle like any other value, and a once-cell holds it directly
  (the prelude's `L2RNatRef`/`L2RIntRef` are gone).
- **Why:** They are counted handles now, which Reussir passes across the
  FFI boundary and keeps in cells (the old Reussir bug with cells, fixed
  upstream in #666 and #681, only concerned `[value]` records).
- **Where:** `LowerBase.lean`: `isBoundaryTy`, `refType`.
- **Remove only if:** `Nat` stops being a counted handle. Under
  `--int-backend rcgmp` without `--rcgmp-type-args` a `Nat`/`Int` is a
  parameter type of the FFI but no type argument (`isFfiTypeArgTy`: a
  once-cell holds it in an `ElemBox`; the lowering's entry above).

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
