# `Nat` and `Int`

Paths: `runtime/prelude.rr`, `runtime/leanrt/src/`, and
`lean2rr/LeanToReussir/` for lean2rr's files.

### `Nat` and `Int` are two-word value enums, not tagged words

- **What:** `enum [value] Nat { Small(u64), Big(LBig) }` and
  `enum [value] Int { Small(i64), Big(LBig) }`. `Big` only holds values
  outside the machine word (`Nat` ≥ 2^64, `Int` outside `i64`); every
  function that may come back into range normalizes. Small arithmetic is
  inline prelude code (an add with an overflow check); only the slow path
  calls the runtime, whose big numbers (`LBig = Rc<(bool, Vec<u64>)>`) use
  GMP and are updated in place when unique.
- **Why:** Native Lean's tagged word (`2n+1`) cannot be used: Reussir
  generates the reference counting and treats every heap handle as a real
  pointer, so a tagged number would be "incremented" at an address. Reussir
  has immediates only for its own nullary constructors.
- **Where:** `prelude.rr` (`Nat`, `Int`, `lean_nat_*`, `lean_int_*`);
  `leanrt/src/big.rs`, `gmp.rs`; `LowerBase.lean`: `lowerTypeApp`; plan
  [§5.1](../../translation-plan.md#51-type-translation).
- **Remove only if:** Reussir supports small integers as immediates (a
  feature request, not a bug fix). Costs: a `Nat` field takes 16 bytes,
  and a big number is two allocations. Tagged words are used where
  Reussir never sees them: inside `Array Nat`/`Array Int`
  ([arrays.md](arrays.md#array-nat-and-array-int-store-one-word-per-element))
  and `Nat`/`Int` references
  ([references.md](references.md#nat-and-int-references-keep-a-tagged-word-and-a-big-number-cell)).

### Big `Nat` literals are parsed from their decimal text

- **What:** A literal below 2^64 is `Nat::Small{k}`; a bigger one is
  `l2r_nat_norm(l2r_big_of_decimal_lstr(s))`, with `s` the decimal digits
  in the string literal table.
- **Why:** A nested arithmetic expression per limb overflowed rrc's stack
  at about 20000 digits and cost quadratic time (adv2 N1, fbf37e8).
- **Where:** `Lower/Values.lean`: `natLiteral`; `prelude.rr`:
  `l2r_big_of_decimal_lstr`; `leanrt/src/big.rs`: `of_decimal`.
- **Remove only if:** rrc handles deep expressions; the flat call is
  cheaper anyway. (Plan
  [§5.4](../../translation-plan.md#54-let-return-literals) still describes
  base-2^32 digits combined by runtime arithmetic; the code above is what
  runs.)

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
  `prelude.rr`: `l2r_nat_repr`, `l2r_nat_repr_small`, `l2r_int_repr`;
  `Opt/PreludeRepr.lean`.
- **Remove only if:** the strings are the same either way; the pass and
  the table only save time and allocations. The runtime keeps the
  functions when the pass is off.

### Indices and positions are never `Nat::Big`

- **What:** An index that is in bounds (a `Fin`, or after the bounds test
  of `get!`) or a position proved valid converts with
  `l2r_index_of_nat`, whose `Big` arm ends the program. Where Lean's C code
  tells "not a scalar" apart from "out of range", the prelude does too: a
  `Nat` ≥ 2^63 (`lean_string_utf8_extract`), an `Int` outside the 32-bit
  range (`Float.scaleB`).
- **Why:** See
  [../ownership.md](../ownership.md#reads-take-their-container-owned-and-in-bounds-indices-end-on-natbig).
- **Where:** `prelude.rr`: `l2r_index_of_nat`, `l2r_index_ok`.
- **Remove only if:** see the linked entry.
