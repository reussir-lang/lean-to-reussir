# Casts between different types (`unsafeCast`)

Mono erases `unsafeCast`, so a value can reach code expecting another type
that Lean represents alike. lean2rr converts as Lean's representation reads
the value: native layout slots, `lean_box`/`lean_unbox`. Paths are relative
to `lean2rr/LeanToReussir/`. Plan
[§5.1](../../translation-plan.md#51-type-translation) ("Through
`unsafeCast`…") and [§5.5](../../translation-plan.md#55-cases) ("Cast
values"); divergences in
[§10](../../translation-plan.md#10-known-divergences-and-unsupported-features)
("Casts that natively read an address").

### Fields pair by native layout slot

- **What:** When one inductive is read as another, each field of the
  target constructor reads the source field at the same slot of Lean's
  native layout (object fields in declaration order, then `usize` fields,
  then other scalars by decreasing size: Lean's `getCtorLayout`), not the
  same declaration position. Same-size scalars are reinterpreted. A field
  that reads data the source does not have (or part of a scalar) makes the
  pair non-isomorphic.
- **Why:** `S₁ {a : UInt8, b : Nat}` read as `S₂ {x : Nat, y : UInt8}` is
  natively `x = b`, `y = a` (adv4 RP4-04, ca9b64d).
- **Where:** `Lower/Conv.lean`: `nativeSlots`, `castFieldMap`,
  `isomorphic`, `convArms`; `Lower/Values.lean`: `viewLayout`.
- **Remove only if:** never.

### Words convert as `lean_box` and `lean_unbox` read them

- **What:** `Nat`, `Int`, `UInt8/16/32`, `Char`, `Bool`, enumerations and
  constructors without fields are boxed scalars natively, and convert
  through their word: truncated to the target's width (`300 : Nat` read as
  `UInt8` is 44; `Bool` is the low byte being nonzero); an index past an
  enumeration's last constructor selects the last one (Lean's `switch`); a
  small `Int` is its 32 bits; a word read as an `Int` is signed 32 bits;
  `Nat` → `Int` is by value, and `Int` → `Nat` reads a small `Int` as the
  `Nat` of its 32 bits (`-5` is `2^32 - 5`) and a big one as its magnitude;
  an index selects the nullary constructor at that position, and back.
- **Why:** That is what native code computes (adv4 RP4-05/RP4-06,
  ca9b64d).
- **Where:** `Lower/Conv.lean`: `wordOf`, `ofWord`, `scalarWord`,
  `wordCastable`, `isWordTarget`, `isPureWord`, `ctorWordFn`,
  `ctorOfWordFn`, `enumIndexFn`, `enumOfIndexFn`; `runtime/prelude.rr`:
  `l2r_int_cast_nat`.
- **Remove only if:** never.

### An object read as a word gets a deterministic stand-in address

- **What:** An object read as a word (a constructor with fields, a
  string, an array, a closure, a thunk, a float cell) gives `2^44 + 8i` for
  a constructor with fields of index `i` and `2^44` otherwise; a big `Nat`
  or `Int` gives the low bits of its value; a word read as `USize` is the
  word. For strings, arrays, closures, cells, and inductives without a
  constructor without fields, these conversions happen only where the
  program performs a cast (`castFallback`, and the `Box` arms of casting
  programs), never when `tryCoerce` merely asks whether two representations
  convert. An inductive that has a constructor without fields is a word
  target already in `tryCoerce`: its constructors with fields give
  `2^44 + 8i` there too (`Option Nat` read as `Nat`: `some _` is
  `2^44 + 8`).
- **Why:** Natively the word is the object's address shifted, different
  on every run; the stand-in has the properties every address has
  (nonzero, a multiple of 4, far above any constructor index). If
  `tryCoerce` accepted it, every function type over a `String` would
  convert to the same one over a `Nat` (e8feb4a).
- **Where:** `Lower/Conv.lean`: `objectWordBase`, `isOtherObject`,
  `isObjectNominal`, `wordCastable` (`objects`), `ctorWordFn`,
  `castFallback`, `coerce`.
- **Remove only if:** never.

### `Float` and `UInt64` (and `Float32` and `UInt32`) cast by their bits

- **What:** A cast between `Float` and `UInt64`, or `Float32` and
  `UInt32`, copies the bits, NaN payloads included.
- **Why:** `Float.ofBits` canonicalized NaNs (round 6 U1, 853288f). A
  `Float32`/`UInt32` cast crashes natively (a tagged scalar against a
  cell); it is not tested (RV6L-03).
- **Where:** `Lower/Conv.lean`: `tryCoerce`; `runtime/prelude.rr`:
  `l2r_f64_of_raw_bits`, `l2r_f64_raw_bits`, `l2r_f32_of_raw_bits`,
  `l2r_f32_raw_bits`.
- **Remove only if:** never.

### Inductives that do not correspond convert by tag

- **What:** A cast the program performs between inductives with
  different constructor counts (`Sum3 | a | b (x : Nat) | c (y : String)`
  read as `Option`) converts constructor by constructor as Lean's `cases`
  reads the value: by tag (past the target's last constructor, the last
  one), a target constructor without fields whatever the source holds,
  fields by native slot, no value for a source without the fields the
  target reads.
- **Why:** Natively the value is read as it is (18fb171, test
  `RtCastBox`).
- **Where:** `Lower/Conv.lean`: `ctorCastable`, `ctorAtTag`, `convArms`,
  `coerce`.
- **Remove only if:** never. Through a `Box` such casts stay unreachable
  ([box-unboxing.md](box-unboxing.md#other-types-variants-only-in-a-program-that-can-cast)).

### A `cases` on a cast value matches through the value's own constructors

- **What:** A `cases` (or projection) whose discriminant has another
  type than the one matched: a value of an isomorphic inductive is matched
  through its own constructors, position by position, each field bound
  from the source field at the same native slot at its own type (no
  conversion of the whole value); a word matched as an enumeration, or an
  enumeration as `Bool` or as one with another constructor count, is
  converted by index first; anything else is converted to the matched
  type's instance; a type without representation runs its only
  alternative.
- **Why:** The alternatives were looked up in the wrong type's
  constructors: every arm was dropped ("unreachable code"), or the program
  was rejected ("bad constructor", "cases on non-nominal type") (adv3
  RP3-4/RP3-5, 8cf7987).
- **Where:** `Lower/Values.lean`: `CastCases`, `castCases`, `viewLayout`;
  `Lower/Code.lean`: `lowerCases`; `Lower/Hooks.lean`: `CasesArm.view`.
- **Remove only if:** never.

### A cast with no conversion warns and panics at run time

- **What:** Where no conversion exists, lean2rr prints `lean2rr:
  warning: no representation conversion from … to …` and emits
  `l2r_internal_panic_at`, which prints Lean's `INTERNAL PANIC:
  unreachable code has been reached` and exits 1 if the cast runs.
- **Why:** The program is still translated (adc9180); natively such a
  cast crashes or reads garbage. The driver shows lean2rr's warnings even
  when it succeeds (adv4 RP4-10, 270eef4).
- **Where:** `Lower/Conv.lean`: `coerce`; `runtime/prelude.rr`:
  `l2r_internal_panic_at`; `scripts/l2r.py`: `run` (`show_stderr`).
- **Remove only if:** never.
