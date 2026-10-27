# Reussir bugs that affect what a program computes

One entry per bug: what lean2rr does, which Reussir change fixes it, and
whether the workaround can be dropped. Every issue here was a bug
(erroneous behaviour), and upstream Reussir `7954a367` fixes each one, so
its file in `reussir-bugs/` is gone (the headings give the old entry
numbers). lean2rr's builds use a later base, upstream `95d9a1c8` with
the series (`./reussir` branch `l2r-base12`, `c1170ff9`); the
workarounds stay until each is removed.
Issues 1 (a missed optimization) and 2 (a missing feature), which
are not bugs, are in [limitations.md](limitations.md). The open issue
files are in [`reussir-bugs/`](../../../reussir-bugs/README.md).
Paths: `lean2rr/LeanToReussir/` for lean2rr's files.

### Old bug 1: `[value]` enum payloads were lost when moved

- **What:** No workaround since 2026-10-19. Outline's step enums are
  `[value]` whatever their field types
  ([../control-flow/outline.md](../control-flow/outline.md#step-enums-are-value)),
  and so is the entry enum of a `state-machines` state machine whose
  variant keeps a field
  ([../control-flow/state-machines.md](../control-flow/state-machines.md)).
  Before, lean2rr emitted only `[value]` enums that the bug did not affect
  (field-less enumerations, and step enums whose representative arm surely
  carried every byte of the other arms, by a layout model of the field
  types); the other enums were shared, a heap cell per value. The core
  form's J4 entry enum stays shared for its cost: token reuse gives it
  the matched variant's cell, and a `[value]` enum, measured, ran more
  instructions
  ([../control-flow/state-machines.md](../control-flow/state-machines.md#a-loop-through-outlined-join-points-is-one-state-machine)).
- **Why:** Reussir moved a `[value]` enum as one representative arm's
  struct, so another arm's bytes on its padding or on an `i1` were lost.
  Reussir #663 (commit `823a7b29`, formerly a local patch) fixes it:
  `opaquePayloadType` in `lib/Conversion/TypeConverter/TypeConverter.cpp`
  makes the payload an array of alignment-sized integers when a move of
  the representative would lose another arm's bytes. Reussir has it
  since `7954a367` (so lean2rr's base `95d9a1c8` has it), and
  `scripts/l2r.py` stops on a Reussir checkout without lean2rr's series
  (patch 23-f, which plain upstream and the bases before Phase 2 lack).
  Checked on `l2r-base3` (2026-10-19) with a minimal program: a
  `[value]` enum of six arms of different sizes (`f64`, `bool`, `u8`,
  `u16`, padding, a counted pointer, a nested
  `[value]` struct with padding and a nested `[value]` enum), moved
  through two loops (self tail calls), calls, a `[value]` struct's field,
  a shared record's field and matches, at `-O none`, `default` and
  `aggressive`, with and without `--no-pack-record-members`: every result
  right, and 3000000 iterations on a 1 MiB stack at `-O default` and
  `aggressive`. The enum's LLVM type is `{ i8, [5 x i64] }`.
- **Where:** `Outline.lean`: `stepItem`; `Opt/StateMachines.lean`:
  `emitStateMachineAlongside` (`Lower/StateMachine.lean`:
  `emitStateMachine` keeps its shared enum, for its cost). Tests:
  `RtOutlineValueSteps` (`fmix`, `floaty`), `RtSmGuard`
  (`tests/runtime/sm-slots-check.sh`).
- **Remove only if:** n/a: nothing is left to remove. The core form's
  entry enum and the program's own inductives with fields stay shared for
  other reasons
  ([../representations/records.md](../representations/records.md#three-shapes-and-value-enums-only-without-fields)).

### Old bug 2: in-place reuse skipped a field store

- **What:** The driver passes `--no-pack-record-members`, and lean2rr
  orders each constructor's fields by decreasing alignment itself, so
  records have no padding between members and equal member types at
  indices 0..i put member i at the same offset.
- **Why:** Reussir's copy avoidance skips storing a field it believes is
  in place; with packed layouts the variant check is wrong (a wrong value,
  no error). Reussir fixes the structure half (#652, commit `3be77a64`,
  in the old base `943f2195`) and the variant half (#656, commit
  `c7ab73d5`, the offset rule; formerly a local patch) (444a70a,
  7860807).
- **Where:** `scripts/l2r.py` (`--no-pack-record-members`);
  `Opt/FieldOrder.lean`; `LowerBase.lean`: `nominalType`, `fieldAlign`.
- **Remove only if:** the flag is removable after the move to Reussir
  7954a367. `field-order` itself is optional; it stays for records
  without padding.

### Old bug 4: rrc recursed forever on two equal recursive types

- **What:** When rrc dies from a signal, `scripts/l2r.py` retries without
  `--reuse-across-call` (and says so on stderr).
- **Why:** Reussir's structural type comparison crashed on a user list and
  `List` (456bc97). Reussir fixes it (#654, commit `634fb551`, formerly a
  local patch; in the old base `943f2195`).
- **Where:** `scripts/l2r.py`: `main`.
- **Remove only if:** it stays as a fallback for unknown crashes; it costs
  nothing when rrc does not crash.

### Old bug 5: TokenReuse crashed on a one-armed `if`

- **What:** The runtime's own diagnostics (index out of bounds,
  `String.get!`, `dbgTraceIfShared`) reach `l2r_stderr_put` from Rust,
  through the program's `extern "C"` trampoline `l2r_stderr_put_c`
  (descriptor 2 without one), instead of a Reussir-level call.
- **Why:** A Reussir-level call from the prelude's array helpers into the
  stream code made rrc crash in `TokenReusePass` under
  `--reuse-across-call` (caea747; RtStreamsRedirectOob). Reussir's
  `main` fixes the crash (#655, commit `943f2195`, formerly a local patch;
  the old base); user code could still hit it on an older Reussir.
- **Where:** `runtime/prelude.rr`: `l2r_panic_code`, `l2r_diag_put`;
  `runtime/leanrt/src/io.rs`: `diag_put`; `Emit/Entry.lean`: `lowerEntry`.
- **Remove only if:** removable after the move to Reussir 7954a367 (not
  needed since the old base `943f2195`); the trampoline is cheap and may
  stay.

### Old bug 6: a static cell was freed after about 2^32 references

- **What:** No lean2rr-side workaround: the retains come from Reussir's
  own lowering of nullary constructors. lean2rr relies on Reussir's fix
  (#661, commit `198213ff`, formerly a local patch); the documented
  flag alternative
  (`--nullary-variant-encoding arch-independent` or `boxed`, through
  `L2R_RRC_FLAGS`) is not used. The runtime's array code relies on an
  immediate never being freed: it skips immediates when freeing or
  copying arrays of records (aarch64).
- **Why:** the fix keeps the default encoding's speed (to be remeasured on
  an idle machine).
- **Where:** `scripts/l2r.py` (`L2R_RRC_FLAGS`, 42dacc7);
  `runtime/leanrt/src/drop.rs`: `ReleaseElems`;
  `runtime/leanrt/src/array.rs`: `ExtendCloned`.
- **Remove only if:** n/a: the skips stay. If the flag replaces the
  default encoding, revisit the immediate skips ([../ownership.md](../ownership.md#array-copies-skip-the-increments-of-immediates)).

### Old bug 19: a `Cell` of a `[value]` record with counted members

- **What:** A Reussir cell holds no `[value]` record: a reference's cell
  holds a `Box` (one reference type), a once-cell a value of a boundary
  type or an `ElemBox` (`Nat`/`Int`, `[value]` enums before patch 10-a,
  are counted handles now, which cells hold directly).
- **Why:** rrc rejected `cell::get`/`set` on such a cell (fixed upstream
  in Reussir #666, commit `3f96d206`, and #681, commit `1ec611dc`;
  formerly a local patch).
- **Where:** [../representations/references.md](../representations/references.md#a-reference-is-one-record-type-around-a-reussir-cell-of-a-box);
  `LowerBase.lean`: `cellStorage`.
- **Remove only if:** removable after the move to Reussir 7954a367.

### Old bug 21: an unterminated `[:` in a texture was dropped

- **What:** `[` is written as `\x5b` in the string literal table.
- **Why:** Reussir dropped the `[:` and the text after it (fixed
  upstream in Reussir #657, commit `fec8f033`; formerly a local patch);
  round 6 RV6L-01.
- **Where:** [../representations/strings.md](../representations/strings.md#-is-escaped-in-the-string-literal-table).
- **Remove only if:** removable after the move to Reussir 7954a367; the
  escape is free and may stay.
