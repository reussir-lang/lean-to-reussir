# Reussir bugs that affect what a program computes

One entry per bug: what lean2rr does, which Reussir change fixes it, and
whether the workaround can be dropped. Every issue here was a bug
(erroneous behaviour), and upstream Reussir `7954a367` fixes each one, so
its file in `reussir-bugs/` is gone (the headings give the old entry
numbers). lean2rr's builds use that base (`./reussir` branch
`l2r-base3`, `4c490260`); the workarounds stay until each is removed.
The last entry, the drain-end hook, is a local addition for an open issue
(9). Issues 1 (a missed optimization) and 2 (a missing feature), which
are not bugs, are in [limitations.md](limitations.md). The open issue
files are in [`reussir-bugs/`](../../../reussir-bugs/README.md).
Paths: `lean2rr/LeanToReussir/` for lean2rr's files.

### Old bug 1: `[value]` enum payloads were lost when moved

- **What:** lean2rr emits only `[value]` enums that are unaffected:
  field-less enumerations (`Nat`/`Int` are tagged handles since patch
  10-a, not `[value]` enums), and Outline's step enums whose
  representative arm surely carries every byte of the other arms (a layout
  model checks it; otherwise the step enum is shared:
  [../control-flow/outline.md](../control-flow/outline.md#step-enums-are-value-when-their-layout-is-safe-to-move)).
  Everything else with several arms is a shared enum
  (J4 entry enums with fields included: the core form's, and the
  `state-machines` form's when a field has no slot; with only nullary
  variants that form's entry point is an integer, not an enum);
  multi-field value records are `[value]` structs.
- **Why:** Reussir moves a `[value]` enum as one representative arm's
  struct, so another arm's bytes on its padding or on an `i1` were lost
  (fixed upstream in Reussir #663, commit `823a7b29`; formerly a local
  patch).
- **Where:** `LowerBase.lean`: `nominalType`, `tupleType`;
  `Lower/StateMachine.lean`: `emitStateMachine`;
  `Opt/StateMachines.lean`: `emitStateMachineAlongside`;
  `Outline.lean`: `stepItem`, `fieldLayout`.
- **Remove only if:** removable after the move to Reussir 7954a367.
  Without the workaround, J4 entry enums with fields and multi-arm value
  types could be `[value]`.

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

### The drain-end hook (local patch 09-a)

- **What:** The runtime stores a callback in Reussir's
  `__reussir_drop_drained`, which local patch 09-a makes every outermost
  drain that released something call when it ends. lean2rr requires the
  patch since switch step 6: `scripts/l2r.py` stops with an error when the
  Reussir checkout lacks it (`check_reussir_patches`), and leanrt names the
  symbol (`task::hook_drained`), so it would not link either. The
  patch is [`reussir-bugs/patches/09-a-drain-end-hook.patch`](../../../reussir-bugs/patches/09-a-drain-end-hook.patch),
  described in [issue 9](../../../reussir-bugs/09-drain-end-hook.md).
- **Why:** Not a bug: Reussir has no hook at the end of a free, and the
  `sync` dependents of promises dropped inside a free must run when it is
  over (round 7 RV7C-01). A missing feature: issue 9.
- **Where:** [../tasks/dependents.md](../tasks/dependents.md#dependents-of-a-promise-dropped-inside-a-free-run-when-the-free-is-over).
- **Remove only if:** n/a (the patch is applied to `l2r-local` since
  2026-10-03; the fallback for builds without it went in switch step 6,
  when lean-runtime's deferred resolutions came to need every drain's end).
