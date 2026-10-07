# Reussir bugs that affect what a program computes

One entry per bug: what lean2rr does, whether a local patch fixes it, and
whether the workaround can be dropped. Every issue here is a bug
(erroneous behaviour); the last entry, the drain-end hook, is a local
addition, not an issue. Issues 7 (a missed optimization) and 13 (a missing
feature), which are not bugs, are in [limitations.md](limitations.md). The
issue files are in [`reussir-bugs/`](../../../reussir-bugs/README.md).
Paths: `lean2rr/LeanToReussir/` for lean2rr's files.

### Bug 1: `[value]` enum payloads are lost when moved

- **What:** lean2rr emits only `[value]` enums that are unaffected:
  field-less enumerations (`Nat`/`Int` are tagged handles since patch
  41-a, not `[value]` enums). Everything else with several arms is a shared enum
  (J4 entry enums included); multi-field value records are `[value]`
  structs.
- **Why:** Reussir moves a `[value]` enum as one representative arm's
  struct, so another arm's bytes on its padding or on an `i1` are lost
  ([01-value-enum-payload.md](../../../reussir-bugs/01-value-enum-payload.md)).
- **Where:** `LowerBase.lean`: `nominalType`, `tupleType`;
  `Lower/StateMachine.lean`: `emitStateMachine`.
- **Remove only if:** not needed with patch 01-a (applied), but kept: by
  the policy lean2rr also works with an unpatched Reussir. Without the
  workaround, J4 entry enums and multi-arm value types could be `[value]`.

### Bug 2: in-place reuse skips a field store

- **What:** The driver passes `--no-pack-record-members`, and lean2rr
  orders each constructor's fields by decreasing alignment itself, so
  records have no padding between members and equal member types at
  indices 0..i put member i at the same offset.
- **Why:** Reussir's copy avoidance skips storing a field it believes is
  in place; with packed layouts the variant check is wrong (a wrong value,
  no error). Patch 02-a fixes the structure half and 02-b the variant
  half (both applied)
  ([02-reuse-field-store.md](../../../reussir-bugs/02-reuse-field-store.md);
  444a70a, 7860807).
- **Where:** `scripts/l2r.py` (`--no-pack-record-members`);
  `Opt/FieldOrder.lean`; `LowerBase.lean`: `nominalType`, `fieldAlign`.
- **Remove only if:** not needed with 02-b (applied), but kept: by the
  policy lean2rr also works with an unpatched Reussir. `field-order` itself
  is optional; the flag is not.

### Bug 4: rrc recurses forever on two equal recursive types

- **What:** When rrc dies from a signal, `scripts/l2r.py` retries without
  `--reuse-across-call` (and says so on stderr).
- **Why:** Reussir's structural type comparison crashed on a user list and
  `List` (456bc97). Patch 04-a (applied) fixes it
  ([04-recursive-type-compare.md](../../../reussir-bugs/04-recursive-type-compare.md)).
- **Where:** `scripts/l2r.py`: `main`.
- **Remove only if:** it stays as a fallback for unknown crashes; it costs
  nothing when rrc does not crash.

### Bug 5: TokenReuse crashed on a one-armed `if`

- **What:** The runtime's own diagnostics (index out of bounds,
  `String.get!`, `dbgTraceIfShared`) reach `l2r_stderr_put` from Rust,
  through the program's `extern "C"` trampoline `l2r_stderr_put_c`
  (descriptor 2 without one), instead of a Reussir-level call.
- **Why:** A Reussir-level call from the prelude's array helpers into the
  stream code made rrc crash in `TokenReusePass` under
  `--reuse-across-call` (caea747; RtStreamsRedirectOob). Patch 05-a
  (applied) fixes the crash; user code could still hit it without the
  patch
  ([05-one-armed-if.md](../../../reussir-bugs/05-one-armed-if.md)).
- **Where:** `runtime/prelude.rr`: `l2r_panic_code`, `l2r_diag_put`;
  `runtime/leanrt/src/io.rs`: `diag_put`; `Emit/Entry.lean`: `lowerEntry`.
- **Remove only if:** not needed with 05-a (applied), but kept: by the
  policy lean2rr also works with an unpatched Reussir, and the trampoline
  is cheap.

### Bug 6: a static cell is freed after about 2^32 references

- **What:** No lean2rr-side workaround: the retains come from Reussir's
  own lowering of nullary constructors. lean2rr relies on patch 06-a
  (applied); the documented flag alternative
  (`--nullary-variant-encoding arch-independent` or `boxed`, through
  `L2R_RRC_FLAGS`) is not used. The runtime's array code relies on an
  immediate never being freed: it skips immediates when freeing or
  copying arrays of records (aarch64).
- **Why:** 06-a keeps the default encoding's speed (to be remeasured on an
  idle machine;
  [06-static-count-wrap.md](../../../reussir-bugs/06-static-count-wrap.md)).
- **Where:** `scripts/l2r.py` (`L2R_RRC_FLAGS`, 42dacc7);
  `runtime/leanrt/src/drop.rs`: `ReleaseElems`;
  `runtime/leanrt/src/array.rs`: `ExtendCloned`.
- **Remove only if:** n/a. If the flag replaces 06-a, revisit the
  immediate skips ([../ownership.md](../ownership.md#array-copies-skip-the-increments-of-immediates)).

### Bug 8: a padding lift breaks declaration-order layouts

- **What:** Nothing to do: lean2rr never emits the shape (records have no
  padding between members; one-field `[value]` structs).
- **Why:** [08-padding-lift.md](../../../reussir-bugs/08-padding-lift.md)
  (patch 08-a, applied).
  With `field-order` off, Reussir pads with bytes, which does not trigger
  it either (5830b1c).
- **Where:** `LowerBase.lean`: `nominalType`.
- **Remove only if:** n/a.

### Bugs 9 and 14: a bound member loses a reference

- **What:** No workaround possible: the shapes come from Reussir's own
  inliner. Patch 09-a (applied) fixes both.
- **Why:** [09-duplicate-bound-member.md](../../../reussir-bugs/09-duplicate-bound-member.md),
  [14-member-consumed-before-release.md](../../../reussir-bugs/14-member-consumed-before-release.md).
- **Where:** n/a.
- **Remove only if:** n/a.

### Bug 12: the parser swaps subtrees whose hashes collide

- **What:** No workaround possible (any shape, name or literal can
  collide in a large file). Patch 12-a (applied).
- **Why:** [12-node-cache-collision.md](../../../reussir-bugs/12-node-cache-collision.md).
- **Where:** n/a.
- **Remove only if:** n/a.

### Bug 15: a `match` on a `Nullable` yielding a counted value

- **What:** Nothing to do: lean2rr does not use `Nullable`.
- **Why:** [15-nullable-match-yield.md](../../../reussir-bugs/15-nullable-match-yield.md)
  (patch 15-a, applied).
- **Where:** n/a.
- **Remove only if:** n/a.

### Bug 19: a `Cell` of a `[value]` record with counted members

- **What:** A Reussir cell holds no `[value]` record: a reference's cell
  holds a `Box` (one reference type), a once-cell a value of a boundary
  type or an `ElemBox` (`Nat`/`Int`, `[value]` enums before patch 41-a,
  are counted handles now, which cells hold directly).
- **Why:** rrc rejects `cell::get`/`set` on such a cell
  ([19-cell-of-value-record.md](../../../reussir-bugs/19-cell-of-value-record.md);
  patch 19-a, applied).
- **Where:** [../representations/references.md](../representations/references.md#a-reference-is-one-record-type-around-a-reussir-cell-of-a-box);
  `LowerBase.lean`: `cellStorage`.
- **Remove only if:** not needed with 19-a (applied), but kept: by the
  policy lean2rr also works with an unpatched Reussir.

### Bug 21: an unterminated `[:` in a texture is dropped

- **What:** `[` is written as `\x5b` in the string literal table.
- **Why:** [21-unterminated-placeholder.md](../../../reussir-bugs/21-unterminated-placeholder.md);
  round 6 RV6L-01.
- **Where:** [../representations/strings.md](../representations/strings.md#-is-escaped-in-the-string-literal-table).
- **Remove only if:** not needed with patch 21-a (applied since
  2026-10-03), but kept: by the policy lean2rr also works with an unpatched Reussir,
  and the escape is free.

### The drain-end hook (local patch 40-a)

- **What:** The runtime stores a callback in Reussir's
  `__reussir_drop_drained`, which local patch 40-a makes every outermost
  drain that released something call when it ends. lean2rr requires the
  patch since switch step 6: `scripts/l2r.py` stops with an error when the
  Reussir checkout lacks it (`check_reussir_patches`), and leanrt names the
  symbol (`task::hook_drained`), so it would not link either. The
  patch is [`reussir-bugs/patches/40-a-drain-end-hook.patch`](../../../reussir-bugs/patches/40-a-drain-end-hook.patch),
  described in [issue 40](../../../reussir-bugs/40-drain-end-hook.md).
- **Why:** Not a bug: Reussir has no hook at the end of a free, and the
  `sync` dependents of promises dropped inside a free must run when it is
  over (round 7 RV7C-01). A missing feature: issue 40.
- **Where:** [../tasks/dependents.md](../tasks/dependents.md#dependents-of-a-promise-dropped-inside-a-free-run-when-the-free-is-over).
- **Remove only if:** n/a (40-a is applied to `l2r-local` since
  2026-10-03; the fallback for builds without it went in switch step 6,
  when lean-runtime's deferred resolutions came to need every drain's end).
