# Reussir bugs that affect what a program computes

One entry per bug: what lean2rr does, whether a local patch fixes it, and
whether the workaround can be dropped. Bug files are in
[`reussir-bugs/`](../../../reussir-bugs/README.md). Paths:
`lean2rr/LeanToReussir/` for lean2rr's files.

### Bug 1: `[value]` enum payloads are lost when moved

- **What:** lean2rr emits only `[value]` enums that are unaffected:
  field-less enumerations, and the prelude's `Nat`/`Int`, whose arms each
  hold one 64-bit word. Everything else with several arms is a shared enum
  (J4 entry enums included); multi-field value records are `[value]`
  structs.
- **Why:** Reussir moves a `[value]` enum as one representative arm's
  struct, so another arm's bytes on its padding or on an `i1` are lost
  ([01-value-enum-payload.md](../../../reussir-bugs/01-value-enum-payload.md)).
- **Where:** `LowerBase.lean`: `nominalType`, `tupleType`;
  `Lower/StateMachine.lean`: `emitStateMachine`.
- **Remove only if:** the bug is fixed (no patch yet). Then J4 entry
  enums and multi-arm value types could be `[value]`.

### Bug 2: in-place reuse skips a field store

- **What:** The driver passes `--no-pack-record-members`, and lean2rr
  orders each constructor's fields by decreasing alignment itself, so
  records have no padding between members and equal member types at
  indices 0..i put member i at the same offset.
- **Why:** Reussir's copy avoidance skips storing a field it believes is
  in place; with packed layouts the variant check is wrong (a wrong value,
  no error). Patch 0002 fixes the structure half only
  ([02-reuse-field-store.md](../../../reussir-bugs/02-reuse-field-store.md);
  444a70a, 7860807).
- **Where:** `scripts/l2r.py` (`--no-pack-record-members`);
  `Opt/FieldOrder.lean`; `LowerBase.lean`: `nominalType`, `fieldAlign`.
- **Remove only if:** the variant half is fixed too. `field-order` itself
  is optional; the flag is not.

### Bug 4: rrc recurses forever on two equal recursive types

- **What:** When rrc dies from a signal, `scripts/l2r.py` retries without
  `--reuse-across-call` (and says so on stderr).
- **Why:** Reussir's structural type comparison crashed on a user list and
  `List` (456bc97). Patch 0004 (applied) fixes it
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
  `--reuse-across-call` (caea747; RtStreamsRedirectOob). Patch 0005
  (applied) fixes the crash; user code could still hit it without the
  patch
  ([05-one-armed-if.md](../../../reussir-bugs/05-one-armed-if.md)).
- **Where:** `runtime/prelude.rr`: `l2r_panic_code`, `l2r_diag_put`;
  `runtime/leanrt/src/io.rs`: `diag_put`; `Emit/Entry.lean`: `lowerEntry`.
- **Remove only if:** not needed with 0005 (applied), but kept: by the
  policy lean2rr also works with an unpatched Reussir, and the trampoline
  is cheap.

### Bug 6: a static cell is freed after about 2^32 references

- **What:** No lean2rr-side workaround: the retains come from Reussir's
  own lowering of nullary constructors. lean2rr relies on patch 0006
  (applied); the documented flag alternative
  (`--nullary-variant-encoding arch-independent` or `boxed`, through
  `L2R_RRC_FLAGS`) is not used. The runtime's array code relies on an
  immediate never being freed: it skips immediates when freeing or
  copying arrays of records (aarch64).
- **Why:** 0006 keeps the default encoding's speed (to be remeasured on an
  idle machine;
  [06-static-count-wrap.md](../../../reussir-bugs/06-static-count-wrap.md)).
- **Where:** `scripts/l2r.py` (`L2R_RRC_FLAGS`, 42dacc7);
  `runtime/leanrt/src/drop.rs`: `ReleaseElems`;
  `runtime/leanrt/src/array.rs`: `ExtendCloned`.
- **Remove only if:** n/a. If the flag replaces 0006, revisit the
  immediate skips ([../ownership.md](../ownership.md#array-copies-skip-the-increments-of-immediates)).

### Bug 7: token reuse picks decrements that never free

- **What:** The optional passes `lazy-fields` and `sink-proj` bind fields
  where they are used, so a value that stays live has no retained fields
  whose releases look like donors; `nullary-scrutinee` rebuilds a matched
  constructor without fields in its arm, so the scrutinee is not kept
  alive by a use there.
- **Why:** A missed optimization, not a bug; patch 0007 (applied) covers
  some shapes (`UInt64` keys) but not a call before the branch (`Nat` and
  `String` comparisons), which the passes do
  ([07-phantom-reuse-donor.md](../../../reussir-bugs/07-phantom-reuse-donor.md)).
  0007 stays because 0009 uses its helper.
- **Where:** [../control-flow/cases.md](../control-flow/cases.md).
- **Remove only if:** Reussir's token reuse handles the call-before-branch
  shape; then measure with the passes off.

### Bug 8: a padding lift breaks declaration-order layouts

- **What:** Nothing to do: lean2rr never emits the shape (records have no
  padding between members; one-field `[value]` structs).
- **Why:** [08-padding-lift.md](../../../reussir-bugs/08-padding-lift.md).
  With `field-order` off, Reussir pads with bytes, which does not trigger
  it either (5830b1c).
- **Where:** `LowerBase.lean`: `nominalType`.
- **Remove only if:** n/a.

### Bugs 9 and 14: a bound member loses a reference

- **What:** No workaround possible: the shapes come from Reussir's own
  inliner. Patch 0009 (applied) fixes both.
- **Why:** [09-duplicate-bound-member.md](../../../reussir-bugs/09-duplicate-bound-member.md),
  [14-member-consumed-before-release.md](../../../reussir-bugs/14-member-consumed-before-release.md).
- **Where:** n/a.
- **Remove only if:** n/a.

### Bug 12: the parser swaps subtrees whose hashes collide

- **What:** No workaround possible (any shape, name or literal can
  collide in a large file). Patch 0012 (applied).
- **Why:** [12-node-cache-collision.md](../../../reussir-bugs/12-node-cache-collision.md).
- **Where:** n/a.
- **Remove only if:** n/a.

### Bug 13: drop glue recursed once per cell

- **What:** The runtime frees its containers through the per-thread
  pending stack that patch 0014 adds (`reussir_rt::drop`), and needs it to
  build; 0013 and 0015 complete it.
- **Why:** A missing feature, not a bug: Lean frees iteratively
  ([13-long-list-drop.md](../../../reussir-bugs/13-long-list-drop.md)).
- **Where:** [../ownership.md](../ownership.md#containers-free-through-the-threads-pending-stack-in-leans-order).
- **Remove only if:** never (required).

### Bug 15: a `match` on a `Nullable` yielding a counted value

- **What:** Nothing to do: lean2rr does not use `Nullable`.
- **Why:** [15-nullable-match-yield.md](../../../reussir-bugs/15-nullable-match-yield.md).
- **Where:** n/a.
- **Remove only if:** n/a.

### Bug 19: a `Cell` of a `[value]` record with counted members

- **What:** `Nat`/`Int` references are the prelude's `L2RNatRef`/
  `L2RIntRef` (a tagged word and a big-number cell); other `[value]`
  records are stored in an `ElemBox`.
- **Why:** rrc rejects `cell::get`/`set` on such a cell
  ([19-cell-of-value-record.md](../../../reussir-bugs/19-cell-of-value-record.md)).
- **Where:** [../representations/references.md](../representations/references.md#nat-and-int-references-keep-a-tagged-word-and-a-big-number-cell).
- **Remove only if:** the bug is fixed (no patch yet).

### Bug 21: an unterminated `[:` in a texture is dropped

- **What:** `[` is written as `\x5b` in the string literal table.
- **Why:** [21-unterminated-placeholder.md](../../../reussir-bugs/21-unterminated-placeholder.md);
  round 6 RV6L-01.
- **Where:** [../representations/strings.md](../representations/strings.md#-is-escaped-in-the-string-literal-table).
- **Remove only if:** not needed once patch 0016 is applied (it is not),
  but kept: by the policy lean2rr also works with an unpatched Reussir,
  and the escape is free.

### The drain-end hook (local patch 0040)

- **What:** The runtime stores a callback in Reussir's
  `__reussir_drop_drained`, linked weakly, which local patch 0040 makes
  every outermost drain that released something call when it ends; without
  the patch the runtime still builds and falls back to walking later. The
  patch is `reussir-patches/0040-l2r-local-drop-call-the-host-s-function-when-a-drain.patch`
  at b299aab (see [README.md](README.md#summary)).
- **Why:** Not a bug: Reussir has no hook at the end of a free, and the
  `sync` dependents of promises dropped inside a free must run when it is
  over (round 7 RV7C-01). No bug entry exists for it.
- **Where:** [../tasks/dependents.md](../tasks/dependents.md#dependents-of-a-promise-dropped-inside-a-free-run-when-the-free-is-over).
- **Remove only if:** n/a (the fallback is for Reussir builds without
  0040; 0040 is not applied to `l2r-local` yet).
