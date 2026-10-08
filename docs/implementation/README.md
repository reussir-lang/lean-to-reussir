# lean2rr implementation notes

A catalog of the implementation's tricks and special cases: the things
lean2rr does for particular situations, why, where in the code, and what
would break without them. The design itself is in
[`../translation-plan.md`](../translation-plan.md), which these notes do not
repeat: each entry gives the gist and links to the plan's section.

**How to use and maintain these files.** To find out why lean2rr does
something, search these files for the function name, the generated name
(`l2r_sink`, `L2RStep_k`), the review finding (RV6J-03, IO6-14, PF4-10) or
the Reussir issue number, or start from the area list below. Every change
that adds, removes or changes a trick updates its entry here **in the same
commit**: add an entry for a new special case, delete the entry of one that
is removed, and keep "Where" pointing at functions that exist. Entries
marked *in progress* or *parked* describe work on other branches; update
them when that work is merged.

Each entry has a one-line title and four parts:

- **What:** the trick or special case;
- **Why:** the problem it solves, with the review finding, test or commit
  that showed it where known;
- **Where:** the files and functions, and the plan section;
- **Remove only if:** what would break without it, or which Reussir patch
  or feature would make it unnecessary.

Paths in "Where" are relative to `lean2rr/LeanToReussir/` unless a file
says otherwise; runtime paths start with `runtime/`. Finding ids name
adversarial review rounds (adv2-adv5, round 6 `RV6…`/`IO6…`/`TY6…`,
round 7 `RV7…`, round 8 `RV8…`, round 9 `RV9…` with the reviews of its
fixes `C01R…`-`C03R…`), the cross-tests on external fixtures (`XT-…`, their reviews
`XT6-…`) and the reviews of merged branches (`RVPB-…`, `RVA-…`,
`L434-…`); short hashes are commits on `dev` or on the branches merged
into it. Reussir issues (bugs, costs and the other kinds) link to
[`../../reussir-bugs/`](../../reussir-bugs/README.md).

## Areas

1. [types/](types/README.md): monomorphization and types: instances,
   static dictionaries, polymorphic recursion, Lean's passes, type
   recovery, `lcAny` and the "can cast" fact.
2. [representations/](representations/README.md): `Nat`/`Int`, generated
   records and value types, arrays (compact arrays of scalars), strings and the literal
   table, `Box`, placeholders, function values, references, identity.
3. [conversions/](conversions/README.md): where conversions go (a value
   of an inductive is never rebuilt: one type per inductive), lazy
   conversions of function values, thunks and tasks, unboxing, casts.
4. [control-flow/](control-flow/README.md): calls and `let`s, `cases`
   shapes, join points (J1/J1′/J2/J3), state machines (J4), `Outline`.
5. [ownership.md](ownership.md): borrow emulation, store-then-release
   reference sets, the drop stack, `ReleaseElems`, owned reads, the
   release of an element a set replaces.
6. [startup/](startup/README.md): module phases and initializer order
   (the library's initializers included), constants and once-cells,
   closed-term chains, persist walks, the entry point.
7. [tasks/](tasks/README.md): thunk and task cells, deferral, `sync`
   dependents, the scheduler, polling, the stack guard, the event loop.
8. [reussir-workarounds/](reussir-workarounds/README.md): each Reussir
   issue (bug or cost) with lean2rr's workaround and whether it can go;
   Reussir's limitations, its missed optimizations and missing features.
9. [optional-passes.md](optional-passes.md): one line per optional pass
   with its soundness guard (all on by default but `unread-fields`, which
   leaves out values in fields no kept code reads: the owner's exception), and
   the required parts.
10. [externs-ffi/](externs-ffi/README.md): extern dispatch and its order,
    glue, the `L2RShim` library, special cases of single runtime externs,
    the shared crate lean-runtime, externs of the program (Lean code plus
    Lean's runtime library: the binding of their C symbol, their Lean
    definitions, refusals), the C FFI (parked).
11. [translator.md](translator.md): lean2rr itself: loading the program,
    its stack and limits, its switches.
12. [testing.md](testing.md): the test tooling that checks costs and the
    translation itself: the allocation counter, its limits and
    `alloc-check.sh`, the `.xfail` of the allocation check alone, canonical
    fingerprints of the generated code, the determinism check, pay-nothing
    baselines; the dependent-type corpus (sharing checked by memory, timing
    tests that follow Lean's arities, the combined shared cases).
