# lean2rr implementation notes

A catalog of the implementation's tricks and special cases: the things
lean2rr does for particular situations, why, where in the code, and what
would break without them. The design itself is in
[`../translation-plan.md`](../translation-plan.md), which these notes do not
repeat: each entry gives the gist and links to the plan's section.

**How to use and maintain these files.** To find out why lean2rr does
something, search these files for the function name, the generated name
(`l2r_sink`, `L2RStep_k`), the review finding (RV6J-03, IO6-14, PF4-10) or
the Reussir bug number, or start from the area list below. Every change
that adds, removes or changes a trick updates its entry here **in the same
commit**: add an entry for a new special case, delete the entry of one that
is removed, and keep "Where" pointing at functions that exist. Entries
marked *in progress* or *being removed* describe work on other branches;
update them when that work is merged.

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
round 7 `RV7…`); short hashes are commits on `dev`. Reussir bugs link to
[`../../reussir-bugs/`](../../reussir-bugs/README.md).

## Areas

1. [types/](types/README.md): monomorphization and types: instances,
   static dictionaries, polymorphic recursion, Lean's passes, type
   recovery, `lcAny` and the "can cast" fact.
2. [representations/](representations/README.md): `Nat`/`Int`, generated
   records and value types, arrays and `ElemBox`, strings and the literal
   table, `Box`, placeholders, function values, references, identity.
3. [conversions/](conversions/README.md): structural conversions and
   `convMachine`, lazy conversions of function values, thunks and tasks,
   unboxing, casts.
4. [control-flow/](control-flow/README.md): calls and `let`s, `cases`
   shapes, join points (J1/J1′/J2/J3), state machines (J4), `Outline`.
5. [ownership.md](ownership.md): borrow emulation, store-then-release
   reference sets, the drop stack, `ReleaseElems`, owned reads, the origin
   table.
6. [startup/](startup/README.md): module phases and initializer order,
   constants and once-cells, closed-term chains, persist walks, the entry
   point.
7. [tasks/](tasks/README.md): thunk and task cells, deferral, `sync`
   dependents, the scheduler, polling, the stack guard, the event loop.
8. [reussir-workarounds/](reussir-workarounds/README.md): each Reussir bug
   with lean2rr's workaround and whether it can go; Reussir's limitations.
9. [optional-passes.md](optional-passes.md): one line per optional pass
   with its soundness guard, and the required parts.
10. [externs-ffi/](externs-ffi/README.md): extern dispatch and its order,
    glue, the `L2RShim` library, the C FFI (in progress).
11. [translator.md](translator.md): lean2rr itself: loading the program,
    its stack and limits, its switches.
