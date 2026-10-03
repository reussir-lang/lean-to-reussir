# `cases`

Paths are relative to `lean2rr/LeanToReussir/`. Plan
[§5.5](../../translation-plan.md#55-cases).

### How a `cases` is lowered

- **What:** On `Bool`, an `if`; on a structure, projections at the record
  positions of its layout (alignment-sorted under `field-order`); on an
  enum, a `match` whose
  missing constructors (no default) get `_ => l2r_unreachable`. A `cases`
  on a `Box` converts the value to the inductive's uniform instance first;
  one on a cast value goes through `castCases`
  ([../conversions/casts.md](../conversions/casts.md#a-cases-on-a-cast-value-matches-through-the-values-own-constructors)).
  Erased fields get no binders.
- **Why:** Lean has proved the missing alternatives impossible.
- **Where:** `Lower/Code.lean`: `lowerCases`, `lowerAlt`.
- **Remove only if:** never.

### An arm that returns the matched value returns that value

- **What:** When `simp` turns `node l k r` rebuilt in an arm back into
  the matched `t`, the arm returns `t` itself, with its sharing, not a
  copy.
- **Why:** A rebuilt copy (863d8ca, a workaround for Reussir's token reuse)
  broke code that stops when `ptrEq` says a step changed nothing (Lean's
  `Expr.replace`, fixpoints never stopped), turned a DAG kept by a
  traversal into a tree (Rp3Dag 25: 1.58 GB), and made a lookup returning
  an existing node allocate one per call (adv3 RP3-1/RP3-2, d1a507d).
- **Where:** `Lower/Code.lean`: `lowerCode` (the `.return` case).
- **Remove only if:** never. The cost (Reussir cannot reuse the matched
  cell in the other arms while it stays live) is addressed by
  `fresh-rebuild` and `lazy-fields` below.

### Fresh values returned whole are rebuilt (`fresh-rebuild`)

- **What:** In a program that never observes identity or sharing, an arm
  that binds every field and only returns the matched value returns the
  constructor rebuilt from its fields, when the matched value is freshly
  built: bound in the same function to a constructor application, or to a
  full call of a declaration all of whose results are freshly built (a
  whole-program analysis).
- **Why:** The error arm of every `ExceptT`/`Option`/`EStateM` bind
  (`| .error _ => r`) kept the matched value live, so each bind's success
  path allocated and freed a cell. Rebuilt, every arm consumes the cell
  and Reussir reuses it (MonadicInterp 1.25x → 1.08x native, cb884c1).
  Parameters, fields, constants and results of lookups, externs or
  function values are still returned themselves (they may be shared).
- **Where:** `Opt/FreshRebuild.lean`: `enumFields`, `freshDecls`,
  `bodyFresh`, `onlyReturned`; `Lower/Ctx.lean`: `CodeCtx.rebuild`,
  `CodeCtx.letCalls`; guard: `LowerCtx.observesIdentity`
  ([../representations/identity.md](../representations/identity.md#whether-the-program-observes-identity-is-a-whole-program-fact)).
- **Remove only if:** the pass is off (correct, slower). Branch
  `mem-identity` (in progress) drops the identity guard.

### Fields of a live matched value are bound where they are used (`lazy-fields`)

- **What:** In an arm where the matched value stays live (stored whole in
  a new constructor, returned whole, or passed whole to a call), the match
  binds only the fields used while the value is live; an inner alternative
  that no longer uses the value matches it again (a structure: projects
  it) and binds the fields it uses there.
- **Why:** Reussir projects every bound field at the match with an
  increment; the field's later release looks like a reusable cell to token
  reuse, which prefers it to the cell actually freed
  ([Reussir bug 7](../../../reussir-bugs/07-phantom-reuse-donor.md)):
  `TreeMap.insert` allocated and freed a node per level (13.2 allocations
  per insertion → 2.2, bc951a4); BST inserts with `Nat`/`String` keys
  (9f35c6c); `List.mergeSort`'s merge allocated a cell per step, and the
  result's memory order then depended on allocator state (5-9x native at
  some lengths; round 6 S6-02, 26515ee).
- **Where:** `Opt/LazyFields.lean`: `lazyStructFields`, `lazyEnumFields`,
  `lazyLowerAlt`, `usesWhileLive`, `liveScan`, `usedAsArg`,
  `returnedWhole`, `LazyFieldsState`.
- **Remove only if:** the pass is off (correct, slower), or Reussir's token
  reuse stops preferring decrements that never free in the
  call-before-branch case (patch 0007 alone does not cover it).

### The matched value of a nullary arm is rebuilt (`nullary-scrutinee`)

- **What:** In the arm of a constructor without fields, a use of the
  matched value uses a new nullary value instead (free in Reussir).
- **Why:** `leaf` reused as the children of a new node no longer keeps the
  scrutinee alive, so its cell can be reused (1146ff0).
- **Where:** `Opt/NullaryScrutinee.lean`: `nullaryPrelude` (pins the
  variable: `CodeCtx.pinned`).
- **Remove only if:** the pass is off.

### Structure projections move into the branches that use them (`sink-proj`)

- **What:** A projection `let x = s.j` at the top of an alternative moves
  into the branches of the following `if`/`match` that use `x`, when
  another branch keeps `s` whole.
- **Why:** The same phantom-donor problem as bug 7: an association-list
  update that keeps the pair whole in one branch allocated a new cons per
  element and freed the matched one after its recursive call, which was
  then no longer a tail call (adv4 PF4-10, 3e3a6aa).
- **Where:** `Opt/SinkProj.lean`: `sinkHere`, `Block.sinkProj`.
- **Remove only if:** the pass is off.

### Wildcard arms release wide values out of line

- **What:** A wildcard arm covering two or more constructors releases the
  values of wide enums (8 or more constructors) it holds and does not use
  through one out-of-line call, `l2r_sink`.
- **Why/Where:** see
  [../reussir-workarounds/build-time.md](../reussir-workarounds/build-time.md#bug-22-a-wildcard-arm-over-a-wide-enum-costs-n3-code).
- **Remove only if:** see the linked entry.

### A scrutinee that ends with a brace is parenthesized

- **What:** The printer puts a `match` scrutinee or an `if` condition in
  parentheses when it ends with a brace (a constructor, a block, a
  `match`, an `if`, a lambda); it also writes nested `if`s in an `else`
  block (Reussir has no `else if`) and no trailing comma after a match's
  last arm.
- **Why:** `match T::c{x} {` did not parse, as in Rust (an extern applied
  to `unsafeCast ()`; a2b49cd).
- **Where:** `RR.lean`: `Expr.renderHead`, the printer.
- **Remove only if:** Reussir's grammar changes.
