# Outline: cutting deep and long functions

`Outline` runs after lowering, over the generated functions. It does not
make programs faster; it keeps rrc's build time and memory, and the `.rr`
text, from growing superlinearly. It is a required part (`outline` in
`Opt/Registry.lean`). Paths are relative to `lean2rr/LeanToReussir/`. Plan
[§10](../../translation-plan.md#10-known-divergences-and-unsupported-features),
"Build time".

### Deep and long tail paths become functions called in tail position

- **What:** A function is cut when a tail path (through the arms of a
  `match`/`if` that is the result, and through the rest of a block after a
  `let`) is 32 levels deep or 256 `let`s long, or a `let`'s value is.
  Then, once a path is 8 levels deep or 64 `let`s long, its rest becomes a
  new function of the variables it uses, called in tail position; a rest
  shorter than 16 `let`s without nested `match`/`if` stays. Ordinary
  functions are below the triggers and come out unchanged.
- **Why:** Every IO bind nests one `match`, so a `main` of N statements is
  N levels deep, and reuse across calls cost about depth^2.6 (a Reussir
  cost, fixed upstream in #672);
  rrc's memory was quadratic in a straight-line `Nat` function (a
  Reussir cost, fixed upstream in #670); the
  `.rr` indentation follows the nesting (a 3000-arm literal match: 126 MB
  of `.rr`, lean2rr out of memory at 16 GB; 072c620, 3597a31). A
  2000-line `main` now builds in about two minutes and 2 GB.
- **Where:** `Outline.lean`: `Limits` (`triggerDepth`, `triggerLets`,
  `maxDepth`, `maxLets`, `minRest`), `outlineFns`, `walkBlock`,
  `walkTail`, `outlineTail`, `extent`, `heavy`; `Emit/Program.lean`:
  `LoweredProgram.outline`; `lean2rr/Main.lean`: `pipeline` (`L2R_NO_OUTLINE`
  skips it, for the repros of those costs).
- **Remove only if:** the two costs are gone upstream (Reussir #672 and
  #670: removable after the move to Reussir 7954a367 as a workaround) and
  the `.rr` text no longer grows with nesting.

### Deep `let` values come from a function

- **What:** In a function that is cut, a `let` whose value is 8 levels
  deep or 64 `let`s long gets its value from a new function of the
  variables the value uses (cut in turn).
- **Why:** A 3000-arm match as a `let`'s value reached rrc whole (adv5
  RF-3, aa2dce4).
- **Where:** `Outline.lean`: `walkValue`.
- **Remove only if:** as above.

### Recursive functions keep their loops: step values

- **What:** A function that can reach itself is cut too, but a rest that
  holds a tail call of a function of its cycle becomes a part that
  *returns* what to do: a value of a generated enum `L2RStep_k`, `done(v)`
  or one variant per function of the cycle with its arguments. The cut
  point matches it and makes the tail call itself.
- **Why:** A cycle of tail calls through the parts would not always be a
  sibling call and would use stack per iteration; this way a self tail
  call stays in the function and remains a loop (aa2dce4; test
  `RtOutlineLoops` runs such loops with a 1 MiB stack). Before, recursive
  functions were skipped: a recursive IO function of 1500 statements made
  over 100 MB of `.rr` and did not build under 16 GB. Cost: a step value
  per iteration, only in functions this long; no heap cell (next entry).
- **Where:** `Outline.lean`: `StepInfo`, `stepInfo`, `stepVariant`,
  `stepify`, `stepDispatch`, `cycleCall?`, `hasCycleCall`,
  `tailCycleCalls`, `cycles`.
- **Remove only if:** as above.

### Step enums are `[value]`

- **What:** The step enum `L2RStep_k` is an `enum [value]`, whatever the
  types of its fields: `done` first, then the call variants in order. The
  fields of a call variant are in decreasing alignment, ties in parameter
  order, so the variant has no padding between them (a type that the type
  table does not know keeps parameter order): the construction and the cut
  point's binders follow that order, the call keeps parameter order. A
  step value goes only from a part's result to the match at the cut point:
  never into a field, an array, a `Cell` or a `Box`, and no conversion is
  generated for its type (Outline runs after lowering), so being `[value]`
  changes nothing else. No step enum contains itself: `done` holds the
  function's result type and a call variant the callee's parameter types,
  all types of the program before outlining. Examples
  (RtOutlineValueSteps): `done(u64)`, `c0(Nat, u64, u64, u64)`;
  `done(LStr)`, `c0(LStr, RVec<LAny>, Nat, u64, bool, u8)` (parameters
  `Bool, UInt8, String, Array Nat, Nat, UInt64`); `done(f64)`,
  `c0(f64, f64)`; `done(Tuple)` (a `[value]` struct `(f64, bool)`),
  `c0(Nat, f64, u8, bool)`.
- **Why:** A shared step enum is a heap cell per iteration. The
  allocation survey of 2026-10-10 found lean-zip's `lz77LazyMergedLoop`
  step (23 fields, 192 bytes): 43,049 cells, 8.27 MB of the 10.39 MB that
  Z01c's allocations grow by between its two sizes (1.10 times native's
  allocations, 2.04 times its bytes). With `[value]` steps, all seven
  step enums of lean-zip are `[value]`; Z01c's growth is 7,401
  allocations and 2.11 MB (0.16 and 0.41 times native's), Z01r's 0.13 and
  0.59 times native's (before 0.19 and 0.81); Z01d and Z01t do not change
  (survey sizes and counter, outputs identical). From 2026-10-10 to
  2026-10-19 a layout guard kept a step enum shared unless its
  representative arm surely carried every other arm's bytes (`floaty`'s
  `f64`s and `fmix`'s `f64` and `bool` did not): Reussir lost bytes of
  `[value]` enums whose arms differ (old bug 1,
  [../reussir-workarounds/correctness-bugs.md](../reussir-workarounds/correctness-bugs.md#old-bug-1-value-enum-payloads-were-lost-when-moved)),
  fixed in lean2rr's base. Before and after the guard went (2026-10-19;
  allocation counter, and cachegrind instructions of the whole run with
  SVE off): `fmix` at 200000 iterations 165,893 allocations (5.31 MB) to
  43 (6.6 KB), 26.3 to 16.3 million instructions; `floaty` 87,391 to
  43,187 allocations, 14.7 to 11.7 million; a review repro whose step carries a `Float`, a `Bool`, a
  `UInt8`, a `UInt64`, two arrays and a `Nat`
  (`c0(Nat, u64, RVec<u64>, RVec<u8>, Nat, f64, u8, bool)`, 200000
  iterations) 224,221 allocations (14.4 MB) to 60 (8.4 KB), 86.7 to 81.4
  million. Test `RtOutlineValueSteps`: `.alloc`, no
  allocation per iteration, as natively (`fmix` included); `.pipe`,
  3000000 steps of `mixed` and of the mutual recursion `ping` on a 1 MiB
  stack; also `done` arms narrower than a word (`Bool`, `Bool × UInt8`)
  and a `done` tuple larger than the call variant.
- **Where:** `Outline.lean`: `typeTable`, `stepFieldOrder`, `StepCall`,
  `stepItem`, `stepVariant`, `stepInfo`, `stepify`, `stepDispatch`,
  `outlineFns`; `FieldAlign.lean`: `fieldAlign?` (shared with
  `fieldAlign`, the record field order); `Emit/Program.lean`:
  `LoweredProgram.outline`.
- **Remove only if:** never (speed).

### Only blocks whose variables have known types are outlined

- **What:** A block is outlined only if every variable it uses has a
  known Reussir type (parameters, typed `let`s, fields of matched variants
  from the type declarations and from the prelude's enums such as
  `L2RUnit`);
  otherwise it stays where it is.
- **Why:** An outlined part's parameters need types; the printer's `let`s
  may omit them.
- **Where:** `Outline.lean`: `partParams`, `variantTable`, `Env`.
- **Remove only if:** never.

### Long blocks are cut in one pass from the end

- **What:** A block longer than `maxLets` is cut into its chain of parts in
  one pass from the end, each part calling the next in tail position.
- **Why:** Cutting recursively copied the rest of the block at each cut:
  quadratic time and memory on a long block such as a spliced literal
  (aa2dce4).
- **Where:** `Outline.lean`: `cutLong`.
- **Remove only if:** never.

### Outline runs before the passes over the generated functions

- **What:** The pipeline runs `Outline`, then the release order at the
  start of a branch (core, `Emit/ArmRelease`:
  [ownership.md](../ownership.md#values-that-die-at-the-start-of-an-arm-are-released-newest-first)),
  then the registry's passes over
  the generated functions (`sink-proj`, `merge-fns`), then the copy anchors of
  `inline-anchors` (`Emit/CopyAnchors`, on the final functions and
  calls), then the text. (The `Array Nat`
  literal tables, which came first, went with the one array type: an
  array of `Box`es has no table form.)
- **Why:** Those passes then see bounded functions (`sink-proj` was
  quadratic in the nesting depth of uncut code, aa2dce4).
- **Where:** `lean2rr/Main.lean`: `pipeline`; `Emit/Program.lean`:
  `LoweredProgram.outline`, `LoweredProgram.runRRPasses`;
  `Emit/ArmRelease.lean`: `LoweredProgram.armRelease`;
  `Emit/CopyAnchors.lean`: `LoweredProgram.anchorCopies`.
- **Remove only if:** never.

### Known limit: Outline's own time is quadratic in a tail path's length

- **What:** Each cut computes the free variables of the whole rest of the
  path (`partParams`), so lean2rr's time is quadratic in the length of a
  tail path (a function of 1600 matches in a row took 20 s).
- **Why:** Not fixed; computing the free variables bottom-up once during
  the walk would make it linear (noted with RV6J-03, 3dcbdeb).
- **Where:** `Outline.lean`: `partParams`, `outlineTail`.
- **Remove only if:** the free variables are computed incrementally.
