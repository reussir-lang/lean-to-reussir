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
  N levels deep, and reuse across calls costs about depth^2.6
  ([Reussir issue 16](../../../reussir-bugs/16-nested-io-matches.md), a
  cost);
  rrc's memory is quadratic in a straight-line `Nat` function
  ([Reussir issue 17](../../../reussir-bugs/17-long-nat-block.md), a
  cost); the
  `.rr` indentation follows the nesting (a 3000-arm literal match: 126 MB
  of `.rr`, lean2rr out of memory at 16 GB; 072c620, 3597a31). A
  2000-line `main` now builds in about two minutes and 2 GB.
- **Where:** `Outline.lean`: `Limits` (`triggerDepth`, `triggerLets`,
  `maxDepth`, `maxLets`, `minRest`), `outlineFns`, `walkBlock`,
  `walkTail`, `outlineTail`, `extent`, `heavy`; `Emit/Program.lean`:
  `LoweredProgram.outline`; `lean2rr/Main.lean`: `pipeline` (`L2R_NO_OUTLINE`
  skips it, for the repros of issues 16 and 17).
- **Remove only if:** the costs of issues 16 and 17 are gone and the
  `.rr` text no longer grows with nesting.

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
  per iteration, only in functions this long.
- **Where:** `Outline.lean`: `StepInfo`, `stepInfo`, `stepVariant`,
  `stepify`, `stepDispatch`, `cycleCall?`, `hasCycleCall`,
  `tailCycleCalls`, `cycles`.
- **Remove only if:** as above.

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

- **What:** The pipeline runs the `Array Nat` literal tables, then
  `Outline`, then the registry's passes over the generated functions
  (`sink-proj`), then the text.
- **Why:** Those passes then see bounded functions (`sink-proj` was
  quadratic in the nesting depth of uncut code, aa2dce4).
- **Where:** `lean2rr/Main.lean`: `pipeline`; `Emit/Program.lean`:
  `LoweredProgram.literalTables`, `LoweredProgram.outline`,
  `LoweredProgram.runRRPasses`.
- **Remove only if:** never.

### Known limit: Outline's own time is quadratic in a tail path's length

- **What:** Each cut computes the free variables of the whole rest of the
  path (`partParams`), so lean2rr's time is quadratic in the length of a
  tail path (a function of 1600 matches in a row took 20 s).
- **Why:** Not fixed; computing the free variables bottom-up once during
  the walk would make it linear (noted with RV6J-03, 3dcbdeb).
- **Where:** `Outline.lean`: `partParams`, `outlineTail`.
- **Remove only if:** the free variables are computed incrementally.
