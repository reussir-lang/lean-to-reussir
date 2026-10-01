# Local Reussir patches

Patches for the Reussir checkout at `./reussir` (revision `ef922049`). They
fix only the bugs that break lean2rr's output where lean2rr has no
reasonable way around them. `docs/reussir-bugs.md` describes each bug, its
repro, and why it is patched rather than worked around. The patches are
local and are not submitted upstream.

| Patch | Bug | Pass | Effect on lean2rr output |
|---|---|---|---|
| `0006-*` | 6 | `RcDecrementExpansion` / rc lowering | a static cell is never freed or reused, even after 2^32 references |
| `0004-*` | 4 | `RcCreateFusion` (`structurallySameType`) | no rrc crash on two structurally equal recursive types; `[value]` and shared records never compare equal |
| `0002-*` | 2 (structures) | `RcCreateFusion` (`markCompoundAvoidedCopies`) | a reused structure cell always gets fields that sit elsewhere in the new type |
| `0007-*` | 7 | `RcDispatchFusion` | an arm returning the matched value no longer blocks reuse in the other arms |
| `0009-*` | 9 | `RcDispatchFusion` (`fuseArm`) | a member used twice before the scrutinee's release keeps its count |
| `0005-*` | 5 | `TokenReusePass` | no rrc crash on a one-armed `if` that has to free a token |
| `0012-*` | 12 | parser (`reussir-syntax` sink) | syntax nodes are never swapped for an earlier node with a colliding hash (could fail with bogus errors or miscompile silently) |
| `0013-*` | 13 | `AcquireDropExpansion` (drop glue) | releasing a long list (or any chain of cells) runs in a loop, not one stack frame per cell |

Apply them in this order and rebuild:

```
git -C reussir checkout ef922049
git -C reussir am ../reussir-patches/0006-*.patch ../reussir-patches/0004-*.patch \
    ../reussir-patches/0002-*.patch ../reussir-patches/0007-*.patch \
    ../reussir-patches/0009-*.patch ../reussir-patches/0005-*.patch \
    ../reussir-patches/0013-*.patch ../reussir-patches/0012-*.patch
cmake --build reussir/build
```

`git am` records them as local commits. `git apply` works as well, if you
would rather keep them as uncommitted changes. Unpatched, lean2rr programs
still compile, but the bugs above can appear.

On the development machine they are applied to `./reussir` as the local
branch `l2r-local` (ef922049 + these eight commits), which is never
pushed. `docs/reussir-bugs/run.sh ./reussir` prints FIXED for each patched
bug. Each patch passed adversarial review, one to three rounds until a
round found nothing: code review, differential fuzzing against a reference
evaluator, ASan builds, and the lean2rr runtime suite and corpus.
