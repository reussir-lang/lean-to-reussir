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
| `0014-*` | 13 | `AcquireDropExpansion` (drop glue), `reussir-rt` | the other record members being freed go on a stack of pending work per thread, so any value deep through records is freed at a bounded depth; lean2rr's runtime frees its containers through the same stack |
| `0015-*` | 13 | `reussir-rt` (`drop`) | 0014's stack is cheaper (one destructor-less thread-local state, fast paths); the same order and behaviour |
| `0016-*` | 21 | `CompilePolymorphicFFI` | an unterminated `[:` in a texture body is kept as written |
| `0017-*` | 23 | `CompilePolymorphicFFI` (gather) | the texture modules are linked through one `llvm::Linker` (linear, not quadratic) |
| `0040-*` | - (a hook) | `reussir-rt` (`drop`) | `reussir_rt::drop` exports `__reussir_drop_drained`, called when a drain that released something ends: lean2rr's runtime runs a released promise's `sync` dependents there (RV7C-01) |
| `0050-*` | (feature) | frontend, `FFIObjectType`, `BasicOpsLowering` | `#[ffi(rust = "...", tagged)]`: a handle may be an odd immediate, which `rc.inc`/`rc.dec` skip; lean2rr's `Nat` and `Int` are one word (lean2rr needs it) |

Apply them in this order and rebuild:

```
git -C reussir checkout ef922049
git -C reussir am ../reussir-patches/0006-*.patch ../reussir-patches/0004-*.patch \
    ../reussir-patches/0002-*.patch ../reussir-patches/0007-*.patch \
    ../reussir-patches/0009-*.patch ../reussir-patches/0005-*.patch \
    ../reussir-patches/0013-*.patch ../reussir-patches/0012-*.patch \
    ../reussir-patches/0014-*.patch ../reussir-patches/0015-*.patch \
    ../reussir-patches/0016-*.patch ../reussir-patches/0017-*.patch \
    ../reussir-patches/0040-*.patch ../reussir-patches/0050-*.patch
cmake --build reussir/build
```

`git am` records them as local commits. `git apply` works as well, if you
would rather keep them as uncommitted changes. lean2rr's runtime needs 0014
(it uses `reussir_rt::drop`, the pending stack 0014 adds to Reussir's
runtime) and 0040 (it sets `__reussir_drop_drained`), and lean2rr's
prelude needs 0050 (it declares `Nat` and `Int` `tagged`). Without the others, lean2rr programs still compile, but the
bugs above can appear.

On the development machine they are applied to `./reussir` as the local
branch `l2r-local` (ef922049 + these ten commits), which is never
pushed. `docs/reussir-bugs/run.sh ./reussir` prints FIXED for each patched
bug (and REPRODUCES for `02b`, the variant half of bug 2, which is not
patched: lean2rr turns member packing off instead). Each patch passed
adversarial review, rounds repeated until one found nothing (one to three
rounds for most; 0014 needed a fourth round and two revisions, 0015 a fifth
round): code review, differential fuzzing against a reference evaluator,
ASan builds (Miri for the runtime patches), and the lean2rr runtime suite
and corpus. 0009 needs 0007 (it uses `consumesFusedMember`, which 0007
adds), and 0015 needs 0014. The `From <sha>` line of each patch file names
the commit in the scratch checkout where it was made; `./reussir`'s
`l2r-local` commits have the same contents and messages.

**Detailed reports** of every patch (the bug, a repro, the root cause in
Reussir's source, the fix hunk by hunk, how it was checked) and a table of
the bugs that are not patched, with the reason, are in
[`details/`](details/README.md).
