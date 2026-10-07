# Reussir

<p class="lead">The compiler that lean2rr targets, and the local patches that
lean2rr's builds use. Source: <a href="repo:reussir-bugs/README.md">reussir-bugs/README.md</a>
(the status table below is generated from it).</p>

## What Reussir is

Reussir is a research compiler framework for reference-counted functional
programs (github.com/reussir-lang/reussir). Its front end is in Rust, its
back end in MLIR and C++, its runtime in Rust. Its main idea: reusable
memory is explicit in the IR. A cell that dies becomes a *token*, and a later
allocation of the same size can use the token instead of new memory. Reussir
does the ownership analysis (Perceus-style reference counting), token reuse,
drop glue, and LLVM code generation.

lean2rr writes Reussir source (`.rr`) and lets Reussir do all memory
management. This is why lean2rr stops Lean's pipeline before the impure
phase: Reussir replaces Lean's reference counting and reset/reuse.

{{svg:rrc}}

What lean2rr uses from Reussir, and how:

| Feature | lean2rr's use |
|---|---|
| shared and `[value]` records and enums | Lean's inductive types ([Representations](representations.html)) |
| opaque `#[ffi]` types | `LStr`, `RVec`, `LCell`, handles: runtime types that do their own counting |
| tagged opaque handles (local patch 41-a) | one-word `Nat` and `Int` |
| textures (`#[ffi(import)]` functions with a Rust body) | the prelude's calls into `leanrt`; inlined when compiled for the same CPU |
| token reuse, `--reuse-across-call` | in-place updates, as Lean's reset/reuse |
| `#[transform_anchor]` | keeps unboxing, wrapper and cast functions out of Reussir's MLIR inliner (issue 20, a cost) |

## The local patch stack

lean2rr needs Reussir built from source with local patches: Reussir
`ef922049` plus the {{v:patches_total}} patches of
[reussir-bugs/patches/series](repo:reussir-bugs/patches/series), in that
order. Each patch belongs to one entry and is named after it: the file
`13-b-pending-release-stack.patch` is the second patch of issue 13, and the
text calls it 13-b. Branch `l2r-local` of the checkout `./reussir` (head
{{v:reussir_head}}) has the first {{v:patches_applied}} patches of the
series.

<div class="rule" markdown="1">
**Policy.**

- Every Reussir problem that lean2rr meets is documented, with a repro.
- A real Reussir bug gets a small local patch, reviewed adversarially, even
  when lean2rr works around it or never triggers it.
- A cost from an avoidable inefficiency (build time, or run time as in
  issue 3) gets a small patch too. This patch is an optimization, not a
  fix. A missed optimization gets a patch only when lean2rr cannot work
  around it (issue 36).
- Patches are local only: never pushed or submitted upstream.
- lean2rr keeps its workarounds, so that it also works with an unpatched
  Reussir. The exceptions are the features that lean2rr requires: the
  runtime needs patch 13-b to build, the prelude needs 41-a, and the
  driver requires 40-a, 38-a and 13-d.
</div>

**Patch 34-a (bug 34), applied since 2026-10-04.** `rrc --emit executable`
compiled static code into a position-independent executable, so every
lean2rr build carried text relocations. The patch is reviewed (no defect).
The driver also keeps its workaround: it passes `--relocation-mode pic`,
and every runtime test checks that the executable has no text relocations.

**Patch 35-a (issue 35, a cost), applied since 2026-10-04.** rrc compiles
each Rust FFI snippet with its own rustc run, on every build. Every lean2rr
program has about 470 of them, so this step takes most of rrc's time
(about 13 s of 16 s for a small program). This is not a bug: the output is
correct. The patch is an optimization. It keeps the compiled snippets in a
cache directory, keyed by a digest of everything the output depends on
(the documented exceptions are in the issue's file). With a full cache,
rrc takes about 3 s for the same program. The driver gives rrc the
directory; an rrc without the patch ignores it. The review found a
race (a library replaced during a build); it is fixed, and a second look
checked the fix.

**Patch 13-d (issue 13), not applied yet.** Inside a free, the drop glue
releases the last record field of a cell after the cell, directly. So a
chain through that field is freed in a loop. But this field then comes
before the work that the other fields of the cell pushed, and Lean
releases the last field first. The patch keeps a field for last only when
no field after it can push work (an array, a thunk or task cell, a
`[value]` record). Otherwise the glue pushes every record field, in field
order.

**Patch 36-a (issue 36, a missed optimization), not applied yet.** Reussir
code calls a Rust FFI snippet through a small trampoline that rrc makes.
The trampoline only packs the arguments. Neither function has an inline
attribute, so LLVM uses its cost model alone. At a call site that LLVM
thinks is rare (deep in branches), it inlines only very small functions
(cost 45). The read of an `Array` element became too large for this limit
with the one-word `Box`, so such reads stayed calls. The patch marks a
snippet and its trampoline `alwaysinline` when the snippet's cost is at
most the limit of a usual call site (cost 225, or 250 at `-O
aggressive`). Larger snippets do not change. The review found that
`alwaysinline` also skipped LLVM's stack limit for recursive callers: a
snippet with a 64 KiB buffer, inlined into a recursive function,
overflowed the stack. Patch 36-b leaves out snippets with a stack frame
over 1024 bytes and snippets that cannot return (panics).

**Patch 03-a (issue 3, a cost), not applied yet.** Reussir's Rust
allocator gives every Rust allocation 16-byte alignment, on purpose.
For sizes of at most 64 bytes, mimalloc gives this alignment from a
block's size class only when the size is a multiple of 16. For other
small sizes it sometimes allocated a larger block and moved the pointer. Then every later free in the same page took
mimalloc's slow path, also for lean2rr's own objects. The patch rounds the
size of a Rust allocation up to a multiple of 16. The alignment stays 16,
and mimalloc does not move these pointers any more. Patch 03-b (review
fixes) keeps the exact size in the sanitizer builds, which use the C
allocator.

## All entries

{{v:bug_entries}} entries. Each entry is a numbered *issue*. Its kind (column
*Kind*) tells what it is:

- A *bug* is wrong behaviour: a crash, a wrong result, valid code that is
  rejected, or a broken build.
- A *cost* is correct but slow or big (build time, memory, run time). A
  *missed optimization* is correct but slower than it can be. A *missing
  feature* is something that Reussir does not promise but Lean needs. An
  *intended* entry is documented behaviour.
- Only a bug is wrong behaviour. For the other kinds the output is correct,
  and a patch is an optimization or a feature, not a fix.

Older text and commit messages say "bug NN" for every entry; read it as
"issue NN". They also cite patches by old four-digit numbers (0002 to
0069); the README of `reussir-bugs/` maps each to its new name. The table
is generated from the status table of
`reussir-bugs/README.md`; each number links to the entry's file, which has
the repro, the cause in Reussir's source, and the patch explained.

{{gen:patches}}

## Two features for lean2rr's runtime

Two of the missing features are needed only by lean2rr's runtime and
prelude:

- **40-a, a hook at the end of a drain** (`__reussir_drop_drained`,
  [issue 40](repo:reussir-bugs/40-drain-end-hook.md)).
  Reussir's runtime calls a function that the host stores when a free that
  released something ends. lean2rr's runtime uses it to resolve the
  promises released inside a free, and run their `sync` dependents, once
  the free is over. lean2rr requires the patch: its build script checks
  for it, and the runtime does not link without it.
- **41-a, tagged opaque handles**
  ([issue 41](repo:reussir-bugs/41-tagged-ffi-objects.md)).
  `#[ffi(rust = "...", tagged)]` makes an
  odd handle an immediate that is not counted. lean2rr's one-word `Nat` and
  `Int` need it.

## How the patches are checked

Each patch is reviewed adversarially: code review, differential fuzzing
against an independent reference evaluator, ASan builds (Miri for the
runtime patches), and lean2rr's runtime suite and corpus, in rounds until a
round finds nothing. `reussir-bugs/repros/run.sh RRC_CHECKOUT` builds every
repro on a given rrc and prints `REPRODUCES` or `FIXED` for each issue.

## Missing features that cost performance

Not bugs, but each one costs lean2rr measurably:

- **Borrowed parameters.** Every read of an array or string takes the
  container owned. A traversal that keeps the nodes it visits pays
  increments and releases that native Lean does not (about 1.5× native on
  such a traversal).
- **Inlining of runtime calls (issue 36, a missed optimization).** rrc's
  import trampolines carry no inline attribute, so LLVM inlines a runtime
  function at a call site it judges cold only when the function is small.
  lean2rr keeps its array and string read functions small;
  `tests/runtime/ffi-inline-check.sh` fails if a read stays a call.
  Patches 36-a and 36-b (not applied yet) inline small runtime functions
  at such sites.
- **The choice of a reuse token (issues 7 and 39, missed optimizations).**
  When two dead cells have the right size, token reuse takes the one
  released last. A release that never frees can win: a cell that a later
  field still holds (issue 7), or a value that an opaque call returned
  while another reference to it stays live (issue 39). The new cell is
  then allocated, and the cell that does die is freed. lean2rr binds the
  fields of a live matched value late (`lazy-fields`) because of issue 7.
  Because of issue 39, lean2rr boxes a field again when it puts the field
  back into a rebuilt node. If it put back the field's own box, the
  unboxed value would die there, and `RtProbeBump` would allocate one list
  cell for each rebuilt node.
- **`[value]` types across the FFI boundary.** A `[value]` struct of
  several fields in a box, a once-cell or a polymorphic extern's argument
  needs a wrapper (`ElemBox`).
- **Guaranteed tail calls.** A mutual tail call is a sibling call only when
  all arguments fit in registers. lean2rr's join-point strategies and state
  machines keep loops in one function for this reason.
