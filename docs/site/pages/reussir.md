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
| tagged opaque handles (local patch 0050) | one-word `Nat` and `Int` |
| textures (`#[ffi(import)]` functions with a Rust body) | the prelude's calls into `leanrt`; inlined when compiled for the same CPU |
| token reuse, `--reuse-across-call` | in-place updates, as Lean's reset/reuse |
| `#[transform_anchor]` | keeps conversion functions out of Reussir's MLIR inliner (issue 20, a cost) |

## The local patch stack

lean2rr needs Reussir built from source with local patches: branch
`l2r-local` of the checkout `./reussir`, head {{v:reussir_head}}, which is
Reussir `ef922049` plus {{v:patches_applied}} patches. The patch files are in
[reussir-bugs/patches/](repo:reussir-bugs/patches/).

<div class="rule" markdown="1">
**Policy.**

- Every Reussir problem that lean2rr meets is documented, with a repro.
- A real Reussir bug gets a small local patch, reviewed adversarially, even
  when lean2rr works around it or never triggers it.
- A build-time cost from an avoidable inefficiency gets a small patch too.
  This patch is an optimization, not a fix.
- Patches are local only: never pushed or submitted upstream.
- lean2rr keeps its workarounds, so that it also works with an unpatched
  Reussir. The exception: the runtime needs patch 0014 to build.
</div>

**Patch 0065 (bug 34), applied since 2026-10-04.** `rrc --emit executable`
compiled static code into a position-independent executable, so every
lean2rr build carried text relocations. The patch is reviewed (no defect).
The driver also keeps its workaround: it passes `--relocation-mode pic`,
and every runtime test checks that the executable has no text relocations.

**Patch 0066 (issue 35, a cost), applied since 2026-10-04.** rrc compiles
each Rust FFI snippet with its own rustc run, on every build. Every lean2rr
program has about 470 of them, so this step takes most of rrc's time
(about 13 s of 16 s for a small program). This is not a bug: the output is
correct. The patch is an optimization. It keeps the compiled snippets in a
cache directory, keyed by a digest of everything the output depends on,
except the documented cases (3 s for the same program). The driver gives
rrc the directory; an rrc without the patch ignores it. The review found a
race (a library replaced during a build); it is fixed, and a second look
checked the fix.

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
"issue NN". The table is generated from the status table of
`reussir-bugs/README.md`; each number links to the entry's file, which has
the repro, the cause in Reussir's source, and the patch explained.

{{gen:patches}}

## Two patches without an entry

[local-additions.md](repo:reussir-bugs/local-additions.md) describes them:

- **0040, a hook at the end of a drain** (`__reussir_drop_drained`).
  Reussir's runtime calls a function that the host stores when a free that
  released something ends. lean2rr's runtime uses it to resolve the
  promises released inside a free, and run their `sync` dependents, once
  the free is over. lean2rr requires the patch: its build script checks
  for it, and the runtime does not link without it.
- **0050, tagged opaque handles.** `#[ffi(rust = "...", tagged)]` makes an
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
- **`[value]` types across the FFI boundary.** Arrays of `[value]` records
  need a wrapper (`ElemBox`).
- **Guaranteed tail calls.** A mutual tail call is a sibling call only when
  all arguments fit in registers. lean2rr's join-point strategies and state
  machines keep loops in one function for this reason.
