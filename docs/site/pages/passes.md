# Optional passes

<p class="lead">lean2rr's own optimizations. The tables on this page are
generated from <code>lean2rr/LeanToReussir/Opt/Registry.lean</code> and from
the guard column of
<a href="repo:docs/implementation/optional-passes.md">optional-passes.md</a>.</p>

## The rules

<div class="rule" markdown="1">
- The core translation is correct without any optional pass. The classic
  corpus and the runtime tests match native with all of them off.
- Every optional pass is on by default. No pass is switched per program or
  per benchmark.
- A pass limits itself only through checks it makes on every program: what
  soundness needs, and for some passes bounds on code size or translation
  time (the "guard").
</div>

Each pass is a module `Opt/Name.lean` with an `install` function. The
registry lists it in one line: name, on by default, description,
`install`. `install` plugs the pass into a hook of `PassConfig` and keeps
what was installed before. The hooks are:

- choices of representation (field order, `[value]` structs, cached
  placeholders, boxed constants);
- passes over the checked mono code (`monoPasses`);
- Lean definitions replaced by prelude functions;
- lowering hooks (`LowerHooks`: the J1′ choice, the form of a J4 state
  machine, constant caching, how a `cases` binds its fields);
- which helpers Stage 4 generates at the end (only those live code
  reaches: unboxing, application and conversion functions);
- passes over the generated Reussir functions (`rrPasses`).

To turn a pass off for a test:

```
lean2rr --disable-opt NAME ...
scripts/l2r.py --disable-opt NAME ...
L2R_DISABLE_OPTS=a,b tests/runtime/run.sh
lean2rr --list-opts            # prints the registry
```

## The passes, in installation order

{{v:opt_count}} optional passes.

{{gen:passes}}

### Helpers for live code only (`conv-liveness`)

At the end of Stage 4, lean2rr generates helpers that match: an unboxing
function has an arm per boxed type that can hold a value of its type, an
application function an arm per variant of its function type. An arm can
wrap or cast, and that can ask for more helpers. In a program that can
cast (one `unsafe` implementation in any library that it imports), every
unboxing function also gets an arm and a cast for every type with a
compatible layout. So the helpers grow quadratically, and almost all of
them can never run.

`conv-liveness` makes a reachability pass over the generated program, from
the entry point, the startup chain and the runtime's entry points. It
generates a helper only when live code reaches it, and an arm only for a
type or a variant that live code builds. Then it drops the functions that
nothing reaches.

- **Effect.** A program that imports `Cslib.Init` went from 990,927
  functions (1.44 GB of `.rr`) to 30,418 (26 MB). A program that imports
  `Batteries` went from 162,096 functions to 10,743. Small programs get a
  few percent fewer functions.
- **Soundness.** An arm that is left out matches a variant that no running
  code builds, so the program computes the same results. The one other
  difference is at translation time: an extern that only a removed arm
  calls is not reported as missing.

## Parts that look optional but are not

{{v:req_count}} required parts. `--disable-opt` refuses their names.

{{gen:required}}

## Edits of Lean's Stage 2 pass list

These are required too: see [Pipeline](pipeline.html#stage-2-leans-mono-pipeline).

{{gen:stage2}}
