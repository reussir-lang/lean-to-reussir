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

### Values spread into their fields (`flatten-structs`)

Rule 1 gives every datatype one layout. A field whose type is a type
parameter is an `L2RBox`. So the state of a loop with several variables
(`Prod Nat (Prod Nat Nat)`, an `MProd` chain) and the result of a monadic
function (`EST.Out ε σ (Except ε' α × σ')`) hold boxed fields. Each step
builds the records, boxes the fields, and the next step unboxes them.

`flatten-structs` passes such a value as its fields, each at its own type.
It works on the mono code after Stage 3, where the types are precise. It
does not change a layout.

- **Arguments.** A parameter of a join point, or of a function that calls
  itself, whose type is a structure becomes one parameter per field. Nested
  structures are split too. A parameter of another function is split when
  the function only reads it and a caller passes a value whose fields are
  known (for example a loop that passes its state to a helper).
- **Results.** A function whose result is a structure, or a type with two
  constructors (`EST.Out`, `Except`, `Option`, `ForInStep`), returns its
  fields as a `[value]` tuple. A type with two constructors adds a tag (a
  `bool`). The fields of the other constructor hold placeholders.
- **Worker and wrapper.** The function becomes a worker with the new
  signature. A wrapper keeps the old name and signature, for function
  values and entry points. Every direct call goes to the worker.

Example: a loop that counts and sums in `IO`.

```
for i in [0:n] do
  count := count + 1
  sum := sum + i
```

Before, the loop function takes `b : Prod Nat Nat`, and each step builds
`Prod.mk count' sum'` with two boxed fields. After, the worker takes
`count sum : Nat` and calls itself with `count' sum'`. At the end it
returns the tuple `(tag, count, sum, error)`, and the caller reads `count`
and `sum` from it. No step allocates or boxes.

The pass splits a value only where its fields are known: a constructor
application of the same function, a split parameter, a value that a
`cases` matched, a constant that is one constructor application, or the
result of a call that returns a tuple. A use of the whole value (stored,
passed to another function) keeps that part of a parameter whole. There
are two exceptions, where the pass builds the value again from its fields
because this adds no allocation:

- at the end of a loop, when each step built a new value. The wrapper runs
  the first step, so a loop that stops at once returns its value as it
  came;
- the result of a call, which the called function no longer builds.

The pass never builds again a value that came from the caller, a value
that is shared, or a value whose object the program looks at
(`ptrAddrUnsafe`, `dbgTraceIfShared`, `isExclusiveUnsafe`). When a loop
can stop at once and return the value that it got from its caller, the
pass does not split that part of its result for a caller that uses it
whole. The pass builds each value at most one time in each run of the code
that has the value. If two builds of one value can both run, for example
one in a join point and one before the jump to it, the pass keeps that
value whole. In a program that opens files or starts processes, it
does not change a function that takes or returns such a resource: the
release times of resources come from Lean's borrow inference on that code.

- **Effect.** Against the same build with the pass off (cachegrind): Sieve
  −54 %, MonadicInterp −51 %, Unionfind −51 %, HigherOrder −4 %,
  Liasolver −8 %, Mergesort −7 %; lean-zip compress −5 %, decompress
  −11 %.

## Parts that look optional but are not

{{v:req_count}} required parts. `--disable-opt` refuses their names.

{{gen:required}}

## Edits of Lean's Stage 2 pass list

These are required too: see [Pipeline](pipeline.html#stage-2-leans-mono-pipeline).

{{gen:stage2}}
