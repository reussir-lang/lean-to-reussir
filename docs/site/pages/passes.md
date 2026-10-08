# Optional passes

<p class="lead">lean2rr's own optimizations. The tables on this page are
generated from <code>lean2rr/LeanToReussir/Opt/Registry.lean</code> and from
the guard column of
<a href="repo:docs/implementation/optional-passes.md">optional-passes.md</a>.</p>

## The rules

<div class="rule" markdown="1">
- The core translation is correct without any optional pass. The classic
  corpus and the runtime tests match native with all of them off.
- Every optional pass is on by default, except `unread-fields`: the owner
  wants it off by default. No pass is switched per program or per
  benchmark.
- A pass limits itself only through checks it makes on every program: what
  soundness needs, and for some passes bounds on code size or translation
  time (the "guard").
</div>

Each pass is a module `Opt/Name.lean` with an `install` function. The
registry lists it in one line: name, on by default, description,
`install`. `install` plugs the pass into a hook of `PassConfig` and keeps
what was installed before. The hooks are:

- passes over Stage 2's code that leave declarations out, before Stage 3
  (`prunePasses`);
- choices of representation (field order, `[value]` structs, cached
  placeholders, boxed constants);
- passes over the checked mono code (`monoPasses`);
- Lean definitions replaced by prelude functions;
- lowering hooks (`LowerHooks`: the J1′ choice, the form of a J4 state
  machine, constant caching, how a `cases` binds its fields);
- which helpers Stage 4 generates at the end (only those live code
  reaches: unboxing, application and conversion functions);
- passes over the generated Reussir functions (`rrPasses`).

To turn a pass off for a test, or to turn on a pass that is off by
default:

```
lean2rr --disable-opt NAME ...
scripts/l2r.py --disable-opt NAME ...
L2R_DISABLE_OPTS=a,b tests/runtime/run.sh
lean2rr --enable-opt unread-fields ...
L2R_ENABLE_OPTS=unread-fields tests/runtime/run.sh
lean2rr --list-opts            # prints the registry
```

## The passes, in installation order

{{v:opt_count}} optional passes.

{{gen:passes}}

### Values that no code reads (`unread-fields`)

This pass is off by default. `--enable-opt unread-fields` turns it on.

A library's `initialize` blocks often store callbacks for Lean's
elaborator: a linter's `run`, an attribute's `add` and `erase`, the hooks
of an environment extension. The program runs these blocks at startup, as
native Lean does. The program never calls the callbacks: only the
elaborator reads those fields. But lean2rr keeps every function that kept
code mentions. Through the callbacks, a program that imports `Batteries`
reaches C++ functions of the `Lean` package (`Lean.Expr.instantiate`,
`Lean.Meta.isExprDefEqAux`, …), which lean2rr's runtime does not have, and
lean2rr refuses the program. Data can do the same: a derived
`Lean.ToExpr` instance holds an `Expr`, which Lean's C++ builds, in its
field `toTypeExpr`, and no program code reads it.

The pass runs on Stage 2's code, before Stage 3. It finds, from the entry
point and the startup steps, the code that is useful:

- A field of a constructor is *read* when kept code projects it, or
  matches the constructor and uses the field.
- A variable is *useful* when kept code returns it, matches it, calls it,
  gives it to an extern, or projects a field of it. It is also useful when
  a useful value is computed from it, or when a read field or a useful
  parameter gets it.
- A parameter of a function or of a join point is useful when the body
  uses it in a useful way.
- A `let` stays when its variable is useful, or when its value can have an
  effect (a full call).

Then, in the code that stays, the pass puts `◾` in place of each value
that a constructor stores in a field that no code reads, and of each value
that an unused parameter gets. The lowering gives a placeholder for `◾` (at
a function type, the variant `z`). The `let`s that are no longer useful
and the functions that no code mentions go.

Example: Batteries registers a tag attribute with
`registerTagAttribute name descr validate`. The attribute's `add` is a
closure that holds `validate`. No kept code reads `add`, so the closure
goes. Then `validate` is an unused parameter, so the caller's lambda goes
too, and all the code that only it reaches.

The pass replaces functions and data alike, but never a field of a type
that lean2rr's runtime represents itself (strings, arrays, numbers,
thunks, tasks). No code reads a field in a generic way: equality,
hashing, `Repr`, `ToString` and the other derived instances are Lean code
that matches the value and uses each field. These fields count as read,
also when no Lean code reads them:

- every field of a type that an extern takes (by the extern's declared
  parameter type, also inside other types). A parameter declared at a type
  variable does not count: the runtime only keeps the value and gives it
  back;
- every field of `IO.FS.Stream` (the runtime writes panics with the
  current stderr's `putStr`), of the results of IO actions, and of tasks,
  thunks, references and promises.

The pass does nothing in a program that can read a value as another type
(`unsafeCast` in the program's own code). In a program whose kept code
makes tasks, it replaces a value only when it cannot hold a task, nor can
the values that a closure holds. In a program whose kept code opens files or
starts processes, it replaces no value that may hold a file handle or a
process: a handle that is released earlier is flushed and closed
earlier. A pass over the kept code follows where such values can go. The startup steps of the program, `Init` and
`Std` all run. A step of a `Lean` package constant runs when kept code
still reads the constant.

With the pass, a program that runs cedar-spec's authorizer
(`Cedar.Spec.isAuthorized`; cedar-spec imports `Batteries`) keeps 8,335 of
its 25,363 declarations. It reaches no C++ function of the `Lean`
package, and its output equals native's. lean-regex, with its `ToExpr`
instances, keeps 979 of its 1,443 declarations, and its output equals
native's.

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
