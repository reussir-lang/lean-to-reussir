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

- choices of representation (field order, `[value]` structs, one-word
  `Nat` arrays, cached placeholders);
- a part of Stage 3 (split map loops, uniform updates);
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

## Parts that look optional but are not

{{v:req_count}} required parts. `--disable-opt` refuses their names.

{{gen:required}}

## Edits of Lean's Stage 2 pass list

These are required too: see [Pipeline](pipeline.html#stage-2-leans-mono-pipeline).

{{gen:stage2}}
