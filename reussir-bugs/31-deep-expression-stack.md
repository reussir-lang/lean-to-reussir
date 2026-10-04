# 31. rrc overflows its stack on deeply nested expressions

## Summary

**Kind:** bug (crash on valid input). **Status:** patched (0063), applied in `./reussir` (`l2r-local` cc8e5aa5).

**Verdict: bug.** rrc aborts with "thread 'main' has overflowed its stack"
on a sum of 8000 terms, or a literal in 100000 parentheses. Reussir's
parser is written to survive such input (it grows its own stack with
`stacker`, and `reussir-syntax` tests a 100000-deep parenthesized
expression), but the stages after it recurse on the process's 8 MiB main
thread. The first to overflow is the elaborator (type inference).

## Symptom and repro

Repro [`repros/bug31-deep-expression.py`](repros/bug31-deep-expression.py)
`N DEPTH OUT.rr` writes `chain`, a sum of N calls `f(z, 0) + f(z, 1) +
...` (a left-nested `+` tree N deep: the shape of
[bug 11](11-sccp-call-graph.md)'s generator, where it was found at
N = 8000), and `parens`, a literal in DEPTH parentheses. The program prints
`N + N(N-1)/2 + 7`.

**Command.** `rrc OUT.rr -O aggressive` (N = 8000, DEPTH = 100000).

**Expected.** Compiles; prints `32004007`.

**Actual on ef922049.** rrc aborts (SIGABRT): `thread 'main' (…) has
overflowed its stack`, `fatal runtime error: stack overflow, aborting`.
Either shape alone does it, the sum already with `--emit hir` (the output
of elaboration); a sum of 4000 terms still builds. `run.sh` prints
`bug 31   REPRODUCES  rrc: thread 'main' has overflowed its stack
(SIGABRT)`.

## Cause

The backtrace of the overflow (gdb, N = 8000) is about 10000 frames of

```
reussir_core::semi::ctxt::Elaborator::infer_binop
reussir_core::semi::ctxt::Elaborator::infer_expr
reussir_core::semi::ctxt::Elaborator::infer_binop
...
Elaborator::check_expr ← check_function ← run_files ← run ← driver::frontend
```

`infer_expr` (`crates/reussir-core/src/semi/check.rs`) dispatches on the
surface expression and `infer_binop` infers both operands with
`infer_expr`: one pair of frames per `+`, about 1 KiB of stack per nesting
level. The parser does not overflow: it wraps its recursion in
`stacker::maybe_grow` (`crates/reussir-syntax/src/parser/expr.rs`,
`grammar.rs`). The elaborator and the later stages (HIR to MIR lowering,
codegen of expression trees, and the drop of a deep `cstree` syntax tree,
which `reussir-syntax`'s own deep-parenthesis test runs on a 256 MiB thread)
do not. `rrc`'s `main` (`crates/reussir-compiler/src/main.rs`) runs the
whole driver on the main thread, whose stack is the process limit (8 MiB
here).

## lean2rr

Not expected to be hit: lean2rr emits let-bound code (Lean's IR is in
A-normal form) and cuts tail paths and `let` values deeper than 8 levels
into functions ([bug 16](16-nested-io-matches.md)). The patch costs
lean2rr nothing; its 1 GiB stack is virtual address space and counts
against a `ulimit -v` (like rrc's other threads): rrc's peak virtual size
on a lean2rr program goes from 1.9 to 3.1 GB, its resident size is
unchanged, and under a limit too tight for the stack rrc falls back to the
main thread.

## Patch

Patch file
[`patches/0063-l2r-local-bug-31-run-rrc-s-driver-on-a-thread-with-a.patch`](patches/0063-l2r-local-bug-31-run-rrc-s-driver-on-a-thread-with-a.patch)
(`l2r-local` commit `f8afea34`, applied in `./reussir`; `l2r-local` head cc8e5aa5; made as commit `b2e0bfd3`
in a scratch checkout; it depends on no other patch). `main` runs the driver on a thread with a 1 GiB
stack:

```rust
const DRIVER_STACK_SIZE: usize = 1024 * 1024 * 1024;

fn main() -> ExitCode {
    // Named `main` so diagnostics (a panic, a stack overflow) read as before.
    let spawned = std::thread::Builder::new()
        .name("main".into())
        .stack_size(DRIVER_STACK_SIZE)
        .spawn(reussir_compiler::driver::main);
    match spawned {
        Ok(driver) => match driver.join() {
            Ok(code) => code,
            // The panic was reported on the driver thread; exit as a
            // panicking main thread would.
            Err(panic) => std::panic::resume_unwind(panic),
        },
        // The stack is reserved address space, so a tight address-space
        // limit (`ulimit -v`) can refuse it: run the driver here, on the
        // main thread's stack, as rrc did before.
        Err(_) => reussir_compiler::driver::main(),
    }
}
```

One change covers every recursive stage, instead of a `stacker` call in
each walk. If the thread cannot be created (an address-space limit,
review RV8RE-02), `main` calls the driver itself, on the main thread, as
before.

**Why it is correct.** The driver does the same work on another thread;
the main thread only waits. Its exit code is returned unchanged. A panic is
reported by the driver thread's panic hook (the thread is named `main`, so
the message reads as before) and re-raised on the main thread with
`resume_unwind`, which does not run the hook again, so the process exits as
a panicking main thread does (101). Only the stack pages the driver touches
are committed, so normal builds use the memory they used before. 1 GiB is
about a million nesting levels at the measured 1 KiB per level. The
fallback runs exactly the old code path.

**Verification.**

- The repro builds and prints `32004007` (1.75 s, 176 MB). Sums of 16000
  and 64000 terms build (6 s and 81 s, -O aggressive), and the 100000
  parentheses alone build in 0.1 s; bug 11's generator at N = 8000 passes
  the frontend.
- Test `frontend/deep_expression.rr` (program generated by
  `Inputs/deep_expression.py`: both shapes, built, linked and run with a C
  driver). It fails on the unpatched build.
- Reussir's lit suite and lean2rr's runtime tests: as for
  [bug 28](28-unique-carrying-join.md) (every rrc run in them goes through
  the new thread).
- `run.sh`: `bug 31   FIXED       compiles, prints 32004007`.

**Review.** Round RV8 (e)
(local review notes): no correctness
defect. Exit codes (success, compile error, `--help`, a bad flag, a
closed or piped stdout), stdout and stderr are the same as before; a
panic prints once and exits 101, a stack overflow still aborts (134), and
`process::exit` codes pass through. **RV8RE-02** (low): the 1 GiB stack is
reserved address space, which `ulimit -v` counts, so under a limit between
about 0.4 and 1.5 GB rrc panicked at startup ("failed to spawn the driver
thread", exit 101) where it used to compile. Fixed in the final 0063: if
the thread cannot be created, the driver runs on the main thread as
before (test `frontend/driver_stack_address_limit.rr`, a build under
`ulimit -v 1000000`). lean2rr's `bin/l2r` limit (16 GB) and the memory cap
of `cg` (resident memory) are not affected either way.

**Effect on lean2rr.** None.

## Upstream note

`rrc` runs its driver on the 8 MiB main thread; the parser grows its stack
with `stacker`, but `Elaborator::infer_expr`/`infer_binop` (and later
stages) recurse once per nesting level (about 1 KiB each), so a sum of 8000
terms or 100000 nested parentheses aborts with a stack overflow. Fix: run
`driver::main` on a thread with a large stack (here 1 GiB, named `main`),
or `stacker::maybe_grow` in each recursive walk.
