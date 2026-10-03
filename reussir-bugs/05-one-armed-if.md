# 5. TokenReusePass crashes on a one-armed `if`

## Summary

**Kind:** bug. **Status:** patched (0005), applied in `./reussir` (`l2r-local` cc8e5aa5).

TokenReuse matches cells freed by releases ("tokens") with later
allocations of the same size. A token that no allocation takes must be
freed on every path. If a token is available before an `if` and an
allocation inside the then-branch takes it, the pass frees it at the end
of the else-branch instead. When the `if` had no else-branch (MLIR's
canonical form of a one-armed `scf.if`), the pass looked up the first
block of an empty region, got a dangling reference, and rrc crashed with
SIGSEGV (sometimes it hung). Patch 0005 creates the missing else block,
holding only an `scf.yield`, and frees the token there.

## Symptom and repro

Repro [`repros/bug05-one-armed-if.rr`](repros/bug05-one-armed-if.rr)
(found by differential fuzzing in review round 1, finding RV-5, and reduced
by hand):

```
enum T { N(u64, T, T), L }
#[ffi(import)]
fn say(x : u64) [{ println!("{}", x) }];
fn f(x : T, y : T) -> T {
    match x {
        T::N(a, l, r) => {
            T::N { 0, match y { T::N(a2, l2, r2) => { if a2 == 0 { l } else { l2 } }, T::L => T::L{} }, l }
        },
        T::L => T::L{}
    }
}
fn size(t : T) -> u64 { match t { T::N(a, l, r) => { 1 + size(l) + size(r) }, T::L => { 0 } } }
#[main]
fn main() {
    let x = T::N{1, T::N{2, T::L{}, T::L{}}, T::L{}};
    let y = T::N{0, T::L{}, T::L{}};
    say(size(f(x, y)));
}
```

**Command.** `rrc bug05-one-armed-if.rr -O aggressive`.

**Expected.** Compiles; prints `3`.

**Actual on ef922049.** rrc dies with SIGSEGV (exit 139), at every `-O`
level, with or without `--reuse-across-call`. `run.sh` printed
`bug 05   REPRODUCES  rrc killed by SIGSEGV   [-O aggressive]`. In gdb the
crash is in `ReussirTokenFreeOp::create` → `OperationState` →
`StringMapImpl::FindKey`, called from TokenReuse (round 1). In some builds
it hangs instead (the dangling block is undefined behaviour; the patch
message says so too): one fuzz seed made the unpatched rrc spin for more
than 3 minutes.

The first lean2rr case was the prelude's panic path, which needed
`--reuse-across-call`: without that flag, the calls before the `if` flush
every token.

## Cause

`lib/Transformation/TokenReuse/TokenReuse.cpp`,
`TokenReusePass::oneShotTokenReuse`, walks each region keeping the set of
available tokens (an immutable `immer::set`). At an op with regions
(`RegionBranchOpInterface`: `scf.if`, `scf.index_switch`, dispatches), it
recurses into each region with the current set and intersects the
results. A token available before a branch op and consumed in one of its
regions (taken, or freed at a call) must be freed at the end of every
other region, where it survived:

```c++
for (size_t i = 0; i < branchResults.size(); ++i) {
  for (mlir::Value val : tokensInStableOrder(branchResults[i], dfsOrder)) {
    if (!intersection.count(val)) {
      mlir::Block &block = op.getRegion(i).front();
      frees.push_back({val, block.getTerminator()});
    }
  }
}
```

The recursion handles an empty region by returning the set unchanged:

```c++
if (region.empty())
  return availableTokens;
```

So for `scf.if %c { ... uses %tok ... }` with no else-region, the then
result lacks `%tok` and the else result still has it. The loop then calls
`op.getRegion(1).front()` on a region with no blocks. `Region::front()` on
an empty block list does not return a block, so `getTerminator()` reads
garbage. The `frees` list is materialized at the end of the pass
(`rewriter.setInsertionPoint(free.anchor); ReussirTokenFreeOp::create(...)`),
and that is where rrc crashes.

The shape, from the patch's test (`reuse_inside_scf.mlir`, function
`partial_no_else`):

```
%2 = reussir.rc.dec (%0 : !rc64) : !reussir.nullable<!reussir.token<...>>
scf.if %1 {                                   // no else region
  %tk = reussir.token.alloc : !i64token       // TokenReuse gives it %2
  %5 = reussir.rc.create value(%x : i64) token(%tk : !i64token) : !rc64
  func.call @opaque(%5) : (!rc64) -> ()
}
// on the path where %1 is false, %2 must be freed: where?
```

Where the one-armed `if` comes from: per the patch message, it is the
canonical form of an `if` whose value became a `select` and whose branch
only has side effects. In the repro it comes from the
`if a2 == 0 { l } else { l2 }` inside a constructor argument. The crash
happens at every `-O` level, because the canonicalizer runs at every
level.

## lean2rr

Runtime panics reach `l2r_stderr_put` through an `extern "C"` trampoline
called from Rust (plan §5.12), which removes the shape from the prelude.
User code can still produce it (a nested match inside a constructor
argument, with an `if` choosing between fields), at every `-O` level, so
the driver's retry without `--reuse-across-call` does not help. With the
patch no lean2rr workaround is needed any more, though the prelude change
stays.

## Patch

Patch file
[`patches/0005-l2r-local-bug-5-free-tokens-on-the-else-path-of-an-s.patch`](patches/0005-l2r-local-bug-5-free-tokens-on-the-else-path-of-an-s.patch)
(`l2r-local` commit `0f02db2c`, applied in `./reussir`; `l2r-local` head cc8e5aa5).

**New helper `getOrCreateExitBlock(region)`:**

```c++
mlir::Block *getOrCreateExitBlock(mlir::Region &region) {
  if (!region.empty())
    return &region.front();
  auto ifOp = llvm::dyn_cast<mlir::scf::IfOp>(region.getParentOp());
  if (!ifOp || &ifOp.getElseRegion() != &region)
    return nullptr;
  mlir::OpBuilder builder(ifOp.getContext());
  builder.createBlock(&region);
  mlir::scf::YieldOp::create(builder, ifOp.getLoc());
  return &region.front();
}
```

**The call site** uses it, and reports a pass failure instead of undefined
behaviour for any other op with an empty region:

```c++
-                mlir::Block &block = op.getRegion(i).front();
-                frees.push_back({val, block.getTerminator()});
+                mlir::Block *exit = getOrCreateExitBlock(op.getRegion(i));
+                if (!exit) {
+                  op.emitOpError() << "token reuse cannot free a token on "
+                                      "the path through an empty region";
+                  signalPassFailure();
+                  return {};
+                }
+                frees.push_back({val, exit->getTerminator()});
```

The test above now gives:

```
scf.if %1 {
  %3 = reussir.token.ensure(%2 ...)
  %4 = reussir.rc.create value(%x : i64) token(%3 ...)
  func.call @opaque(%4)
} else {
  reussir.token.free(%2 : !reussir.nullable<...>)
}
```

**Why it is correct.** An `scf.if` without results and without an else
region means the same as one whose else block holds only `scf.yield`. (An
`scf.if` with results always has an else region, so only result-less ifs
reach the new code.) Materializing the block changes no behaviour. It only
gives the free a place to live, exactly as if the source had an explicit
empty else. Ops with non-empty regions take the old code path unchanged.
No other region-branch op with an empty region was seen, and such an op
now fails the pass with a diagnostic instead of crashing.

**Verification.**

- Review round 2: the RV-5 repro and the round-1 fuzz seeds that crashed
  TokenReuse (generator seeds 89, 1151, 2161) compile and run correctly. A
  dedicated test (`onearm.rr`) covers the original one-armed side-effect
  `if`, nested one-armed ifs with constructions at both levels, a
  value-yielding `if` containing a one-armed one, a token produced inside
  the then-branch and consumed after it, and one-armed ifs inside
  member-match arms. It ran under six flag sets (reuse across calls on and
  off, `-O none/default/aggressive`, packed layout). The patched plain and
  ASan builds agreed with each other and with the unpatched rrc wherever
  that one compiled.
- Rounds 3 and 4: no change, included in every combined stack's fuzzing.
- On the round-2 stack: FIXED (`3`). `run.sh` on the patched build:
  `bug 05   FIXED       compiles, prints 3   [-O aggressive]`.

**Effect on lean2rr.** No rrc crash on a one-armed `if` that has to free a
token, whatever the user code.

## Upstream note

`TokenReusePass::oneShotTokenReuse` frees a token that does not survive a
region branch at `op.getRegion(i).front().getTerminator()` for every other
region. For an `scf.if` without an else region (the canonical one-armed
`if`), `front()` of the empty region is a dangling block, and rrc crashes
in `ReussirTokenFreeOp::create` (SIGSEGV or a hang) at every `-O` level.
Fix: materialize the else block (`scf.yield`) to hold the free, and report
an error for other ops with empty regions.
