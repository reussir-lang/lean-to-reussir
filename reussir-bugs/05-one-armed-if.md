# Patch 0005: TokenReuse crashes on a one-armed `if` (bug 5)

Patch file: `../0005-l2r-local-bug-5-free-tokens-on-the-else-path-of-an-s.patch`
(`l2r-local` commit `e033367b`). Bug section:
[docs/reussir-bugs.md, bug 5](../../docs/reussir-bugs.md#5-tokenreusepass-crashes-on-a-one-armed-if).

## 1. Summary

TokenReuse matches cells freed by releases ("tokens") with later
allocations of the same size. A token that no allocation takes must be
freed on every path. If a token is available before an `if` and an
allocation inside the then-branch takes it, the pass frees it at the end
of the else-branch instead. When the `if` had no else-branch (MLIR's
canonical form of a one-armed `scf.if`), the pass looked up the first
block of an empty region, got a dangling reference, and rrc crashed with
SIGSEGV (sometimes it hung). The patch creates the missing else block,
holding only an `scf.yield`, and frees the token there.

## 2. Symptom

Repro `docs/reussir-bugs/bug05-one-armed-if.rr` (found by differential
fuzzing in review round 1, finding RV-5, and reduced by hand):

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

Command: `rrc bug05-one-armed-if.rr -O aggressive`.

- Expected: compiles; prints `3`.
- Actual on ef922049: rrc dies with SIGSEGV (exit 139) at every `-O`
  level, with or without `--reuse-across-call`. `run.sh` printed
  `bug 05   REPRODUCES  rrc killed by SIGSEGV   [-O aggressive]`. In gdb
  the crash is in `ReussirTokenFreeOp::create` → `OperationState` →
  `StringMapImpl::FindKey`, called from TokenReuse (round 1). The patch
  message adds that it sometimes hung instead; one fuzz seed made the
  unpatched rrc spin for more than 3 minutes.

The first lean2rr case was the prelude's panic path, with
`--reuse-across-call`. Without that flag, the calls before the `if` flush
every token.

## 3. Root cause

`lib/Transformation/TokenReuse/TokenReuse.cpp`,
`TokenReusePass::oneShotTokenReuse`, walks each region keeping the set of
available tokens (an immutable `immer::set`). At an op with regions
(`RegionBranchOpInterface`: `scf.if`, `scf.index_switch`, dispatches), it
recurses into each region with the current set and intersects the
results. A token that survives one region but not another (it was taken,
or freed at a call, inside the other region) must be freed at the end of
the region where it survived:

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

## 4. The fix

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

## 5. Verification

- Review round 2: the RV-5 repro and the round-1 fuzz seeds that crashed
  TokenReuse (generator seeds 89, 1151, 2161) compile and run correctly. A
  dedicated test (`onearm.rr`) covers the original one-armed
  side-effect `if`, nested one-armed ifs with constructions at both levels,
  a value-yielding `if` containing a one-armed one, a token produced
  inside the then-branch and consumed after it, and one-armed ifs inside
  member-match arms. It ran under six flag sets (reuse across calls on and
  off, `-O none/default/aggressive`, packed layout). The patched plain and
  ASan builds agreed with each other and with the unpatched rrc wherever
  that one compiled.
- Rounds 3 and 4: no change, included in every combined stack's fuzzing.
- `run.sh` on the patched build:
  `bug 05   FIXED       compiles, prints 3   [-O aggressive]`.

## 6. Effect on lean2rr

lean2rr had already reshaped its prelude: runtime panics reach
`l2r_stderr_put` through an `extern "C"` trampoline called from Rust
(plan §5.12), which removes the shape from the prelude. User code can
still produce it: a nested match inside a constructor argument, with an
`if` choosing between fields. It does so at every `-O` level, so the
driver's retry without `--reuse-across-call` does not help. The patch
removes the crash. No lean2rr workaround is needed for it any more, though
the prelude change stays.

## 7. Upstream note

`TokenReusePass::oneShotTokenReuse` frees a token that does not survive a
region branch at `op.getRegion(i).front().getTerminator()` for every other
region. For an `scf.if` without an else region (the canonical one-armed
`if`), `front()` of the empty region is a dangling block, and rrc crashes
in `ReussirTokenFreeOp::create` (SIGSEGV or a hang) at every `-O` level.
Fix: materialize the else block (`scf.yield`) to hold the free, and report
an error for other ops with empty regions.
