# 6. Static cells accumulate increments until the 32-bit count wraps

## Summary

**Kind:** bug, with a flag workaround. **Status:** patched (0006).

**Verdict: bug, with a flag workaround.** Reussir's lowering states that a
nullary dummy's count stays above the shared/unique decision point, but the
default (TBI) encoding increments it unguarded with a 32-bit count. The two
documented encodings `--nullary-variant-encoding arch-independent` and
`boxed` avoid it: the repro prints `4294967300` with either. 0006 keeps the
default encoding and its unguarded increment, so it is a speed choice over
the flag. Measured on 2026-10-02 (pinned, best of 5, a loaded machine, so
only indicative), `arch-independent` against the default with 0006,
lean2rr/native time: rbtree 0.44/0.45, deriv 0.75/0.83, cfold 0.79/0.74,
binarytrees 0.94/0.85, mergesort 0.52/0.46, monadic-interp 1.03/1.01: a
few percent slower on three programs, faster on one. Remeasure on an idle
machine before deciding between the flag and the patch.

Reussir does not allocate nullary constructors such as `Nil` or `Leaf`.
Each one is an *immediate*: a tagged pointer to a single static "dummy"
cell. On aarch64, a retain of an immediate still increments the dummy's
32-bit reference count, and nothing ever decrements it. The count starts
at 2, so after 2^32 − 1 net increments (about 2^32 references) it wraps
around to 1. The next release then believes it
holds the last reference, takes the "free the cell" branch, and hands the
static dummy to the allocator: the program dies with SIGSEGV. Patch 0006
makes that branch first check whether the value is one of its type's
immediates; if it is, the release frees nothing and produces no reuse
token. Retains stay exactly as cheap as before.

## Symptom and repro

Repro [`repros/bug06-static-count-wrap.rr`](repros/bug06-static-count-wrap.rr):

```
enum L { Nil, Cons(u64, L) }
fn len(l : L) -> u64 {
    match l { L::Nil => { 0 }, L::Cons(x, t) => { 1 + len(t) } }
}
fn loop_(x : L, n : u64, acc : u64) -> u64 {
    if n == 0 { acc } else { loop_(x, n - 1, acc + len(x)) }
}
#[ffi(import)]
fn say(x : u64) [{ println!("{}", x) }];
#[ffi(import)]
fn count() -> u64 [{ std::env::args().nth(1).and_then(|s| s.parse().ok()).unwrap_or(4294967300) }];
#[main]
fn main() { say(loop_(L::Cons{1, L::Nil{}}, count(), 0)); }
```

`count()` is the first argument. Every call of `len` binds the tail `t`,
which is the `Nil` immediate, and so retains it once. The matching release
takes the "shared" path, which skips its store for immediates (see below).
Each call therefore adds one net increment to the `Nil` dummy's count. In
Lean the same program is:

```lean
@[noinline] def len (l : List Nat) : Nat := l.length
def loop (x : List Nat) : Nat → Nat → Nat
  | 0, acc => acc
  | n+1, acc => loop x n (acc + len x)
def main (args : List String) : IO Unit :=
  IO.println (loop [args.length] 4294967300 0)
```

**Command.** `rrc bug06-static-count-wrap.rr` with lean2rr's flags (`-O
aggressive --no-pack-record-members --reuse-across-call`), then `./bug06
4294967300`.

**Expected.** `4294967300`.

**Actual on ef922049.** SIGSEGV (exit 139) after about 15 s. With
`4294967290` it prints `4294967290`, because the count has not wrapped yet.
`run.sh` printed
`bug 06   REPRODUCES  N = 4294967300: SIGSEGV (static Nil freed)`.

## Cause

**The immediate encoding.** The pass `reussir-special-pointer-tag`
(`lib/Transformation/SpecialPointerTag/SpecialPointerTag.cpp`) rewrites
every construction of a nullary arm of a "taggable" shared enum into a
`reussir.rc.tagged` immediate: no allocation, no token. The value points
at a per-tag dummy box `{i32 count, i32 tag}` (a `linkonce_odr` global, so
every compilation unit agrees on one address per tag). There are two
encodings, chosen in `crates/reussir-compiler/src/driver/stage.rs`
(`--nullary-variant-encoding arch-dependent`, the default):

- `tbi` on aarch64. The top byte of the pointer is `tag + 1` and the low
  bits are the dummy's address. aarch64's Top Byte Ignore makes loads and
  stores ignore the top byte, so a retain or a tag read through an
  immediate is an ordinary load or store into the dummy. The dummy's count
  starts at 2.
- `immortal` on every other target. The immediate is the dummy's plain
  address, the count starts at 3·2^30, and immediates are recognized by
  the size of their count.

**The invariant, and where it fails.** The comment block at the top of
`lib/Conversion/BasicOpsLowering/BasicOpsLowering.cpp` states the scheme's
invariant: the dummy's count is "pinned above the shared/unique decision
point". `rc.set`, the only store that lowers a count (the shared path of a
release), skips immediates (`ReussirRcSetConversionPattern`, behind
`emitGuardedStore`, which skips the store behind an unlikely branch; the
comment block itself still says `rc.set` "steers a recognized-immediate
access to a separate scratch word (an address select ...)", which is stale:
the code branches around the store, and 0006 leaves that comment line as
it is). Increments are left unguarded:

```
//   In the immortal encoding on targets narrower than 64 bits,
//     `rc.inc`'s store is steered away from a recognized dummy as well —
//     2^(w-2) unbalanced increments would otherwise be reachable and wrap
//     the count. (With w = 64 that is > 4 * 10^18 increments: unreachable,
//     so the increment stays guard-free on 64-bit targets.)
```

But the count word is 32 bits wide: `ReussirRcIncConversionPattern` uses
`auto countType = rewriter.getI32Type();`, and the dummy is two `i32`s.
Under TBI the increment is a plain `load i32; add 1; store i32` into the
dummy, so the "unreachable" wrap takes only 2^32 − 1 net increments from
the starting count of 2. Only the
immortal encoding steers the increment's store (`steerNarrowImmortal`,
which despite its name applies to every immortal-encoded taggable type,
and so already guards the increment of the shared dummy). Bug 6 therefore
needs TBI, so it happens on aarch64 only. The review confirmed that x86-64
never selects TBI.

**The release.** `RcDecrementExpansionPattern`
(`lib/Conversion/RcDecrementExpansion/RcDecrementExpansion.cpp`) expands
each `rc.dec` like this (pseudo-IR):

```
%prev = reussir.rc.fetch %v                  // load the count
%one  = arith.cmpi eq, %prev, 1
%tok  = scf.if (expect %one, true) {         // "unique" branch
          reussir.ref.drop (rc.borrow %v)    // release the contents
          %t = reussir.rc.reinterpret %v     // the cell becomes a token
          scf.yield nonnull(%t)
        } else {                             // "shared" branch
          reussir.rc.set %v, %prev - 1       // skipped for immediates
          scf.yield null
        }
```

The decrement skips static pointers but tests "count == 1 → free" first:
nothing on the unique branch looks at the pointer. Once the dummy's count
has wrapped to 1, the release of a `Nil` takes the unique branch, and the
dummy becomes a token. TokenReuse then either frees it (`token.free` →
`__reussir_deallocate` → `mi_free` on a tagged pointer, SIGSEGV) or gives
it to a later construction, which writes a new cell over the static dummy.

A second, quieter error: after each increment the lowering emits
`llvm.assume(old >= 1)`, with the comment "Valid for immediates too: the
dummy box's count starts at 2 and only ever grows". When the count passes
through 0, that assumption is false, which is undefined behaviour for LLVM.

## lean2rr

Any Lean program on aarch64 that takes more than about 4·10^9 references
to the same nullary constructor (`[]`, `none`, a `leaf`), for example a
long loop over a structure that contains one, crashed. lean2rr cannot
avoid it in its own output: the retains come from Reussir's own lowering.
It could pass `--nullary-variant-encoding arch-independent` (or `boxed`)
to rrc; it uses 0006 instead, which keeps the default encoding (see the
verdict above).

## Patch

Patch file
[`patches/0006-l2r-local-bug-6-never-free-a-tagged-immediate-whose-wrapped-count.patch`](patches/0006-l2r-local-bug-6-never-free-a-tagged-immediate-whose-wrapped-count.patch)
(`l2r-local` commit `565f9862`).

The increment stays a plain load, add and store, so LLVM can still fold
counts on fresh cells. The decrement's unique branch (count == 1) first
checks whether the value is one of its type's nullary immediates; if it
is, the decrement frees nothing and yields no token, so a wrapped count can
never free or reuse the static cell. The `assume(old >= 1)` becomes
`old >= 1 || top byte != 0`. Hunk by hunk:

**Hunk 1 (RcDecrementExpansion.cpp, new `immediateTagsToGuard`).** It
returns the nullary tags a released value may be the immediate of:

- none if the module has no `kSpecialPtrTagAttr`, or if the type cannot
  carry a tag (`mayCarrySpecialPointerTag`);
- for a destructuring decrement of arm `tag`, that tag if the arm is
  nullary. An arm with members is a real box: the dispatch has proved the
  tag;
- otherwise every nullary arm of the type.

**Hunk 2 (same file, at the start of the unique branch).** If there are
such tags, the original unique path is wrapped in a guard:

```c++
mlir::Value same = ReussirRcCompareImmortalOp::create(
    rewriter, op.getLoc(), rewriter.getI1Type(), op.getRcPtr(),
    rewriter.getIndexAttr(tag));
...   // OR over the tags
auto guard = mlir::scf::IfOp::create(
    rewriter, op.getLoc(), op->getResultTypes(),
    ReussirExpectOp::create(rewriter, op.getLoc(), isImmediate, false)
        .getLikely(),
    true, true);
// then: yield a null token; else: the original unique path
```

The resulting shape (from the patch's test
`rc_dec_expansion_immediates.mlir`):

```
%cnt = reussir.rc.fetch ...
%one = arith.cmpi eq, %cnt, ...
scf.if %one {
  %imm = reussir.rc.compare_immortal(%arg0) tag(0)
  scf.if (reussir.expect %imm, false) {
    scf.yield (reussir.nullable.create)      // no drop, no token
  } else {
    reussir.ref.drop ... ; reussir.rc.reinterpret ...
  }
} else { ... rc.set ... }
```

`rc.compare_immortal` already existed. Its lowering compares the pointer
with a link-time constant (`(tag + 1) << 56 | &dummy` under TBI): one
compare, no load. A real cell can never have a dummy's address, so the
test is exact.

**Hunk 3 (BasicOpsLowering.cpp, `ReussirRcIncConversionPattern`).** The
increment itself is unchanged: still a plain load, add and store, so LLVM
can still fold the counts of freshly allocated cells. Under TBI, for
taggable types, the assumption becomes `old >= 1 || top byte != 0`.

**Hunk 4.** The scheme's comments are updated to say that under TBI the
dummy's count does grow and wrap, and that the release rejects immediates
on its unique branch instead. A new FileCheck test covers the expansion,
and one more case in `special_pointer_tag_lowering.mlir` covers the
increment.

**Why it is correct.** A wrapped count can still steer an immediate into
the unique branch, but that branch now does nothing observable for it: no
drop, no token, so no free and no reuse. The shared branch is unchanged,
and `rc.set` still skips the dummy. A real cell is never equal to a dummy
address, so real cells take the old path. The guard is also emitted under
the immortal encoding (the module attribute is set for both). There it is
redundant but harmless. The drop glue's member releases go through the
same pattern (AcquireDropExpansion reuses it), so they are covered too.
0013's `drop_and_free` returns early for nullary arms for the same reason
([bug 13](13-long-list-drop.md)).

**Alternative tried first.** The first version guarded the increment's
store instead (an address `select` that sent an immediate's store to a
scratch word). Review round 1 (finding RV-2) measured it at +17-34% on a
retain-heavy microbenchmark and +29% on rbtree on the test machine's
Cortex-A725 cores. It also hid the count of a freshly allocated cell from
LLVM, so increments on new cells stopped being folded. The sources quote
different peak costs for that version: "up to 22%" on the Cortex-A725
cores (this entry's own measurement), "up to 30%" (the patch message) and
34% (the review's microbenchmark).

**Verification.**

- Review round 1 rejected the store-guard version (above). Round 2
  reviewed this version with forced wraps: an FFI hook reset every dummy's
  count to 1, 0 or 2^32−1 before each operation. The tests covered plain
  and destructuring releases, TRMC, drop glue, arrays (splat, set,
  copy-on-write), closures capturing `Nil`, `[value]` records holding
  `Nil` and shared structs, at `-O aggressive`, `default` and `none`. All
  were correct, and unpatched builds crashed. Wrap fuzzing ran 2000
  generated programs × 3 wrap values. A real wrap (a Lean program with
  4294967300 iterations, through lean2rr) passed in 18.5 s.
- Rounds 3, 4, 4b and 4c repeated the forced-wrap tests and wrap fuzzing
  with 0013 and 0014 applied.
- On the round-2 stack: FIXED (`4294967300`, 14 s). `run.sh` on the
  patched build:
  `bug 06   FIXED       N = 4294967300: prints 4294967300   [-O aggressive --no-pack-record-members --reuse-across-call]`.
- **Cost.** About 4% on rbtree and nothing measurable elsewhere, on both
  core types of the test machine. Review round 2 (finding R2-3) measured
  +11% on the microbenchmark on Cortex-A725 and +2% on Cortex-X925, and
  rbtree +2.7%. Round 2 (finding R2-4, still present in round 3) also
  measured a side effect: the extra branch makes TokenReuse find slightly
  fewer reuses, 0.2 to 1.2% more allocations in 12 of 120 generated test
  programs. The suspected cause is that the guard nests the unique branch
  one `scf.if` deeper, which hides some member releases from TokenReuse's
  search for tokens trapped in branches. Round 3 found both unchanged;
  judged acceptable against a crash. The same nesting has the opposite
  effect on [bug 7](07-phantom-reuse-donor.md)'s phantom donors: on
  `l2r-local` the member releases of a matched node sit one `scf.if`
  deeper, TokenReuse frees their tokens inside, and the node's own cell is
  reused even where 0007 cannot fire (observed 2026-10-02 with
  `repros/bug07b-call-before-branch.rr`: ratio 1.34-2.08 with the default
  encoding, 5.61-11.37 with `--nullary-variant-encoding boxed`, which emits
  no guard; commands and the remarks in bug 7's entry).

**Effect on lean2rr.** A static cell is never freed or reused, even after
2^32 references: the long loops above no longer crash.

A remaining caveat, from review round 1 (RV-6), which cannot be reproduced
on the test machine: TBI treats any pointer with a nonzero top byte as an
immediate. An allocator that tags real pointers would make real cells look
like immediates (see "Tagged pointers from the allocator" in
[the index](README.md#other-observations)).

## Upstream note

Under the TBI nullary-variant encoding, `rc.inc` increments the static
dummy box's 32-bit count unguarded, so about 2^32 references to one nullary
constructor wrap it to 1. A release then frees or reuses the static dummy
(SIGSEGV in `mi_free`), and the `assume(old >= 1)` after `rc.inc` becomes
false. Repro: a loop that passes a one-element list to a function matching
it 4294967300 times on aarch64. A fix that keeps `rc.inc` unguarded: test
for the type's immediates (`rc.compare_immortal`) on the release's
unique branch.
