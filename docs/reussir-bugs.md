# Reussir bugs that affect lean2rr

Every Reussir bug lean2rr has run into, including those it works around or
never triggers, with a repro, the cause where known, what lean2rr does about
it, and the state of a local patch.

Reussir revision: `ef922049`. The checkout at `./reussir` is not part of
this repository. Reussir is patched locally only where a bug breaks
lean2rr's output and lean2rr has no reasonable way around it. Each patch
was reviewed adversarially before it was applied: code review,
differential fuzzing against a reference evaluator, ASan builds and the
lean2rr test suites, over three rounds. The eight patches are in
`reussir-patches/` (see its README). They are applied to `./reussir` as
local commits on its branch `l2r-local` (ef922049 + the eight). They are
not submitted upstream. lean2rr's workarounds stay in place where they are
still needed (bugs 1, 2 for variants, 3, 10, 16, 17, 19).

## Repros

`docs/reussir-bugs/` has one repro per bug: a plain Reussir program
(`bugNN-name.rr`), a Lean program built through lean2rr (`bugNN-name.lean`)
where the bug needs lean2rr's output, or a small generator (`bugNN-name.py`)
where the program must be large. Each file starts with what it shows, the
expected output and what Reussir ef922049 does.

    docs/reussir-bugs/run.sh RRC_CHECKOUT [BUG...]

builds each repro with `RRC_CHECKOUT/build/bin/rrc`, runs it and prints one
line per repro: `REPRODUCES` (the bad behaviour below), `FIXED` (the
expected output) or `OTHER`, with what it saw and the rrc flags. The `.lean`
repros need Lean 4.33 and a lean2rr build; see the script's header.

A plain repro is built with

    rrc bugNN-name.rr -o bugNN --emit executable FLAGS \
        --polyffi-rust-path RUSTC --polyffi-libdir RT --polyffi-libdir RT/deps \
        --polyffi-libdir $(RUSTC --print target-libdir)

where RT is the checkout's `build/target-rt/release` and RUSTC the rustc
that built it (the polymorphic-FFI directories, as `scripts/l2r.py` passes
them). The sections below show only `rrc FILE FLAGS`. "lean2rr's flags" are
`-O aggressive --no-pack-record-members --reuse-across-call`.

Builds used to check the repros (on the aarch64 test machine):

- ef922049, unpatched (`./reussir`): every repro shows its bug.
- ef922049 + 0006, 0004, 0002, 0007, 0009, 0005 as they were in the second
  review round ("round-2 stack").
- ef922049 + 0007, 0009, 0005 as revised after that review ("revised
  0007/0009").
- the round-2 stack + 0013, first version ("0013, first version").
- ef922049 + 0006, 0004, 0002, the revised 0007/0009, 0005 + 0013 as
  extended for chains through a member that is not last, work in progress
  ("0013, extended").
- ef922049 + 0012.
- the final set: ef922049 + 0006, 0004, 0002, 0007, 0009, 0005, 0013,
  0012 as applied to `./reussir` (`l2r-local`). The third review round
  checked it.

## Status

| Bug | Effect | Affects lean2rr output? | lean2rr workaround | Local patch | Patch review | Applied to `./reussir` |
|---|---|---|---|---|---|---|
| 1 | `[value]` enum payload bytes lost when a variant is moved | no, shape avoided | emits only unaffected `[value]` enums | none | - | - |
| 2 | in-place reuse skips the store of a field that sits elsewhere in the new cell | structures: yes, wrong values; variants: no | variants: `--no-pack-record-members` and fields ordered by alignment; structures: none | 0002 (structures) | passed | yes |
| 3 | Rust allocations take mimalloc's aligned path | speed only | runtime calls `mi_malloc` itself | none | - | - |
| 4 | rrc recurses forever on two equal recursive types (SIGSEGV) | yes, rrc crash | driver retries without `--reuse-across-call` | 0004 | passed | yes |
| 5 | TokenReuse crashes on a one-armed `if` (SIGSEGV) | yes, rrc crash | prelude panics avoid the shape; user code can still hit it | 0005 | passed | yes |
| 6 | a static cell is freed after 2^32 references | yes, crash | none | 0006 | passed | yes |
| 7 | token reuse picks decrements that never free | yes, speed | fields bound lazily (plan §5.5) | 0007 | passed (revised after round 2) | yes |
| 8 | padding "lift" gives LLVM a larger layout than Reussir's | no, shape never emitted | - | none | - | - |
| 9 | a member used twice loses a reference (use after free) | yes, through Reussir's inliner | none | 0009 | passed (revised after round 2) | yes |
| 10 | closure devirtualization prints types exponentially (build time) | yes, build time and memory | `--no-closure-wpd` | none | - | - |
| 11 | interprocedural SCCP is superlinear (build time) | yes, build time of large programs | none | none | - | - |
| 12 | the parser swaps syntax subtrees whose hashes collide | yes, wrong code or bogus errors on very large files | none | 0012 | passed | yes |
| 13 | releasing a long list recurses once per cell | yes, stack overflow, 2x time and memory | none | 0013 | passed (extended after round 2) | yes |
| 14 | a member consumed before the release loses a reference (use after free) | yes, through Reussir's inliner | none | in 0009 | passed | yes |
| 15 | a `match` on a `Nullable` yielding a counted value does not compile | no, `Nullable` not used | - | none | - | - |
| 16 | reuse across calls is superlinear in match nesting (build time) | yes, build time and memory | deep tail paths outlined, except in recursive functions | none | - | - |
| 17 | rrc memory is quadratic in a straight-line `Nat` function (build time) | yes, build memory | long tail paths outlined, except in recursive functions | none | - | - |
| 18 | the `rrc` build target alone does not link | no, Reussir's build only | build the default target | none | - | - |
| 19 | a `Cell` of a `[value]` record with counted members does not compile | yes, compile error | `Nat`/`Int` references in two cells; other `[value]` records boxed | none | - | - |

Patch files (`git format-patch` output; they apply on ef922049 in the
order 0006, 0004, 0002, 0007, 0009, 0005, 0013, 0012, and 0012 also applies
alone):

- `0002-l2r-local-bug-2-compound-skip-a-reused-struct-cell-s-field-store.patch`
- `0004-l2r-local-bug-4-compare-recursive-record-types-coind.patch`
- `0005-l2r-local-bug-5-free-tokens-on-the-else-path-of-an-s.patch`
- `0006-l2r-local-bug-6-never-free-a-tagged-immediate-whose-wrapped-count.patch`
- `0007-l2r-local-bug-7-sink-bound-retains-into-the-branch-t.patch`
- `0009-l2r-local-bug-9-fuse-an-arm-s-retains-only-when-the-.patch`
- `0012-l2r-local-bug-12-build-syntax-nodes-without-cstree-s-hash-only-node-cache.patch`
- `0013-l2r-local-bug-13-release-chains-of-cells-in-a-loop-in-the-drop-glue.patch`

Status words used below:
- *worked around*: no patch; lean2rr avoids the construct or works around
  it.
- *patched locally*: a local patch fixes it; it is applied to `./reussir`
  (branch `l2r-local`).
- *does not affect lean2rr*: lean2rr never produces the triggering shape.
- *open*: lean2rr can hit it and has no fix or workaround.

## 1. `[value]` enum payloads lost in the LLVM lowering

**Status.** Worked around.

**Repro.** `bug01-value-enum-payload.rr`:

```
enum [value] M { A(u8), B(bool) }
#[ffi(import)]
fn say(x : u8) [{ println!("{}", x) }];
#[main]
fn main() {
    let m = M::A{42};
    match m { M::A(x) => { say(x) }, M::B(v) => { say(7) } }
}
```

**Command.** `rrc bug01-value-enum-payload.rr -O default`, then run it.

**Expected.** `42`.

**Actual on ef922049.** `0`, at every optimization level: only bit 0 of 42
survives (43 gives 1). With a nested `[value]` enum on the padding, a
pointer can lose its upper bytes (SIGSEGV).

**Cause.** A `[value]` enum is lowered to the LLVM struct `{ tag,
<representative arm> }`. The representative arm is the last arm with the
largest alignment (`lib/IR/ReussirTypes.cpp`, used by
`lib/Conversion/TypeConverter/TypeConverter.cpp`); here `B`, whose payload
is `{ i1 }`. The whole variant is moved as a first-class aggregate of that
type: by the `record.variant` lowering (store into an alloca, then load the
whole struct, `lib/Conversion/BasicOpsLowering/BasicOpsLowering.cpp`), by
passing arguments by value, and by `ref.spilled`. Bytes of another arm that
fall on the representative's padding or on an `i1` field do not survive
the move.

**lean2rr.** Emits only `[value]` enums that are unaffected: enumerations
without fields, and `Nat`/`Int`, whose arms each hold one 64-bit word.
Other multi-arm types are shared enums, and multi-field value records are
`[value]` structs, whose padding is explicit (plan §10).

**Patch.** None.

## 2. In-place reuse skips stores of fields that sit elsewhere in the new record

**Status.** Structures: patched locally (0002). Variants: worked around.

When a unique cell is reused for a new record, RcCreateFusion's copy
avoidance skips the store of field i if its value is a load of field i of
the old record, assuming the bytes are already in place
(`lib/Transformation/RcCreateFusion/RcCreateFusion.cpp`). Two cases get the
offset wrong.

**Repro (structures).** `bug02a-struct-reuse.rr`:

```
struct A(u64, u32)
struct B(u32, u32, u64)
#[ffi(import)]
fn say(x : u64) [{ println!("{}", x) }];
#[ffi(import)]
fn five() -> u32 [{ 5 }];
fn f(a : A) -> B { B{7, a.1, 9} }
fn g(b : B) -> u64 { (b.0 as u64) * 1000000 + (b.1 as u64) * 1000 + b.2 }
#[main]
fn main() { say(g(f(A{123, five()}))); }
```

**Command.** `rrc bug02a-struct-reuse.rr -O aggressive --no-pack-record-members`.

**Expected.** `7005009`.

**Actual on ef922049.** `7000009`, at every -O level, with and without
`--reuse-across-call` and `--no-pack-record-members`. The store of `B.1`
(offset 4) is skipped because its value is a load of `A.1` (offset 8), so
`B.1` reads the high half of `A.0`.

**Cause (structures).** `markCompoundAvoidedCopies` /
`isLoadFromCompoundField` compare only the field index, not the two record
types. Token reuse hands a cell of one structure type to another of the
same size and alignment, so field i can sit at another offset, under any
layout. In Lean terms, with lean2rr's field order:

```
structure P where a : UInt64; b : UInt64; c : UInt32
structure Q where a : UInt64; b : UInt32; c : UInt32; d : UInt32; e : UInt32
@[noinline] def conv (p : P) : Q := { a := p.a + 1, b := 2, c := p.c, d := 3, e := 4 }
```

Both records are 24 bytes; `c` is at offset 16 in `P` and at offset 12 in
`Q`, and `q.c` reads the high half of `p.b`.

**Repro (variants).** `bug02b-variant-packed-layout.rr`:

```
enum M { A(u32, u64), B(u32, u32, u32) }
#[ffi(import)]
fn say(x : u64) [{ println!("{}", x) }];
fn f(m : M) -> u64 {
    match m {
        M::A(c, x) => { f(M::B{c, 1, 0}) },
        M::B(c, d, e) => { (c as u64) * 1000 + (d as u64) }
    }
}
#[main]
fn main() { say(f(M::A{5, 11})); }
```

**Command.** `rrc bug02b-variant-packed-layout.rr -O aggressive`.

**Expected.** `5001`.

**Actual on ef922049.** `11001` (`B.c` reads the low half of `A.x`), at
every -O level. With `--no-pack-record-members`: `5001`.

**Cause (variants).** `markVariantAvoidedCopies` → `isLoadFromVariantField`
→ `hasCompatibleFieldPrefix` skip the store if the member types agree for
indices 0..i in declaration order. The packed layout, the default, sorts
members by alignment, so a member's offset depends on all the members: `A.c`
is at offset 8 and `B.c` at 0. The same check uses `structurallySameType`
(bug 4), which also ignored a record's capability: a `[value]` member is
stored inline and a shared one as a pointer, so two arms could compare
equal while their layouts differ (the bug 4 patch compares capability and
`fixed` too).

**lean2rr.** `scripts/l2r.py` passes `--no-pack-record-members`, and
lean2rr orders each constructor's fields by decreasing alignment itself
(plan §5.1), so its records have no padding and the same member types at
indices 0..i put member i at the same offset. The structure case cannot be
avoided that way.

**Patch.** 0002, structures only (passed review): a structure's field store
is skipped only when the old and new cells have the same type. On the
round-2 stack: `bug02a` FIXED (`7005009`), `bug02b` still `11001` with the
packed layout (not covered; lean2rr's flag avoids it).

## 3. Rust allocations through Reussir's global allocator are 16-aligned

**Status.** Worked around (in the runtime).

**Repro.** `bug03-global-alloc-align.rr`: a Rust texture that keeps 1000
`Box<u64>` and 1000 `mi_malloc(8)` blocks alive and counts the 16-aligned
ones, then times allocate/free pairs of 16 bytes through `Box::new` and
through `mi_malloc` (best of 5 rounds of 20 million).

**Command.** `rrc bug03-global-alloc-align.rr -O aggressive`.

**Expected** (an allocator that keeps Rust's requested alignment): about
half of the boxes 16-aligned, like the `mi_malloc(8)` blocks.

**Actual on ef922049.**

    Box<u64> 16-aligned: 1000 of 1000; mi_malloc(8) 16-aligned: 500 of 1000
    alloc/free pairs: Box::new 0.179 s, mi_malloc 0.145 s, ratio 1.24

The pairs took 6-33% longer through `Box::new` over five runs on the
loaded test machine; allocating batches of 1000 and then freeing them
showed no clear difference.

**Cause.** `crates/reussir-rt/src/alloc.rs`: `ReussirGlobalAlloc` raises
every request to `GLOBAL_MAX_ALIGN = 16` (`max_align_t`, on purpose: other
code sharing the heap may assume it). Reussir builds mimalloc with
`MI_MAX_ALIGN_SIZE=8`, so every Rust `Box`/`Vec` allocation goes to
`mi_malloc_aligned`, and later frees in pages holding aligned blocks take
mimalloc's generic path.

**lean2rr.** The runtime (`runtime/leanrt/src/alloc.rs`) allocates its own
objects (strings, arrays, big numbers) with `mi_malloc`/`mi_realloc`.

**Patch.** None.

## 4. `structurallySameType` recurses forever on equal recursive types

**Status.** Patched locally (0004).

**Repro.** `bug04-recursive-type-compare.rr`:

```
enum L1 { Cons(u64, L1), Nil }
enum L2 { Cons(u64, L2), Nil }
enum [value] V { C(u64, L1), N }
enum [value] W { C(u64, L2), N }
enum S1 { A(V, u64), Z }
enum S2 { A(W, u64), Z }
...
fn conv(s : S1) -> S2 {
    match s { S1::A(c, v) => { S2::A{W::N{}, v} }, S1::Z => { S2::Z{} } }
}
```

**Command.** `rrc bug04-recursive-type-compare.rr -O aggressive`.

**Expected.** Compiles; prints `1005`.

**Actual on ef922049.** rrc dies with SIGSEGV (exit 139) and no message, at
every -O level.

**Cause.** RcCreateFusion's `structurallySameType`
(`lib/Transformation/RcCreateFusion/RcCreateFusion.cpp`), called by the
variant copy avoidance of bug 2, compares two record types member by member
and recurses into member records, with no set of pairs already being
compared. `conv` reuses the `S1` cell for an `S2`, the store of `v` is a
candidate for skipping, so the arms' members before it are compared: `V`
with `W`, hence `L1` with `L2`, which never ends. The pass runs on an LLVM
worker thread, so the stack overflow is a SIGSEGV whatever `ulimit -s` says.
In lean2rr this showed up as a user `MyList` next to `List` with
`MyList.toList` reusing cons cells under `--reuse-across-call`.

**lean2rr.** `scripts/l2r.py` retries rrc without `--reuse-across-call`
when rrc dies from a signal (and says so on stderr). That turns off reuse
across calls for the whole program, and does not help when the crash
happens without the flag, as here.

**Patch.** 0004 (passed review): the comparison keeps a set of type pairs
under comparison and treats a pair seen again as equal (coinductive
equality). It also requires the same capability and `fixed` flag: without
that, closing the cycle turned the crash into a silent miscompile when a
`[value]` record met a shared record of the same shape. On the round-2
stack: FIXED (`1005`).

## 5. TokenReusePass crashes on a one-armed `if`

**Status.** Patched locally (0005).

**Repro.** `bug05-one-armed-if.rr`:

```
enum T { N(u64, T, T), L }
fn f(x : T, y : T) -> T {
    match x {
        T::N(a, l, r) => {
            T::N { 0, match y { T::N(a2, l2, r2) => { if a2 == 0 { l } else { l2 } }, T::L => T::L{} }, l }
        },
        T::L => T::L{}
    }
}
```

(plus a `main` that calls `f` and prints the size of the result).

**Command.** `rrc bug05-one-armed-if.rr -O aggressive`.

**Expected.** Compiles; prints `3`.

**Actual on ef922049.** rrc dies with SIGSEGV (exit 139), at every -O
level, with or without `--reuse-across-call`.

**Cause.** `lib/Transformation/TokenReuse/TokenReuse.cpp`,
`TokenReusePass::oneShotTokenReuse`: a token available before a branch op
and consumed in one of its regions is freed at the end of every other
region, at `getRegion(i).front().getTerminator()`. After canonicalization
an `if` without an else has an empty else region, `front()` of it is a
dangling block, and `ReussirTokenFreeOp::create` crashes when the frees are
materialized. The first lean2rr case was the prelude's panic path, which
needed `--reuse-across-call` (without it the calls before the `if` flush
every token).

**lean2rr.** Runtime panics reach `l2r_stderr_put` through an `extern "C"`
trampoline called from Rust (§5.12), which removes the shape from the
prelude. User code can still produce it (a nested match inside a
constructor argument, with an `if` choosing between fields), at every -O
level, so the driver's retry does not help.

**Patch.** 0005 (passed review): TokenReuse creates the missing else block
(just a yield) and frees the token there. On the round-2 stack: FIXED
(`3`).

## 6. Static cells accumulate increments until the 32-bit count wraps

**Status.** Patched locally (0006).

**Repro.** `bug06-static-count-wrap.rr`:

```
enum L { Nil, Cons(u64, L) }
fn len(l : L) -> u64 {
    match l { L::Nil => { 0 }, L::Cons(x, t) => { 1 + len(t) } }
}
fn loop_(x : L, n : u64, acc : u64) -> u64 {
    if n == 0 { acc } else { loop_(x, n - 1, acc + len(x)) }
}
...
fn main() { say(loop_(L::Cons{1, L::Nil{}}, count(), 0)); }
```

where `count()` is the first argument. In Lean:

```
@[noinline] def len (l : List Nat) : Nat := l.length
def loop (x : List Nat) : Nat → Nat → Nat
  | 0, acc => acc
  | n+1, acc => loop x n (acc + len x)
def main (args : List String) : IO Unit :=
  IO.println (loop [args.length] 4294967300 0)
```

**Command.** `rrc bug06-static-count-wrap.rr` with lean2rr's flags, then
`./bug06 4294967300`.

**Expected.** `4294967300`.

**Actual on ef922049.** SIGSEGV (exit 139) after about 15 s. With
`4294967290` it prints `4294967290`.

**Cause.** Static (immortal) cells, such as the static `Nil`, are tagged in
the pointer's top byte. `ReussirRcIncConversionPattern`
(`lib/Conversion/BasicOpsLowering/BasicOpsLowering.cpp`) increments the
32-bit count unconditionally (`load; add 1; store`). The decrement skips
static pointers but tests "count == 1 → free" first. After 2^32 references
the count wraps to 1 and the next decrement frees the static cell
(`mi_free` on a tagged pointer). Also `assume(old >= 1)` after an increment
becomes false when the count passes 0.

**lean2rr.** Nothing it can do.

**Patch.** 0006 (passed review). The increment stays a plain load, add and
store, so LLVM can still fold counts on fresh cells. The decrement's unique
branch (count == 1) first checks whether the value is one of its type's
nullary immediates; if it is, the decrement frees nothing and yields no
token, so a wrapped count can never free or reuse the static cell. The
`assume(old >= 1)` becomes `old >= 1 || top byte != 0`. This costs about 4%
on rbtree and nothing measurable elsewhere, on both core types of the test
machine (guarding the increment's store instead cost up to 22% on the
Cortex-A725 cores). On the round-2 stack: FIXED (`4294967300`, 14 s).

## 7. Token reuse picks decrements that can never free

**Status.** Patched locally (0007); lean2rr also works around it.

**Repro.** `bug07-phantom-reuse-donor.rr`:

```
enum Tr { Leaf, Node(Tr, u64, Tr) }
fn ins(t : Tr, k : u64) -> Tr {
    match t {
        Tr::Leaf => { Tr::Node{Tr::Leaf{}, k, Tr::Leaf{}} },
        Tr::Node(l, x, r) => {
            if k < x { Tr::Node{ins(l, k), x, r} }
            else { if x < k { Tr::Node{l, x, ins(r, k)} } else { t } }
        }
    }
}
```

and `ins_b`, the same except that the equal-key arm returns
`Tr::Node{l, x, r}`. The program builds a 100,003-key tree with each, then
inserts 3,000,000 keys that are all present, and prints both sizes and the
time ratio `t(ins) / t(ins_b)`.

**Command.** `rrc bug07-phantom-reuse-donor.rr` with lean2rr's flags.

**Expected.** `100003 100003 ratio` near 1: both inserts reuse the cells
on the path.

**Actual on ef922049.** `100003 100003 ratio 6.12` (5.8-7.9 over runs):
`ins` allocates a new node at every level of every insertion.

**Cause.** In `ins`, `t` stays live on the equal-key path, so Reussir
projects `l` and `r` before the branch and retains them. On the other paths
they are released again. Those releases are expanded as "if rc == 1 then
drop and keep the token", but their counts are at least 2 (`t` still holds
them), so they never free anything. TokenReuse scores them the same as the
real donor, `t`'s own cell, and takes the most recent one. The construction
then finds a null token and allocates, and `t`'s cell is freed.
`RcDispatchFusion`'s `fuseArm`
(`lib/Transformation/RcDispatchFusion/RcDispatchFusion.cpp`), which would
turn the retains into a destructuring release of `t`, stops at the first
region op. A decrement of a nullary constructor (an immediate) is the same
kind of phantom donor.

**lean2rr.** A value stored whole in a constructor, a value returned whole
(an insert that returns the node for an equal key), and a structure stored
or returned whole have their fields bound only where they are used (plan
§5.5). The matched value's fields are then not
retained while it stays live, so there is no phantom donor. With this, the
Std.TreeMap insert is as fast as native Lean, and BST inserts with `Nat` or
`String` keys whose equal arm returns the node run at or below native time,
even on ef922049. An earlier workaround returned the constructor rebuilt
from the arm's fields instead of the matched value; it broke `ptrEq`
identity and sharing (Lean's `Expr.replace`-style fixpoints never stopped)
and was removed.

**Patch.** 0007 (passed review; revised after round 2). When the release
of the scrutinee sits inside a branch that runs exactly one of its regions
once (`if` with an else, `index_switch`, record or nullable dispatch), the
arm's retains of the bound members move into every region of that branch.
Paths that release the scrutinee then get the usual destructuring
decrement; paths that release a member get an adjacent retain and release,
which cancel. The move is allowed only if nothing between the old and new
positions releases a value, calls a function or has a region. The review
found a use after free: the fusion inside a region must stop at a use that
consumes a bound member (as for bug 14); the revision does that.

Measured: the BST above allocates exactly like the rebuilt version (0.74 s
→ 0.16 s); a TreeMap-shaped insert without lean2rr's workaround drops from
12.35 to 1.33 allocations per insertion. On the round-2 stack the repro
prints a ratio of 0.86-1.36, with the revised 0007/0009 0.95-1.13: FIXED.

Not patched: the remaining 0.33 extra allocations per insertion come from
decrements of values that may be nullary immediates. They still count as
exact-size donors and can win the most-recent tie-break. Ranking a matched
cell above such donors fixed it in a trial (rbtree 1.48 → 0.98 s) but cost
monadic-interp 1.7%, so it was left out. The patch also stops at calls
before the branch, such as a `Nat` comparison; lean2rr binds such a value's
fields where they are used instead (plan §5.5).

## 8. A padding "lift" breaks declaration-order layouts

**Status.** Does not affect lean2rr.

**Repro.** `bug08-padding-lift.rr`:

```
struct [value] S3(u8, u8, u8)
struct [value] Q(S3, u16)
struct R(Q, Q, Q, Q, Q, Q, u16)
enum L { Nil, Cons(R, L) }
...
fn build(n : u64, acc : L) -> L { if n == 0 { acc } else { build(n - 1, L::Cons{R{mkq(n), ..., (n % 50000) as u16}, acc}) } }
fn sum(l : L, acc : u64) -> u64 { match l { L::Nil => { acc }, L::Cons(r, t) => { sum(t, acc + (r.6 as u64) + (r.5.1 as u64) + (r.0.0.2 as u64)) } } }
#[main]
fn main() { say(sum(build(100000, L::Nil{}), 0)); }
```

**Command.** `rrc bug08-padding-lift.rr -O aggressive --no-pack-record-members`.

**Expected.** `2550200000`.

**Actual on ef922049.** SIGSEGV (a heap overflow). With the default
(packed) layout it prints `2550200000`.

**Cause.** `lib/Conversion/TypeConverter/TypeConverter.cpp`,
`convertRecordType`: under `--no-pack-record-members`, a member followed by
padding is widened to an integer that covers the padding, without checking
that this integer is no more aligned than the next member. Reussir's layout
of `Q` is 6 bytes with alignment 2; its LLVM type `{ i32, i16 }` is 8 bytes
with alignment 4. Reussir allocates `R` as 38 bytes, LLVM's `R` is 52, so
every list cell is written past its end. Reussir's and LLVM's field
offsets also disagree: when a cell of `struct R1(Q, u16)` is reused for
`struct R2(S6, u16)` (`S6` = three `u16`) and the store of the `u16` is
skipped (bug 2), `R2.1` reads the wrong bytes (`300000` instead of
`305000`; with 0002 the store is no longer skipped there). The packed
layout sorts members by alignment and never needs the lift.

**lean2rr.** Never produces this shape: its records have no padding
between members (fields in decreasing alignment), and its `[value]`
structs have a single field whose size is a power of two.

**Patch.** None.

## 9. Duplicate bound members lose a reference in `RcDispatchFusion`

**Status.** Patched locally (0009).

**Repro.** `bug09-duplicate-bound-member.rr`:

```
fn f(x : T) -> T {
    match x {
        T::N(a, l, r) => { let y : T = { let z : T = T::N { a, l, r }; x }; T::N { a, r, l } },
        T::L => x
    }
}
```

`go` runs `f` on 1000 fresh trees and prints how many checksums are wrong.
The shape usually appears after Reussir inlines a callee that drops the
scrutinee:

```
fn second(t : T, y : T) -> T { y }
fn f(x : T) -> T { match x { T::N(a, l, r) => second(x, T::N { a, l, l }), T::L => x } }
```

**Command.** `rrc bug09-duplicate-bound-member.rr` with lean2rr's flags.

**Expected.** `0`.

**Actual on ef922049.** SIGSEGV, at every -O level. (A single call of `f`
prints a wrong checksum in about half of the runs: `882` instead of `2432`
at -O aggressive, garbage at -O none; ASan reports a heap use after free.)

**Cause.** `lib/Transformation/RcDispatchFusion/RcDispatchFusion.cpp`,
`fuseArm`, collects every retain of a member extracted from the scrutinee
without checking for duplicates. `l` and `r` are used twice while `x` is
still live, so `boundMembers` is `[1, 2, 1, 2]`. The unique path of
`RcDecrementExpansion` treats the list as a set and transfers one reference
per member, so each duplicate loses a count and the member is freed while
still referenced.

**lean2rr.** Lean's compiler removes the obvious forms, but Reussir's
inlining at `-O aggressive` can recreate them, and lean2rr cannot prevent
that.

**Patch.** 0009 (passed review; revised after round 2): `fuseArm` binds
each member once and erases only its first retain; further retains of the
same member are real copies and stay, as in `fuseCompoundConsumption`. The
revision also covers bug 14. FIXED (`0`) on the round-2 stack and with the
revised 0007/0009.

## 10. Closure devirtualization prints result types exponentially

**Status.** Worked around (build time only).

**Repro.** `bug10-closure-type-print.py K OUT.rr` writes a program with
`D0 = struct(u64)` and `D(i) = struct(D(i-1), D(i-1))`, and twenty closures
of type `u64 -> D(K)` chosen at run time, so their calls stay indirect.
`D(K)` printed with every named record expanded has 2^K copies of `D0`. The
program prints `780`.

**Command.** `rrc OUT.rr -O aggressive`, and the same with
`--no-closure-wpd`.

**Expected.** Build time about the same with and without closure
devirtualization, and growing linearly with K.

**Actual on ef922049** (rrc build time and peak memory, this machine):

| K | `-O aggressive` | with `--no-closure-wpd` |
|---|---|---|
| 16 | 1.2 s | 0.5 s |
| 18 | 3.8-8.4 s | 0.5-1.3 s |
| 20 | 24 s, 250 MB | 0.7-0.8 s |
| 22 | 89 s, 730 MB | 0.7 s |

Sizes that hit the limits (lean2rr outputs before the workaround, rrc to an
object file, 16 GB limit): a polymorphic recursion through a `StateT` tower
(`Cn3PolyS1`, 1291 functions) took 313 s and 8.1 GB (39 s and 0.8 GB with
`--no-closure-wpd`); two others (`Cn3PolyWhere`, `Cn3PolyMut`) ran out of
memory after 184 s and 225 s.

**Cause.** With `-O aggressive`, rrc devirtualizes closures. It computes a
type id for each closure result type by printing the type to a string and
hashing it (`closureWpdTypeId`, `include/Reussir/Conversion/ClosureWpd.h`),
uncached, at every indirect call, clone or drop site
(`emitClosureWpdTest`) and every vtable (`stampClosureWpdTypeIds`, both in
`lib/Conversion/BasicOpsLowering/BasicOpsLowering.cpp`).
`RecordType::print` (`lib/IR/ReussirTypes.cpp`) expands named records
inline and stops only at a record already on its print stack, so a record
reached k ways is printed k times. lean2rr's function and `Box` types nest
deeply in polymorphic recursion, so the text grows exponentially.

**lean2rr.** The driver passes `--no-closure-wpd`. The classic benchmarks
measured the same with and without it, within noise (lean2rr dispatches
its function values itself).

**Patch.** None.

## 11. Interprocedural SCCP is superlinear on large call graphs

**Status.** Open (build time only).

**Repro.** `bug11-sccp-call-graph.py N OUT.rr` writes N self-recursive
functions (so they are not inlined) that each call the same function `g`,
and a function that calls all N. It prints one number.

**Command.** `rrc OUT.rr -O aggressive`.

**Expected.** Build time about linear in N.

**Actual on ef922049** (rrc build time, several runs on the loaded test
machine; a build of N = 10 takes 0.3 s):

| N | build |
|---|---|
| 1000 | 1.6-2.4 s |
| 2000 | 3.4-6.5 s |
| 4000 | 10-31 s |

In every run N = 4000 took 2.9-4.8 times as long as N = 2000.

perf puts the time in MLIR's data-flow solver
(`DeadCodeAnalysis::visitCallableTerminator`,
`AbstractSparseForwardDataFlowAnalysis::visitCallableOperation`, and the
lookups of analysis states).

Sizes that hit the limits (lean2rr outputs, with `--no-closure-wpd`): five
transformer towers in one program (`Cn3PolyM1`, 2140 functions) build in
936 s and 7.5 GB and give the right output. A single growing `StateT` tower
used at `IO` (8 lines of Lean) does not build within 30 minutes or 12-15
GB; the same tower at `Id` builds in 60 s.

**Cause.** `mlir::createSCCPPass` runs on the whole module twice
(`crates/reussir-backend/src/pipeline.rs`, through `reussirCreateSCCPPass`
in `lib/CAPI/Passes.cpp`). It is interprocedural: every change of a
callable's argument or return lattice re-visits the callable's terminators
and all of its call sites. lean2rr's uniform code for polymorphic
recursion has large, heavily shared callees (the conversion and
application functions of its function and `Box` representations).

**lean2rr.** Nothing yet. Sharing one representation per uniform function
type would shrink the number of such callees.

**Patch.** None.

## 12. The parser's node cache swaps subtrees whose hashes collide

**Status.** Patched locally (0012).

**Repro.** `bug12-node-cache-collision.py OUT.rr` writes a 1.9 MB program
(about 187,000 comment lines that only move the parser's interner keys,
then four small functions):

```
fn first(vvvvvv: u64) -> u64 { get(T::One{vvvvvv}) }
...
fn second(vvvvvv: u64) -> u64 { get(T::One{424242}) }
...
fn main() { say(second(7)); }
```

**Command.** `rrc OUT.rr -O aggressive`.

**Expected.** `424242`.

**Actual on ef922049.** `7`, with no diagnostic, at every -O level:
`second`'s argument `T::One{424242}` is parsed as `T::One{vvvvvv}`.

**Cause.** Reussir builds its syntax tree with the `cstree` 0.14 library
(`crates/reussir-syntax/src/parser/sink.rs`, `Sink::finish`, through
`GreenNodeBuilder`). The builder's node cache (`NodeCache::node` in
cstree's `src/green/builder.rs`) reuses an earlier node for any node of at
most three children with the same kind, the same text length and the same
32-bit hash of its children, without comparing the children. A node whose
hash collides gets the earlier node's whole subtree. Token texts enter the
hash through their interner keys, handed out in order of first occurrence,
so whether two nodes collide depends on the whole file. Expect about one
collision per very large file.

In lean2rr output this showed up as rrc errors that seemed to make no
sense:
- `unknown variable x78617` on a 60,000-element list literal, reported at
  an integer literal whose node had collided with a node holding a variable
  of a function 114,000 lines earlier (changing the literal to one that
  occurs earlier in the file made it pass);
- earlier adversarial findings: a call swapped for another function's
  call, and a match pattern swapped for another variant (a type mismatch).

A swapped subtree that contains a local name almost always fails to
compile, since lean2rr's local names are unique. Subtrees made only of
global names and literals (zero-argument calls, patterns without binders,
calls with literal arguments) can be swapped silently whenever their types
agree.

**lean2rr.** Cannot avoid it: any shape, name or literal can collide.

**Patch.** 0012 (passed review): the parser builds every node without
the cache; tokens still come from the builder, whose token cache compares
whole tokens. It costs 7-18% more parse memory (a 101 MB file: 2.1 → 2.5
GB) and no change in rrc's peak memory on full builds. With 0012: FIXED
(`424242`).

## 13. Drop glue recurses once per cell of a long list

**Status.** Patched locally (0013).

Releasing a chain of cells at once takes one stack frame per cell. Native
Lean frees iteratively. The program needs no recursion of its own:

```
def main (args : List String) : IO Unit := do
  let l := List.replicate 40000000 7
  IO.println s!"{l.head?}"
```

**Repro.** Two files.

- `bug13-long-list-drop.rr SHAPE N` (plain Reussir, `main` on the 8 MB
  main thread) builds a chain of N cells, reads one field and drops the
  chain:
  - SHAPE 0, a list whose recursive field is last: `Cons(u64, L)` (Lean's
    `List`);
  - SHAPE 1, a snoc list whose recursive field is first and a box is last:
    `S(Snoc, Box)`;
  - SHAPE 2, a left spine: `N(u64, T, T)` with the chain in the first `T`.
- `bug13-long-list-drop.lean CASE N` (through lean2rr, whose `main` runs on
  a thread with a 1 GiB stack): CASE 0 is `List.replicate N 7`, CASE 1 a
  snoc list `SnocS.snoc : SnocS → String → SnocS`.

**Command.** `rrc bug13-long-list-drop.rr` with lean2rr's flags, then
`./bug13 0 1000000`; `scripts/l2r.py` on the Lean file, then `./prog 0
40000000`.

**Expected.** The plain repro prints N; the Lean repro prints `(some 7)`
(CASE 0) or `0` (CASE 1), like native Lean.

**Actual on ef922049.**

- Plain, 8 MB stack: `thread 'main' has overflowed its stack`, `fatal
  runtime error: stack overflow, aborting` (SIGABRT). A list (SHAPE 0)
  takes 16 bytes of stack per cell and overflows above about 524,000
  cells; the snoc list and the left spine take 32 bytes per cell and
  overflow above about 261,000 cells.
- lean2rr, 1 GiB stack: `Stack overflow detected. Aborting.` (exit 134;
  the line printed before is lost). Both cases take 32 bytes per cell:
  33,437,500 cells work, 33,906,250 abort.
- At 10 million elements (lean2rr, best of 5, max RSS):

  | | `List.replicate` | snoc list |
  |---|---|---|
  | native Lean | 0.08 s, 313 MiB | 0.08 s, 313 MiB |
  | ef922049 | 0.18 s, 617 MiB | 0.17 s, 541 MiB |
  | 0013, first version | 0.08 s, 312 MiB | 0.16 s, 541 MiB |
  | 0013, extended | 0.06 s, 312 MiB | 0.07 s, 236 MiB |

  The extra 300 MiB on ef922049 is the stack: 10 million frames of 32
  bytes stay resident.

**Cause.** The drop function of a cell (`drop_in_place`, outlined by
`lib/Conversion/AcquireDropExpansion/AcquireDropExpansion.cpp`) releases
the cell's members, and the release of an rc member expands
(`RcDecrementExpansion`) to "count == 1 → call the member's drop function,
take the cell as a token"; the token is freed after that call. So the free
of each cell follows the recursive call on its tail: not a tail call.

**lean2rr.** Cannot avoid releasing such values.

**Patch.** 0013 (passed review; extended after round 2).

The first version, reviewed in round 2: inside drop functions, a release
whose count is 1 calls a new `drop_and_free::<T>`, which drops the cell's
other members, frees the cell, and releases the cell's last managed member
as its last operation, a tail call that LLVM turns into a loop. Releases
outside drop functions, whose cells may be reused, are unchanged. It covers
chains through the last managed member: Lean's `List`, a list whose head
is a `Nat` holding a box, mutual recursion through two types, a right
spine. A tree still recurses along its other children. With it,
`List.replicate 40000000` takes 0.25 s (native 0.37 s) with native memory.
It does not cover the snoc list or the left spine: SHAPE 1 and 2 and CASE 1
still overflow. At `-O none` LLVM does not turn the tail call into a loop,
so every chain still overflows there.

The extension, which the patch file holds and the third review round
checked: `drop_and_free` releases the cell's chain members (the plain shared
boxes whose type can contain the cell's type again) wherever they sit in
the cell; of those about to be freed, the last is released as the tail
call. So the loop follows whichever member carries the chain. A build of
it passes all three plain shapes at 1M cells and both Lean cases at 40M.

## 14. `fuseArm` loses a count when a bound member is consumed before the scrutinee's release

**Status.** Patched locally (in the revised 0009).

**Repro.** `bug14-member-consumed-before-release.rr`:

```
fn f(x : T) -> T {
    match x {
        T::N(a, l, r) => { let y : T = { let z : T = T::N { a, l, T::L{} }; x }; T::L{} },
        T::L => x
    }
}
```

`go` builds a tree `t`, calls `f(t)` and then reads `t` (so `x` is shared),
1000 times, and prints how many checksums are wrong.

**Command.** `rrc bug14-member-consumed-before-release.rr` with lean2rr's
flags.

**Expected.** `0`.

**Actual on ef922049.** A crash at every -O level: SIGSEGV, or SIGABRT
from a stack overflow (a freed cell forms a cycle). ASan reports a heap use
after free.

**Cause.** `RcDispatchFusion`'s `fuseArm` fuses a match arm's member
retains into the release of the scrutinee and keeps scanning past a use
that consumes a bound member: here `l` is stored in `z`, which is released
again before `x`. With `x` shared, `z`'s release drops `l`'s count below
its holders; the fused decrement's shared path then reloads `l` from `x`'s
cell and retains it.

**lean2rr.** Can reach the shape through Reussir's inliner (a callee that
drops a constructed argument); not seen in the corpus or test suites.

**Patch.** In 0009 (passed review): no fusion when an op
before the release uses a bound member other than by a borrow or a retain.
0007 had the same flaw in its own scan, found in review, and is fixed the
same way. The round-2 stack, which has the earlier 0009, still crashes;
with the revised 0007/0009: FIXED (`0`).

## 15. A `match` on a `Nullable` whose arms yield a counted value does not compile

**Status.** Does not affect lean2rr.

**Repro.** `bug15-nullable-match-yield.rr`:

```
struct [shared] B { v: u64 }
enum T { N(u64, T, T), L }
fn g(nb : Nullable<B>, x : T) -> T {
    match nb {
        Nullable::NonNull(b) => { x },
        Nullable::Null => { T::L{} }
    }
}
```

**Command.** `rrc bug15-nullable-match-yield.rr -O aggressive`.

**Expected.** Compiles; prints `1`.

**Actual on ef922049.**

    error: 'reussir.scf.yield' op parent operation expected a value, but nothing is yielded
    error: lowering pipeline failed: RunPass

**Cause.** Not investigated (the match is lowered to
`reussir.nullable.dispatch` in `crates/reussir-codegen/src/lower/expr.rs`,
`nullable_switch`; the error comes from the pass pipeline).

**lean2rr.** Does not use `Nullable`.

**Patch.** None.

## 16. Reuse across calls is superlinear in the nesting depth of matches

**Status.** Worked around (build time only).

Each IO bind is a match on the action's result whose ok arm holds the rest
of the function, so a `main` of N statements nests N matches deep.

**Repro.** `bug16-nested-io-matches.py N OUT.lean` writes

```
def loop : Nat → IO Unit
  | 0 => pure ()
  | k+1 => do
    IO.println "line 0"
    ...                     -- N statements
    loop k
```

built through lean2rr. `loop` is recursive, so lean2rr's workaround below
does not cut it. It prints `line 0` to `line N-1`.

**Command.** `scripts/l2r.py` on the generated module (lean2rr's flags),
and with `--no-reuse-across-call`.

**Expected.** Build time and memory about linear in N.

**Actual on ef922049** (rrc only, this machine; times from the quieter of
two runs, up to 2x longer on a busier host, memory the same):

| N | `--reuse-across-call` | without |
|---|---|---|
| 50 | 17 s, 261 MB | 14 s, 135 MB |
| 100 | 35 s, 1.15 GB | 15 s, 158 MB |
| 150 | 99 s, 3.1 GB (whole build) | |

Sizes that hit the limits (a `main` of N statements, before lean2rr's
workaround): 250 statements took about 200 s and 12.5 GB; 500 crashed rrc,
and the driver's retry without the flag took 434 s and 14.2 GB; 2000 was
killed after 1500 s. Without `--reuse-across-call`, 250 statements built in
16 s and 221 MB. The program is correct whenever the build finishes.

**Cause.** Not narrowed down to one pass. `--reuse-across-call` lets
TokenReuse (`lib/Transformation/TokenReuse/TokenReuse.cpp`) keep tokens
alive across calls, and with it the code the lowering pipeline generates
grows quadratically with the nesting depth: the LLVM IR of the repro has
100k lines at N = 50 and 239k at N = 100 with the flag, 58k and 75k
without. The Reussir MLIR going into the pipeline is the same with and
without the flag.

**lean2rr.** A function whose tail path is 32 matches (or `if`s) deep is
cut into a chain of functions of at most 8 levels, each calling the next in
tail position (`LeanToReussir/Outline.lean`, plan §10 "Build time"). rrc
on 250 statements: 27 s, 343 MB; 2000 statements: 161 s, 1.9 GB (before:
killed after 1500 s). Recursive functions are not cut (a cycle of tail
calls through the parts is not always a loop), so a loop with such a body,
as in the repro, still builds slowly.

**Patch.** None.

## 17. rrc memory is quadratic in the length of a straight-line function on `Nat`

**Status.** Worked around (build time only).

**Repro.** `bug17-long-nat-block.py N OUT.lean [Nat|UInt64]` writes

```
def longDo (x0 : Nat) : Nat → Nat
  | 0 => x0
  | k+1 => Id.run do
    let x1 := (x0 * 3 + x0) % 1000003
    ...                     -- N lets
    return longDo xN k
```

built through lean2rr (recursive, so not cut by the workaround). It prints
the same number as native Lean.

**Command.** `scripts/l2r.py` on the generated module.

**Expected.** rrc memory about linear in N.

**Actual on ef922049** (rrc only, this machine):

| N | `Nat` |
|---|---|
| 250 | 21 s, 417 MB |
| 500 | 32 s, 1.16 GB |
| 1000 | 57 s, 4.1 GB |

The same block on `UInt64` (`bug17-long-nat-block.py 1000 OUT.lean
UInt64`): 20 s, 127 MB. Sizes that hit the limits (before lean2rr's
workaround): 2500 `let`s ran out of memory (`std::bad_alloc` at 14 GB); a
test with a 1500-`let` function needed 5.5 GB. `--reuse-across-call` is
not the cause (1000 `let`s took 4.1 GB without it too).

**Cause.** Not narrowed down. The memory is taken in rrc's MLIR lowering
pipeline: a build that stops after it (`--emit mlir-llvm`) already reaches
the peak (417 MB at N = 250, 1.19 GB at N = 500), while the IR it emits
grows linearly (301k and 565k lines). Probably a per-function analysis
over reference-counted values (`Nat` is a two-arm `[value]` enum whose
`Big` arm holds a box) keeps a set of live values per program point; with
`UInt64` there are no such values.

**lean2rr.** As for bug 16, a function with a tail path of 256 `let`s is
cut into parts of at most 64 `let`s on a path. rrc on the 1000-`let`
block: 877 MB (was 4.1 GB; the rest grows linearly, about 0.3 MB per `Nat`
operation); 2500 `let`s: 99 s, 2.0 GB (was out of memory). Recursive
functions are not cut.

**Patch.** None.

## 18. The `rrc` build target alone does not link

**Status.** Worked around (build the default target).

**Repro.** `bug18-rrc-target-deps.sh REUSSIR_CHECKOUT` checks the cause in
an existing build (read-only). The failure itself needs a fresh build
directory:

    cmake -S reussir -B build -G Ninja ...
    cmake --build build --target rrc

**Expected.** rrc builds.

**Actual on ef922049.** cargo fails to link rrc: `could not find native
static library MLIRReussirInstrumentNonlinearFFI`. The check script prints
`REPRODUCES rrc-build does not depend on
libMLIRReussirInstrumentNonlinearFFI.a, which build.rs links`.

**Cause.** `crates/reussir-backend-sys/build.rs` links
`MLIRReussirInstrumentNonlinearFFI`, but the `rrc-build` custom target
(`crates/reussir-compiler/CMakeLists.txt`) depends only on `ReussirCAPI`
and `MLIRReussir`, which do not pull that library in. The default target
builds every library first.

**lean2rr.** Build Reussir's default target.

**Patch.** None.

## 19. A `Cell` of a `[value]` record with counted members does not compile

**Status.** Worked around.

**Repro.** `bug19-cell-of-value-record.rr`:

```
struct [shared] Bg(u64)
enum [value] Nat { Small(u64), Big(Bg) }
struct RNat(Cell<Nat>)
fn mk(v : Nat) -> RNat { RNat{core::intrinsic::cell::alloc(v)} }
fn run(n : u64) -> u64 {
    let r : RNat = mk(Nat::Small{n});
    let x : Nat = core::intrinsic::cell::get(r.0);
    match x { Nat::Small(y) => y, Nat::Big(b) => b.0 }
}
```

**Command.** `rrc bug19-cell-of-value-record.rr -O aggressive`.

**Expected.** Compiles; prints `42`.

**Actual on ef922049.**

    error: 'func.call' op operand type mismatch: expected operand type
    '!reussir.ref<!reussir.record<variant "_RC3Nat" [value] {...}>>', but provided
    '!reussir.ref<!reussir.record<variant "_RC3Nat" [value] {...}> field>' for operand number 0
    error: lowering pipeline failed: RunPass

`cell::set` fails the same way. With `Big(u64)` (no counted member) the
program compiles and prints `42`.

**Cause.** `lib/Conversion/ConvertToSTD/ConvertToSTD.cpp` projects a cell's
slot with a `field`-capability reference (`getCellSlotRefType`) and emits
`ref.acquire` (get) or `ref.drop` (set) on it (`acquireThenLoadCellSlot`,
`dropThenStoreCellSlot`). For a named record type, `AcquireDropExpansion`
outlines these into the record's acquire and drop functions, whose
parameter is a `ref<T>` of unspecified capability
(`createDtorIfNotExists`, `emitOwnershipAcquisitionFuncIfNotExists`), and
calls them with the `field` reference unchanged. Cells of scalars, of
trivially copyable value records and of rc values take other paths and
work.

**lean2rr.** A reference to a `Nat` or `Int` (`ST.Ref`, `IO.Ref`) is the
prelude's `L2RNatRef`/`L2RIntRef`: a tagged word in a `Cell<u64>` and the
big number in a `Cell<L2RBigOpt>`. A reference to any other `[value]`
record keeps the element in an `ElemBox` (one allocation per `set`; such
references do not occur in practice, since lean2rr's `[value]` structs are
IO results).

**Patch.** None.

## Other observations

- **Tagged pointers from the allocator.** Under top-byte tagging, a pointer
  with a nonzero top byte is an immediate. An allocator that tags real
  pointers (memory tagging, HWASan) would make real cells look like
  immediates: their decrements are skipped (a leak). The allocator lean2rr
  uses returns untagged pointers, and the sanitizer modes use the untagged
  encoding. Not reproducible on the test machine (no MTE).
- **Finalization order.** Values are released in a different order from
  native Lean's `lean_del`. The difference is observable when releasing
  objects has effects, for example file handles that flush buffered output
  when dropped: 16 handles to one file kept in two lists print `L7 L6 ...
  L0` natively and `L0 L1 ... L7` through lean2rr (plan §10).

## Missing features that cost lean2rr performance

Not bugs, but each one costs lean2rr measurably:

- **Borrowed parameters.** Reads of arrays and strings through the runtime
  take the container owned, so each read retains and releases it.
  Traversals that keep unchanged nodes pay the same on fields (about 1.5x
  native on an `Expr.replace`-style DAG traversal).
- **A one-word `Nat`.** `Nat` is a two-word `[value]` enum (small or big).
  Natively it is one tagged word, so nodes with `Nat` fields are larger
  (`Std.TreeMap Nat Nat` uses about 1.5x native memory).
- **`[value]` types across the FFI.** Arrays of `Nat`, `Int` or enumerations
  need runtime-side representations or wrappers.
- **Guaranteed tail calls.** Mutual tail calls are sibling calls only when
  all arguments fit in registers.
