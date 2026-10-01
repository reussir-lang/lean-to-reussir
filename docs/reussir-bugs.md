# Reussir bugs that affect lean2rr

Reussir bugs found while building lean2rr, with a minimal repro, the cause
where known, what lean2rr does about it, and the status of a local patch.

Reussir revision: `ef922049`. The checkout at `./reussir` is not part of
this repository. Every Reussir bug lean2rr has run into is listed here,
including those it works around or never triggers. Reussir is patched
locally only where a bug breaks lean2rr's output and lean2rr has no
reasonable way around it. Those patches live in `reussir-patches/` (see
its README) and are applied only to local builds. They are not submitted
upstream. A local patch is reviewed adversarially (code review,
differential fuzzing against a reference evaluator, ASan builds, the
lean2rr test suites) before it is used. Patch files are added to
`reussir-patches/` once their review is complete. Until then, `./reussir`
stays unpatched and the lean2rr workarounds stay in place.

Status values:
- *worked around*: no patch; lean2rr avoids the construct or works around
  it.
- *patched locally*: a patch in `reussir-patches/`, named after the bug
  number, fixes it.
- *does not affect lean2rr*: lean2rr never produces the triggering shape.
- *open*: lean2rr can hit it and has no fix or workaround yet.

Repros of the form `rrc F.rr ...` use a plain rrc command line: `--emit
executable` plus the polymorphic-FFI directories that `scripts/l2r.py`
passes.

## 1. `[value]` enum payloads lost in the LLVM lowering

Status: worked around.

A `[value]` enum is lowered to the LLVM struct `{ tag, <representative
arm> }`. The representative arm is the last arm with the largest alignment
(`lib/IR/ReussirTypes.cpp`, used by `TypeConverter.cpp`). The whole variant
is moved as a first-class aggregate of that type: by the `record.variant`
lowering (store into an alloca, then load the whole struct), by passing
arguments by value, and by `ref.spilled`. Bytes of another arm that fall on
the representative's padding or on an `i1` field do not survive the move.

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

Expected `42`. Actual `0`: only bit 0 survives, at every optimization
level. With a nested value enum in padding, a pointer can lose its upper
bytes (SIGSEGV).

lean2rr: emits only `[value]` enums that are unaffected: enumerations
without fields, and `Nat`/`Int`, whose arms each hold one 64-bit word.
Other multi-arm types are shared enums, and multi-field value records are
`[value]` structs, whose padding is explicit (plan §10).

## 2. In-place reuse skips stores of fields that sit elsewhere in the new record

Status: variants worked around; structures patched locally
(`0002-...-bug-2-compound-...`, reviewed).

When a unique cell of variant A is reused for variant B, RcCreateFusion
(`markVariantAvoidedCopies` → `isLoadFromVariantField` →
`hasCompatibleFieldPrefix`) skips storing B's field i if it is a load of A's
field i and the member types match for indices 0..i in declaration order.
The packed record layout, which is the default, sorts members by
alignment. A member's offset then depends on all the members, so the
"unchanged" field can move, and its store is still skipped.

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

Expected `5001`. Actual `11001` (B.c reads the low half of A.x). Declaration
order layout (`--no-pack-record-members`) gives `5001`.

lean2rr: `scripts/l2r.py` passes `--no-pack-record-members`, and lean2rr
orders each constructor's fields by decreasing alignment itself (plan
§5.1), so a record has no padding and the same member types at indices
0..i put member i at the same offset.

Structures (`markCompoundAvoidedCopies`) are worse: only the field index is
compared, not the two record types. Token reuse hands a cell of one struct
type to another of the same size, so the skipped field can sit elsewhere
even under declaration order. For example, with lean2rr's field order:

```
structure P where a : UInt64; b : UInt64; c : UInt32
structure Q where a : UInt64; b : UInt32; c : UInt32; d : UInt32; e : UInt32
@[noinline] def conv (p : P) : Q := { a := p.a + 1, b := 2, c := p.c, d := 3, e := 4 }
```

Both records are 24 bytes. `c` is at offset 16 in `P` and at offset 12 in
`Q`. Reading `q.c` gives the high half of `p.b`. lean2rr cannot avoid this
shape, so the patch skips a structure's field store only when the old and
new cells have the same type.

The same comparison decides the variant case (`hasCompatibleFieldPrefix` via
`structurallySameType`, bug 4). It ignored a record's capability: a
`[value]` member is stored inline and a shared one as a pointer, so two
arms could compare equal while their layouts differ. The bug 4 patch also
compares capability and `fixed`.

## 3. Rust allocations through Reussir's global allocator are 16-aligned

Status: worked around (in the runtime).

`ReussirGlobalAlloc` raises every Rust allocation to 16-byte alignment, so
mimalloc takes its slower aligned paths. The runtime (`runtime/leanrt`)
calls `mi_malloc` directly for its own objects.

## 4. `structurallySameType` recurses forever on equal recursive types

Status: patched locally (`0004-...-bug-4-...`, reviewed).

RcCreateFusion's `structurallySameType`
(`lib/Transformation/RcCreateFusion/RcCreateFusion.cpp`) compares two record
types member by member and recurses into member records, with no set of
pairs already assumed equal. Two distinct recursive records with the same
structure make it recurse until the stack of the LLVM worker thread
overflows (SIGSEGV). For example, `MyList Nat` and `List Nat`, when a cell
of one is reused for the other (`MyList.toList`) under
`--reuse-across-call`.

lean2rr: `scripts/l2r.py` retries rrc without `--reuse-across-call` when
rrc dies from a signal (and says so on stderr). The retry turns off reuse
across calls for the whole program, so the bug is patched: the comparison
keeps a set of type pairs under comparison and treats a pair seen again as
equal (coinductive equality). It also requires the same capability and
`fixed` flag (see bug 2): without that, closing the cycle turned a crash
into a silent miscompile when a `[value]` record met a shared record of the
same shape.

## 5. TokenReusePass crashes on a one-armed `if`

Status: patched locally (`0005-...-bug-5-...`, reviewed).

With `--reuse-across-call`, rrc crashed (SIGSEGV) in TokenReusePass on the
prelude's panic path. The panic path called `l2r_stderr_put`, which applies
the current stderr stream. The cause is not the call cycle this suggested.
After canonicalization an `if` without an else has an empty else region.
TokenReuse anchors a token free there through `front()` of that empty
region, and `ReussirTokenFreeOp::create` crashes.

lean2rr: runtime panics reach `l2r_stderr_put` through an `extern "C"`
trampoline called from Rust (§5.12), which removes that shape from the
prelude. A review of the local patches later hit the same crash in user
code shapes (a nested match inside a constructor argument, with an `if`
choosing between fields). There it happens at every `-O` level, with or
without `--reuse-across-call`, so the driver's retry does not help, and the
bug is patched: TokenReuse materializes the missing else block to hold the
token free.


## 6. Static cells accumulate increments until the 32-bit count wraps

Status: patched locally (`0006-...-bug-6-...`, reviewed).

Static (immortal) cells are tagged in the pointer's top byte. The
decrement skips them, but the increment (`load i32; add 1; store`) is
unconditional, and the decrement tests "count == 1 → free" before the
static test. After 2^32 references taken to a static cell, such as the
static `[]`, the count wraps to 1 and the next decrement frees the static
cell (SIGSEGV in `mi_free`).

```
@[noinline] def len (l : List Nat) : Nat := l.length
def loop (x : List Nat) : Nat → Nat → Nat
  | 0, acc => acc
  | n+1, acc => loop x n (acc + len x)
def main (args : List String) : IO Unit :=
  IO.println (loop [args.length] 4294967300 0)
```

Native prints `4294967300`; lean2rr's build crashed after about 15 s.

lean2rr: nothing it can do, so the bug is patched. The increment stays a
plain load, add and store, so LLVM can still fold counts on fresh cells.
The decrement's unique branch (count == 1) first checks whether the value
is one of its type's nullary immediates. If it is, the decrement frees
nothing and yields no token, so a wrapped count can never free or reuse the
static cell. The `assume(old >= 1)` after an increment becomes `old >= 1 ||
top byte != 0`, since a static count passes through 0. This costs about 4%
on rbtree and nothing measurable elsewhere, on both core types of the test
machine. Guarding the increment's store instead cost up to 22% on the
Cortex-A725 cores.

## 7. Token reuse picks decrements that can never free

Status: patched locally (`0007-...-bug-7-...`, being revised after review).

If a match's scrutinee stays live on some path, Reussir projects the
fields before the branch and increments them. On the paths where they are
dead, their decrements count as reuse donors. The decrements are expanded
as "if rc == 1 then drop and keep the token". Their counts are at least 2
there, since the parent still holds them, so these donors never free
anything. TokenReuse scores them the same as the real donor, the consumed
scrutinee's cell, and takes the most recent one. The construction then
checks a null token and allocates, and the scrutinee's cell is freed. A
decrement of a nullary constructor (an immediate) is the same kind of
phantom donor.

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

Every insertion reallocates the whole path. Returning `Tr::Node{l, x, r}`
instead of `t` is 5x faster (3.1M insertions into a 100k-node tree: 0.76 s
vs 0.14 s).

lean2rr: a value stored whole in a constructor has its fields bound where
they are used (plan §5.5, "reuse-friendly shapes"). That makes the
Std.TreeMap insert as fast as native Lean. An arm that returns the matched
value itself has no such workaround. lean2rr used to return the constructor
rebuilt from the arm's fields instead, which broke `ptrEq` identity and
sharing (Lean's `Expr.replace`-style fixpoints never stopped), so the bug is
patched.

The patch changes `RcDispatchFusion`. When the release of the scrutinee sits
inside a branch that runs exactly one of its regions once (`if` with an
else, `index_switch`, record or nullable dispatch), the arm's retains of
the bound members move into every region of that branch. Paths that
release the scrutinee then get the usual destructuring decrement. Paths
that release a member get an adjacent retain and release, which cancel. The
move is allowed only if nothing between the old and new positions releases
a value, calls a function or has a region.

Results: the BST above allocates exactly like the rebuilt version (0.74 s
-> 0.16 s). The TreeMap-shaped insert without lean2rr's workaround drops
from 12.35 to 1.33 allocations per insertion.

Not patched: the remaining 0.33 extra allocations per insertion come from
decrements of values that may be nullary immediates (under top-byte
tagging, a decrement of a `Leaf` never frees a cell). They still count as
exact-size donors and can win the most-recent tie-break. Ranking a matched
cell above such donors fixed it in a trial (rbtree 1.48 -> 0.98 s), but
cost monadic-interp 1.7%. It is left out as an optimization rather than a
fix. The patch also stops at calls before the branch, such as a `Nat`
comparison: lean2rr binds such a value's fields where they are used
instead (plan §5.5).

## 8. A padding "lift" breaks declaration-order layouts

Status: does not affect lean2rr.

Under `--no-pack-record-members`, the type converter widens a member
followed by padding to an integer that covers the padding. It does not
check that this integer is no more aligned than the next member. With
`struct [value] S3(u8,u8,u8)` and `struct [value] Q(S3, u16)`, Reussir's
layout of `Q` is 6 bytes with alignment 2, but its LLVM type `{ i32, i16 }`
is 8 bytes with alignment 4. Records containing `Q` then overflow their
cells.

lean2rr never produces this shape. Its records have no padding between
members (fields in decreasing alignment), and its `[value]` structs have a
single field whose size is a power of two.

## 9. Duplicate bound members lose a reference in `RcDispatchFusion`

Status: patched locally (`0009-...-bug-9-...`, being revised after review).

`fuseArm` collects every retain of a member extracted from the scrutinee
without checking for duplicates. When a member is used twice while the
scrutinee is still live, `boundMembers` lists it twice (`[1, 1]`). The
unique path of `RcDecrementExpansion` transfers one reference per member,
so a count is lost and the member is freed while still referenced
(use-after-free). The shape appears after Reussir inlines a callee that
drops the scrutinee:

```
fn second(t : T, y : T) -> T { y }
fn f(x : T) -> T { match x { T::N(a, l, r) => second(x, T::N { a, l, l }), T::L => x } }
```

lean2rr cannot prevent Reussir's inlining at `-O aggressive`, so this is
patched: `fuseArm` binds each member once and erases only its first retain.
Further retains of the same member are real copies and stay, as in
`fuseCompoundConsumption`.

## 10. Closure devirtualization prints result types exponentially

Status: worked around.

With `-O aggressive`, rrc devirtualizes closures. It computes a type id for
each closure result type by printing the type to a string and hashing it,
uncached, at every indirect call site and vtable. `RecordType::print`
expands named records inline and stops only at a record already on its
print stack. The text therefore grows exponentially with the nesting of
lean2rr's function and `Box` types. Programs with polymorphic recursion
through monad transformer towers ran out of memory at 16 GB.

lean2rr: the driver passes `--no-closure-wpd`. The classic benchmarks
measured the same with and without it, within noise.

## 11. Interprocedural SCCP is superlinear on large call graphs

Status: open (build time only).

The module-level `mlir::createSCCPPass` takes most of rrc's time on the
largest polymorphic-recursion towers. One adversarial program (five
transformer towers, 2132 functions) builds in about 15 minutes and 7.5 GB.
It gives the right output. A single growing `StateT` tower used at `IO` (8
lines of Lean) does not build within 30 minutes or 12-15 GB. The same
tower at `Id` builds in 60 s. Ordinary programs are unaffected.

## 12. rrc reports an unknown variable in a very large function

Status: open.

A 60,000-element `List` literal (a program compiled with a raised
`maxRecDepth`) translates, but rrc stops in its frontend (`--emit hir`)
with an error like ``unknown variable `x78617` ``. The reported position is
an integer literal (`Nat::Small{368973}`), and the variable belongs to an
unrelated function 114,000 lines earlier. The failure depends on content:
changing that one literal to 368974 makes rrc pass, and other random
literals, or 50k, 55k or 70k elements, build and run correctly. Removing
one three-`let` function also makes it pass. It looks like a token or name
confusion in the frontend. If the confused name were a variable in scope,
it might miscompile silently instead of failing. The cause is not yet
known.

## 13. Drop glue recurses once per cell of a long list

Status: patched locally (`0013-...-bug-13-...`, being revised after review).

Reussir's generated drop function for a list cell releases the head,
recurses on the tail, and only then frees the cell. That is not a tail
call, so each cell takes a stack frame. Releasing a 40-million-element list
at once overflows lean2rr's 1 GiB thread, and 10 million take 2.4x native
time and 2x memory. Native Lean frees iteratively. The release needs no
recursion in the program:

```
def main (args : List String) : IO Unit := do
  let l := List.replicate 40000000 7
  IO.println s!"{l.head?}"
```

lean2rr cannot avoid releasing such values, so the bug is patched. Inside
drop functions, a release whose count is 1 frees the cell before releasing
the cell's last recursive member, as a tail call, so LLVM turns the chain
into a loop. A tree still recurses along its other children. Releases
outside drop functions, whose cells may be reused, are unchanged. The
example now runs at 0.8x native time with native memory.

## 14. `fuseArm` loses a count when a bound member is consumed before the scrutinee's release

Status: patched locally (in the bug 9 patch, being revised after review).

`RcDispatchFusion` fuses a match arm's member retains into the release of
the scrutinee. It keeps scanning past a use that consumes a bound member,
for example the member stored in a new cell that is released again before
the scrutinee:

```
fn f(x : T) -> T { match x { T::N(a, l, r) => { let y : T = { let z : T = T::N { a, l, T::L{} }; x };
                                                 T::L{} }, T::L => x } }
```

With `x` shared, `z`'s release drops `l`'s count below its holders. The
fused decrement's shared path then reloads `l` from `x`'s cell and retains
it: a use-after-free (ASan). lean2rr can reach the shape through Reussir's
inliner (a callee that drops a constructed argument). The fix stops the
fusion at the first non-borrow use of a bound member. The bug 7 patch had
the same flaw in its own scan, found in review, and is fixed the same way.

## 15. A `match` on a `Nullable` whose arms yield a counted value does not compile

Status: does not affect lean2rr.

`match` on a `Nullable<T>` whose arms return a reference-counted value fails
with "'reussir.scf.yield' op parent operation expected a value, but nothing
is yielded". lean2rr does not use `Nullable`.

## 16. Reuse across calls is superlinear in the nesting depth of matches

Status: open (build time only).

Each IO bind is a match on the action's result, so a `main` of N
statements nests N matches deep. With `--reuse-across-call`, rrc's time and
memory grow much faster than N:

| statements | rrc build |
|---|---|
| 100 | 30 s, 1.1 GB |
| 250 | about 200 s, 12.5 GB |
| 500 | crash; the retry without the flag takes 434 s, 14.2 GB |

Without `--reuse-across-call`, 250 statements build in 16 s and 221 MB. The
generated program is correct when the build finishes.

## 17. rrc memory is quadratic in the length of a straight-line function on `Nat`

Status: open (build time only).

A `do` block of 1000 `let`s on `Nat` (a two-arm `[value]` enum) takes rrc
4.1 GB and 45 s; 2500 `let`s run out of memory (`std::bad_alloc` at 14 GB).
The same block on `UInt64` takes 127 MB. `--reuse-across-call` is not the
cause. Large literals and long generated functions hit it (a test with a
1500-`let` function needed 5.5 GB).

## 18. The `rrc` build target alone does not link

Status: worked around (build the default target).

`cmake --build build --target rrc` fails: cargo cannot find the native
static library `MLIRReussirInstrumentNonlinearFFI`, because the target does
not depend on it. Building the default target works.

## Other observations

- **Tagged pointers from the allocator.** Under top-byte tagging, a pointer
  with a nonzero top byte is an immediate. An allocator that tags real
  pointers (memory tagging, HWASan) would make real cells look like
  immediates: their decrements are skipped (a leak). The allocator lean2rr
  uses returns untagged pointers, and the sanitizer modes use the untagged
  encoding.
- **Finalization order.** Values are released in a different order from
  native Lean's `lean_del`. The difference is observable when releasing
  objects has effects, for example file handles that flush buffered output
  when dropped (plan §10).

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
