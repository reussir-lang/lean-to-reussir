# Reussir bugs that affect lean2rr

Reussir bugs found while building lean2rr, with a minimal repro, the cause
where known, what lean2rr does about it, and the status of a local patch.

Reussir revision: `ef922049`. The checkout at `./reussir` is not part of
this repository. Local patches live in `reussir-patches/` (see its README)
and are applied only to local builds. They are not submitted upstream.

Status values:
- *open*: no patch; lean2rr works around it or avoids the construct.
- *patched locally*: a patch in `reussir-patches/` fixes it. The patch
  names the bug number.

Repros of the form `rrc F.rr ...` use a plain rrc command line: `--emit
executable` plus the polymorphic-FFI directories that `scripts/l2r.py`
passes.

## 1. `[value]` enum payloads lost in the LLVM lowering

Status: open.

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

## 2. In-place variant reuse skips stores of fields that the packed layout moves

Status: open.

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

lean2rr: `scripts/l2r.py` passes `--no-pack-record-members`, which costs
memory on records with mixed field sizes.

## 3. Rust allocations through Reussir's global allocator are 16-aligned

Status: open (worked around in the runtime).

`ReussirGlobalAlloc` raises every Rust allocation to 16-byte alignment, so
mimalloc takes its slower aligned paths. The runtime (`runtime/leanrt`)
calls `mi_malloc` directly for its own objects.

## 4. `structurallySameType` recurses forever on equal recursive types

Status: open.

RcCreateFusion's `structurallySameType`
(`lib/Transformation/RcCreateFusion/RcCreateFusion.cpp`) compares two record
types member by member and recurses into member records, with no set of
pairs already assumed equal. Two distinct recursive records with the same
structure make it recurse until the stack of the LLVM worker thread
overflows (SIGSEGV). For example, `MyList Nat` and `List Nat`, when a cell
of one is reused for the other (`MyList.toList`) under
`--reuse-across-call`.

lean2rr: `scripts/l2r.py` retries rrc without `--reuse-across-call` when
rrc dies from a signal (and says so on stderr).

## 5. TokenReusePass crashes on a call cycle through runtime helpers

Status: open.

With `--reuse-across-call`, rrc crashes (SIGSEGV) in TokenReusePass when
the call graph has a cycle through the prelude's helpers: the prelude's
panic path called `l2r_stderr_put`, which applies the current stderr
stream, which can reach the array helpers that panic.

lean2rr: runtime panics reach `l2r_stderr_put` through an `extern "C"`
trampoline called from Rust, so Reussir sees no cycle (§5.12).

## 6. Static cells accumulate increments until the 32-bit count wraps

Status: open.

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

Native prints `4294967300`; lean2rr's build crashes after about 15 s.

lean2rr: none.

## 7. Token reuse picks decrements that can never free

Status: open.

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
they are used (plan §5.5, "reuse-friendly shapes"). The Std.TreeMap
insert is at parity with native Lean.
