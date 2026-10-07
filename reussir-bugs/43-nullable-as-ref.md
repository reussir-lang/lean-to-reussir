# 43. `Nullable::as_ref` in Reussir's runtime returns a reference to a local copy

## Summary

**Kind:** bug. **Status:** not patched; it does not affect lean2rr
(unreachable: nothing calls the function, and no `Nullable` value reaches
Rust code).

**Verdict: bug.** `reussir_rt::nullable::Nullable<T>` is the Rust side of
Reussir's `Nullable<T>` (a pointer that may be null, one word).
`Nullable::as_ref` should return a reference to the `T` stored in the
`Nullable` itself. It returns a reference to a copy of the pointer word in
its own stack frame, which is gone when it returns: the reference dangles.
`as_deref` calls `as_ref` and has the same fault. A second, smaller
problem: `Nullable::new` reinterprets a `T` as the pointer word, and the
check that `T` has the size and the alignment of a pointer is a
`debug_assert!`, so a release build accepts any `T` without a check.

Found by a review of Reussir's runtime crate (finding HRT-01).

## Symptom and repro

Repro [`repros/bug43-nullable-as-ref.rs`](repros/bug43-nullable-as-ref.rs):
two Rust tests of `Nullable<Rc<u64>>`, compiled with `rustc --test`
against the checkout's `crates/reussir-rt/src/nullable.rs` and `rc.rs`
(they use only `std`):

```rust
let n = Nullable::new(Rc::new(123u64));
let r = n.as_ref().unwrap() as *const Rc<u64> as usize;
let me = &n as *const Nullable<Rc<u64>> as usize;
assert_eq!(r, me);          // as_ref_points_into_self
```

The second test (`as_ref_reads_after_another_call`) calls another function
that uses the stack, then reads the pointer word through the reference.

**Command.** `run.sh RRC_CHECKOUT 43` (it compiles the repro with the
checkout's rustc and runs it).

**Expected.** Both tests pass: the reference points into `n`, and reading
through it gives `n`'s pointer word.

**Actual on ef922049** (and on the whole series, which does not change
`nullable.rs`): both tests fail. The reference points into `as_ref`'s
dead stack frame, not at `n`, and after the other call that slot holds
another value. `run.sh` prints `issue 43   REPRODUCES  Nullable::as_ref:
2 of 2 tests fail (the reference points to a dead copy)`.

## Cause

`crates/reussir-rt/src/nullable.rs`:

```rust
pub struct Nullable<T> {
    ptr: StdOption<NonNull<u8>>,
    ty: PhantomData<T>,
}
...
    pub fn as_ref(&self) -> Option<&T> {
        match self.ptr {
            Some(ptr) => Some(unsafe { NonNull::from(&ptr).cast::<T>().as_ref() }),
            None => None,
        }
    }
```

`self.ptr` is `Copy`, so `match self.ptr` binds `ptr` to a copy in the
function's frame. `&ptr` is the address of that copy, and the `&T` made
from it lives as long as `&self`, much longer than the copy. The fix is to
match on `&self.ptr` (`Some(ptr) => ... NonNull::from(ptr) ...`), so that
the reference points into the `Nullable` (with that change, in a copy of
the file outside the checkout, the repro's two tests pass). `to_option`
reads through the same kind of local reference, but it reads at once,
while the copy is alive, so it is correct.

`Nullable::new` checks `size_of::<T>() == size_of::<Self>()` and the
alignments with `debug_assert!` only.

## lean2rr

Not affected, and not reachable:

- Nothing in Reussir's runtime or in compiler-emitted code calls
  `as_ref` or `as_deref`: the generated code works on the pointer word
  itself.
- A `Nullable` cannot reach Rust code: the front end rejects it at the
  FFI boundary (`crates/reussir-core/src/full/ffi.rs`: "`Nullable` cannot
  cross the FFI boundary yet"), so no texture receives one.
- lean2rr does not use `Nullable` at all.

## Why it stays unpatched

No patch (the owner's rule since 2026-10-07: Reussir is changed only where
lean2rr has no other way; lean2rr does not reach this code). The repro
documents it.

## Upstream note

`Nullable::as_ref` (`crates/reussir-rt/src/nullable.rs`) matches on
`self.ptr` by value, so the returned `&T` points to a local copy of the
pointer word (dangling once `as_ref` returns; `as_deref` inherits it).
Matching on `&self.ptr` fixes it. `Nullable::new`'s size and alignment
checks are `debug_assert!`s; a `const` assertion (or `assert!`) would
also hold in release builds.
