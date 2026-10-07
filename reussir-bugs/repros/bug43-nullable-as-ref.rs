// Bug 43: reussir-rt's `Nullable::as_ref` returns a reference to a local
// copy of the pointer word (a slot in `as_ref`'s own stack frame), not to
// the `Nullable`'s storage: the reference dangles once `as_ref` returns.
// Two tests of `Nullable<Rc<u64>>`, compiled against the checkout's
// `crates/reussir-rt/src/nullable.rs` and `rc.rs` (both use only `std`),
// which run.sh links to `rt/` next to this file's copy.
// Command: rustc --edition 2021 --test THIS -o t && ./t
// Expected: both tests pass (`test result: ok. 2 passed`).
// Reussir ef922049: both fail (`as_ref returned 0x..., the Nullable lives
// at 0x...`; `the slot as_ref pointed at now holds ..., not the box ...`).
#[path = "rt/rc.rs"]
#[allow(dead_code)]
mod rc;
#[path = "rt/nullable.rs"]
#[allow(dead_code)]
mod nullable;

use nullable::Nullable;
use rc::Rc;

#[inline(never)]
fn clobber_stack(n: u64) -> u64 {
    // Reuses the stack area as_ref's frame occupied.
    let a = [n.wrapping_mul(0x9E37_79B9_7F4A_7C15); 64];
    std::hint::black_box(&a).iter().fold(0u64, |s, &x| s.wrapping_add(x))
}

#[test]
fn as_ref_points_into_self() {
    let n = Nullable::new(Rc::new(123u64));
    let r = n.as_ref().unwrap() as *const Rc<u64> as usize;
    let me = &n as *const Nullable<Rc<u64>> as usize;
    assert_eq!(r, me, "as_ref returned {r:#x}, the Nullable lives at {me:#x}");
}

#[test]
fn as_ref_reads_after_another_call() {
    let n = Nullable::new(Rc::new(123u64));
    let r: &Rc<u64> = n.as_ref().unwrap();
    std::hint::black_box(clobber_stack(7));
    // Reading through `r` dereferences whatever now sits in as_ref's old
    // stack slot.
    let word = unsafe { *(r as *const Rc<u64> as *const usize) };
    let me = unsafe { *(&n as *const Nullable<Rc<u64>> as *const usize) };
    assert_eq!(word, me, "the slot as_ref pointed at now holds {word:#x}, not the box {me:#x}");
}
