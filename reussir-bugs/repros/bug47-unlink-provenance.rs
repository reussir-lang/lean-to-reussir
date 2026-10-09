// Issue 47: reussir-rt's pending stack (`crates/reussir-rt/src/drop.rs`,
// added by patch 13-b) links a cell deferred with a wide header to the cell
// deferred before it by storing only the offset between them in its header.
// `unlink` rebuilds the earlier cell's pointer as the later cell's pointer
// plus that offset (`wrapping_offset`), so the rebuilt pointer carries the
// provenance of the later cell's allocation. The release of the earlier
// cell then reads its memory through a pointer to another allocation, here
// one already freed: undefined behaviour, which Miri reports. Reussir's own
// drop tests do not see it: they put all their cells in one allocation.
// The test defers two separately boxed cells wide (one run, linked), then
// drains.
//
// This file is the lib.rs of a scratch crate, next to copies of the
// checkout's `drop.rs` and `drop/tests.rs` (they use only core and std).
// Command (a nightly toolchain with the miri component):
//   mkdir -p t/src/drop && cp THIS t/src/lib.rs
//   cp RRC_CHECKOUT/crates/reussir-rt/src/drop.rs t/src/
//   cp RRC_CHECKOUT/crates/reussir-rt/src/drop/tests.rs t/src/drop/
//   printf '[package]\nname = "bug47"\nversion = "0.1.0"\nedition = "2024"\n[workspace]\n' > t/Cargo.toml
//   cd t && cargo +nightly miri test two_boxes_linked
// (`cargo test two_boxes_linked` runs it natively.) The test first checks
// that the two cells form one run (`depth() == 1`).
// Expected: the test passes under Miri.
// Reussir l2r-base2 71f17ae2 (13-b and every later patch keep `unlink`):
// the native run passes; Miri stops in `rel_box` with "Undefined Behavior:
// in-bounds pointer arithmetic failed: alloc... has been freed".
pub mod drop;

#[cfg(test)]
mod bug47 {
    use crate::drop::{__reussir_drop_defer_wide, __reussir_drop_drain, depth};
    use std::cell::RefCell;

    thread_local! {
        static SEEN: RefCell<Vec<u64>> = const { RefCell::new(Vec::new()) };
    }

    // The release: reads the cell's id, then frees the cell.
    unsafe extern "C" fn rel_box(p: *mut u8) {
        let id = unsafe { p.cast::<u64>().add(1).read() };
        SEEN.with(|s| s.borrow_mut().push(id));
        std::mem::drop(unsafe { Box::from_raw(p.cast::<[u64; 2]>()) });
    }

    // A new cell: 8 bytes of header (32-bit count 1, 32-bit padding 0),
    // then an id.
    fn cell(id: u64) -> *mut u8 {
        Box::into_raw(Box::new([1u64, id])).cast::<u8>()
    }

    #[test]
    fn two_boxes_linked() {
        // Two cells less than 2^42 bytes apart: link() starts a new run for
        // a cell farther from the one before it. A thread's first boxes can
        // be blocks that another thread freed, in that thread's heap (the
        // test harness's main thread); such a cell is put aside.
        let mut far = Vec::new();
        let (mut a, mut b) = (cell(10), cell(20));
        while a.addr().abs_diff(b.addr()) >= 1 << 42 {
            far.push(unsafe { Box::from_raw(a.cast::<[u64; 2]>()) });
            unsafe { b.cast::<u64>().add(1).write(10) };
            (a, b) = (b, cell(20));
        }
        unsafe {
            __reussir_drop_defer_wide(a, rel_box);
            __reussir_drop_defer_wide(b, rel_box); // b's header: offset to a
            assert_eq!(depth(), 1); // one run: b links to a
            __reussir_drop_drain(); // rel_box(b), then rel_box(a rebuilt from b)
        }
        assert_eq!(SEEN.with(|s| s.borrow().clone()), vec![20, 10]);
    }
}
