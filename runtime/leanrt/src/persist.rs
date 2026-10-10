//! The persistent mark (lean2rr's walk `l2r_persist_T`, translation plan
//! §5.14), as native Lean's persistent objects.
//!
//! Natively `lean_mark_persistent` visits every object a value reaches,
//! with a stack of objects to visit, and sets each visited object's count
//! to 0: a persistent object is never freed and never exclusive, and a
//! later walk does not look into it (the walk skips an object whose count
//! is 0 already). It waits for each task it reaches (`lean_task_get`), a
//! promise's through its result task. It runs after each `[init]`
//! declaration's initializer and on each constant that the module
//! initializer evaluates, on a closed term at its first evaluation
//! (`lean_obj_once_cold`), and in `Runtime.markPersistent`.
//!
//! lean2rr's walk is generated per type; it looks into the types that can
//! hold a task. Each cell it visits (a record, an array, a function value,
//! a thunk or task, a reference, a promise) is marked here (`mark`), and
//! so is a box's payload whose type cannot hold a task (`mark_box`, which
//! does not look into it): the cell's count, the `u32` at its address, goes
//! up by `PERSISTENT` (2^30). So the count never comes back to 1: the cell
//! is never freed, so it never releases what it holds, and it is never
//! unique (an update copies it), as natively; and the bit tells a later
//! visit (in this walk or a later one) not to look into the cell again.
//! Because the mark is in the cell, a marked cell's address is never
//! reused (the cell is never freed). The hot paths do not change: a count
//! update is the same addition or subtraction, and their tests are for 1.
//!
//! The limit: a count of `drop::IMMORTAL` (2^31) or more is a dummy box of
//! a nullary variant under the `immortal` encoding, for leanrt (`any::of`
//! boxes such a record as an immediate; the inline count updates stop). A
//! marked cell gets there at 2^30 real references to it (8 GiB of pointers,
//! as `Array.replicate (2^30) x` of a marked `x`), an unmarked one at 2^31.
//!
//! A nullary variant is no cell and is not marked: under the `tbi` encoding
//! (the aarch64 default) by its nonzero top byte (its dummy box's count is
//! an ordinary count, from 2), under the `immortal` encoding by its dummy's
//! count, `IMMORTAL` or more.
//!
//! Natively waiting for a task only blocks: the term's tasks are run by the
//! workers in the order they were queued, whatever order the walk waits for
//! them in. lean-runtime's `wait` does the same, so the walk waits for each
//! task as it reaches it, in one pass.
//!
//! `mark_box` also marks `Runtime.markPersistent`'s argument, boxed,
//! whatever its type (the walk looks only into the types that can hold a
//! task, and runs only in a program that makes tasks): a handle marked
//! persistent is never closed, as natively.

use crate::any::{LAny, ADDR_MASK};
use crate::drop::IMMORTAL;
use std::mem::{size_of, transmute_copy};

/// The bit of a cell's count that marks it persistent.
pub const PERSISTENT: u32 = 1 << 30;

/// The handle types that `mark` takes: one word, a pointer to a block whose
/// `u32` count is at offset 0 (Reussir's records and enums, `Bridge`, whose
/// nullary variants are immediates; Reussir's `Rc`, a promise or a runtime
/// object; leanrt's arrays and thunk or task cells). No other type compiles
/// in `mark`: a scalar word must never be written through.
///
/// # Safety
/// The type is one word, and a value of it is either such a pointer or (a
/// `Bridge` only) a Reussir immediate of the `tbi` encoding (a nonzero top
/// byte) or of the `immortal` encoding (a pointer to a dummy box).
pub unsafe trait Counted: Sized {}

unsafe impl<X> Counted for reussir_rt::bridge::Bridge<X> {}
unsafe impl<T> Counted for reussir_rt::rc::Rc<T> {}
unsafe impl<T: Clone> Counted for crate::drop::Vec<T> {}
unsafe impl<T> Counted for crate::drop::Cell<T> {}

/// The address of the count of the cell that `v` is, or none for a Reussir
/// immediate of the `tbi` encoding (a nonzero top byte).
#[inline(always)]
fn count_at<T: Counted>(v: &T) -> Option<*mut u32> {
    const { assert!(size_of::<T>() == size_of::<usize>()) };
    let w: usize = unsafe { transmute_copy(v) };
    (w >> 56 == 0 && w != 0).then_some(w as *mut u32)
}

/// Mark the cell whose count is at `p`: whether it was persistent already.
/// A dummy box (count `IMMORTAL` or more) is left as it is (false).
///
/// # Safety
/// `p` is the address of a live counted block's count.
#[inline(always)]
unsafe fn mark_at(p: *mut u32) -> bool {
    let c = unsafe { *p };
    if c >= IMMORTAL {
        false
    } else if c & PERSISTENT != 0 {
        true
    } else {
        unsafe { *p = c | PERSISTENT };
        false
    }
}

/// Whether the cell `v` is persistent already; otherwise it is marked
/// persistent now, and the answer is false. A nullary variant (no cell, or a
/// dummy box) is never marked: false, and nothing changes (it holds
/// nothing).
#[inline]
pub fn mark<T: Counted>(v: T) -> bool {
    let r = match count_at(&v) {
        Some(p) => unsafe { mark_at(p) },
        None => false,
    };
    drop(v);
    r
}

/// Mark the payload of box `v` persistent, without looking into it: a
/// payload whose type cannot hold a task, met by the walk, and
/// `Runtime.markPersistent`'s argument. Every payload a box points to is a
/// block whose `u32` count is at offset 0 (`any`'s module comment); an
/// immediate (an odd word) has none. Returns 0.
#[inline]
pub fn mark_box(v: LAny) -> u64 {
    let w = v.word();
    if w & 1 == 0 {
        unsafe { mark_at((w & ADDR_MASK) as usize as *mut u32) };
    }
    drop(v);
    0
}

/// Whether the cell `v` is persistent (tests).
pub fn is_persistent<T: Counted>(v: &T) -> bool {
    match count_at(v) {
        Some(p) => {
            let c = unsafe { *p };
            c < IMMORTAL && c & PERSISTENT != 0
        }
        None => false,
    }
}

/// Whether the payload of box `v` is persistent (tests).
pub fn box_is_persistent(v: &LAny) -> bool {
    let w = v.word();
    if w & 1 != 0 {
        return false;
    }
    let c = unsafe { *((w & ADDR_MASK) as usize as *const u32) };
    c < IMMORTAL && c & PERSISTENT != 0
}

#[cfg(test)]
mod tests {
    use super::*;
    use reussir_rt::bridge::Bridge;

    fn count<T: Counted>(v: &T) -> u32 {
        unsafe { *count_at(v).unwrap() }
    }

    /// A cell is marked once: its count goes up by `PERSISTENT`, the next
    /// marks answer true and change nothing, and the count's updates go on
    /// as before (the cell is shared, never freed).
    #[test]
    fn marks_a_cell_once() {
        let v = crate::array::from_slice(&[1u64, 2, 3]);
        assert!(v.is_unique() && !is_persistent(&v));
        assert!(!mark(v.clone()));
        assert!(is_persistent(&v) && !v.is_unique());
        assert_eq!(count(&v), PERSISTENT | 1);
        assert!(mark(v.clone()));
        assert_eq!(count(&v), PERSISTENT | 1);
        let w = v.clone();
        assert_eq!(count(&v), PERSISTENT | 2);
        drop(w);
        assert!(crate::is_shared(&v));
        // An update through the only handle copies the block.
        let h = v.hdr();
        let u = crate::array::set(v, 0, 9u64);
        assert!(u.hdr() != h && u.is_unique() && !is_persistent(&u));
    }

    /// Through a box: the payload's cell (the low 48 bits of the word); an
    /// immediate box is no cell.
    #[test]
    fn marks_a_box_payload() {
        let s = crate::string::from_bytes(b"persistent");
        let b = crate::any::of(s, 0);
        assert!(!box_is_persistent(&b));
        assert_eq!(mark_box(b.clone()), 0);
        assert!(box_is_persistent(&b) && !b.is_exclusive());
        assert_eq!(mark_box(b.clone()), 0);
        assert!(box_is_persistent(&b));
        let i = LAny::imm(5);
        assert_eq!(mark_box(i.clone()), 0);
        assert!(!box_is_persistent(&i) && !box_is_persistent(&LAny::unit()));
    }

    /// A dummy box (the `immortal` encoding of a nullary variant) and a
    /// word with a nonzero top byte (the `tbi` encoding) are left as they
    /// are (a `Bridge` over a plain word stands for a record handle here).
    #[test]
    fn leaves_immediates() {
        let p = Box::into_raw(Box::new([IMMORTAL | PERSISTENT, 1u32])) as usize;
        assert!(!mark(Bridge::new(p)));
        assert_eq!(unsafe { *(p as *const u32) }, IMMORTAL | PERSISTENT);
        let tbi = Bridge::new(p | (3usize << 56));
        assert!(!is_persistent(&tbi) && !mark(tbi));
    }
}
