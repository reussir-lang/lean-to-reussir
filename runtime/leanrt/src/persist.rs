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
//! does not look into it). Marking keeps one reference to the cell for the
//! rest of the run: the reference the call received is never released
//! (`forget`, so no count is read or written here; Reussir's own copy made
//! it). So the cell is never freed, so it never releases what it holds,
//! and it is never unique (an update copies it), as natively. The cell's
//! handle word (its address; for a box, its payload's) goes into a set of
//! marked cells, which tells a later visit (in this walk or a later one)
//! not to look into the cell again: a marked cell is never freed, so its
//! address is never reused. A nullary variant is marked as any handle (its
//! word goes into the set; its release does nothing, so keeping it costs
//! nothing): it holds nothing.
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
use std::cell::UnsafeCell;
use std::mem::{forget, replace, size_of, transmute_copy};

/// The handle types that `mark` takes: one word that identifies the cell
/// while a reference to it is kept (Reussir's records and enums, `Bridge`,
/// whose nullary variants are words of their own; Reussir's `Rc`, a
/// promise or a runtime object; leanrt's arrays and thunk or task cells).
/// No other type compiles in `mark`: a scalar is no cell.
///
/// # Safety
/// The type is one word, and two live values of it with the same word are
/// the same cell (or the same nullary variant).
pub unsafe trait Counted: Sized {}

unsafe impl<X> Counted for reussir_rt::bridge::Bridge<X> {}
unsafe impl<T> Counted for reussir_rt::rc::Rc<T> {}
unsafe impl<T: Clone> Counted for crate::drop::Vec<T> {}
unsafe impl<T> Counted for crate::drop::Cell<T> {}

/// A set of nonzero words (the marked cells' words; a box's: its payload's
/// address): open addressing with linear probing in a power-of-two table
/// at most half full, 0 marking a free slot. A cell's word is never 0 (an
/// address, or a nullary variant's tagged word). Generic hash sets cost
/// more per mark: `std`'s with SipHash made a walk of 300 000 cells
/// (`RtPersistWalk`) run 2.8 times the instructions, `hashbrown` with a
/// one-multiplication hash 1.8 times (its insert and its rehashes), this
/// table under a mutex 1.5 times, where the count's bit cost a load and a
/// store.
struct WordSet {
    slots: Vec<usize>,
    len: usize,
}

impl WordSet {
    const fn new() -> Self {
        WordSet { slots: Vec::new(), len: 0 }
    }

    /// The slot where `w`'s probe starts: a multiplication, its high half
    /// folded into the low one (the low bits of an address are zeros).
    #[inline(always)]
    fn start(w: usize, mask: usize) -> usize {
        let h = (w as u64).wrapping_mul(0x9e37_79b9_7f4a_7c15);
        (h ^ (h >> 32)) as usize & mask
    }

    /// Put `w` in the set: whether it was there already.
    fn insert(&mut self, w: usize) -> bool {
        debug_assert!(w != 0, "leanrt: persist mark of a zero word");
        if 2 * (self.len + 1) > self.slots.len() {
            self.grow();
        }
        let mask = self.slots.len() - 1;
        let mut i = Self::start(w, mask);
        loop {
            let s = self.slots[i];
            if s == w {
                return true;
            }
            if s == 0 {
                self.slots[i] = w;
                self.len += 1;
                return false;
            }
            i = (i + 1) & mask;
        }
    }

    fn contains(&self, w: usize) -> bool {
        if self.slots.is_empty() {
            return false;
        }
        let mask = self.slots.len() - 1;
        let mut i = Self::start(w, mask);
        loop {
            match self.slots[i] {
                0 => return false,
                s if s == w => return true,
                _ => i = (i + 1) & mask,
            }
        }
    }

    /// Double the table (at first 1024 slots) and put the words back.
    #[cold]
    #[inline(never)]
    fn grow(&mut self) {
        let n = (self.slots.len() * 2).max(1024);
        let old = replace(&mut self.slots, vec![0; n]);
        let mask = n - 1;
        for w in old.into_iter().filter(|&w| w != 0) {
            let mut i = Self::start(w, mask);
            while self.slots[i] != 0 {
                i = (i + 1) & mask;
            }
            self.slots[i] = w;
        }
    }
}

struct Global<T>(UnsafeCell<T>);

unsafe impl<T> Sync for Global<T> {}

/// The words of the marked cells. lean2rr runs Lean code on one thread at a
/// time (the module initializers, then `main`'s thread; lean-runtime's
/// scheduler switches its contexts on it), as `task::TASKS` assumes, so
/// the set needs no lock; no context switches while it is used. A
/// thread-local was slower (its lazy-initialization test and the
/// `RefCell`'s flag: `RtPersistWalk` 774 M instructions against 744 M with
/// a mutex) and would split the set between the initializers' thread and
/// `main`'s.
static MARKED: Global<WordSet> = Global(UnsafeCell::new(WordSet::new()));

#[inline(always)]
fn marked() -> &'static mut WordSet {
    unsafe { &mut *MARKED.0.get() }
}

/// Put `w` in the set of marked cells: whether it was there already.
#[inline]
fn insert(w: usize) -> bool {
    marked().insert(w)
}

fn contains(w: usize) -> bool {
    marked().contains(w)
}

/// Unit tests run on several threads at once: the ones that mark take this
/// lock (the set has none).
#[cfg(test)]
pub(crate) static TEST_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());

#[cfg(test)]
pub(crate) fn test_lock() -> std::sync::MutexGuard<'static, ()> {
    TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner())
}

#[inline(always)]
fn word_of<T: Counted>(v: &T) -> usize {
    const { assert!(size_of::<T>() == size_of::<usize>()) };
    unsafe { transmute_copy(v) }
}

/// Whether the cell `v` is persistent already (its reference is then
/// released); otherwise it is marked persistent now, `v`'s reference kept
/// for the rest of the run, and the answer is false.
#[inline]
pub fn mark<T: Counted>(v: T) -> bool {
    if insert(word_of(&v)) {
        drop(v);
        true
    } else {
        forget(v);
        false
    }
}

/// Mark the payload of box `v` persistent, without looking into it: a
/// payload whose type cannot hold a task, met by the walk, and
/// `Runtime.markPersistent`'s argument. The box's reference is kept (a
/// box holds one reference to its payload) unless the payload was marked
/// already; an immediate (an odd word) is no cell. Returns 0.
#[inline]
pub fn mark_box(v: LAny) -> u64 {
    let w = v.word();
    if w & 1 == 0 && !insert((w & ADDR_MASK) as usize) {
        forget(v);
    } else {
        drop(v);
    }
    0
}

/// Whether the cell `v` is persistent (tests).
pub fn is_persistent<T: Counted>(v: &T) -> bool {
    contains(word_of(v))
}

/// Whether the payload of box `v` is persistent (tests).
pub fn box_is_persistent(v: &LAny) -> bool {
    let w = v.word();
    w & 1 == 0 && contains((w & ADDR_MASK) as usize)
}

#[cfg(test)]
mod tests {
    use super::*;
    use reussir_rt::bridge::Bridge;

    /// A cell is marked once: one reference to it is kept, the next marks
    /// answer true and release theirs; the cell is shared, never freed.
    #[test]
    fn marks_a_cell_once() {
        let _g = test_lock();
        let v = crate::array::from_slice(&[1u64, 2, 3]);
        assert!(v.is_unique() && !is_persistent(&v));
        assert!(!mark(v.clone()));
        assert!(is_persistent(&v) && !v.is_unique());
        assert!(mark(v.clone()));
        let w = v.clone();
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
        let _g = test_lock();
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

    /// The set keeps every word through its growth, and answers each once.
    #[test]
    fn word_set_grows() {
        let mut set = WordSet::new();
        for i in 1..5000usize {
            assert!(!set.insert(i * 16));
        }
        for i in 1..5000usize {
            assert!(set.contains(i * 16) && set.insert(i * 16));
        }
        assert!(!set.contains(8) && set.len == 4999);
    }

    /// The mark writes nothing into the cell: a handle over a plain block
    /// (a `Bridge` over a word stands for a record handle, or a nullary
    /// variant's word) is marked by its word alone.
    #[test]
    fn marks_without_writing() {
        let _g = test_lock();
        let p = Box::into_raw(Box::new([7u32, 1u32])) as usize;
        assert!(!mark(Bridge::new(p)));
        assert!(mark(Bridge::new(p)) && is_persistent(&Bridge::new(p)));
        assert_eq!(unsafe { *(p as *const [u32; 2]) }, [7, 1]);
        let tbi = Bridge::new(p | (3usize << 56));
        assert!(!is_persistent(&tbi) && !mark(tbi));
        // The block stays allocated, as a marked cell is never freed: the set
        // is the process's, and another test's block must not reuse the
        // address.
    }
}
