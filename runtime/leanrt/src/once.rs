//! Once-cells for constants (CAFs and closed terms): each slot holds one
//! reference to a value forever. Values are stored type-erased as their
//! pointer-sized bit pattern (the prelude's generic wrappers transmute; the
//! caller guarantees that a slot is always used at one type).
//!
//! A slot's word and set flag are also kept in `FAST` and `FLAGS`, tables at
//! fixed addresses, so that a read of a set constant is one load (two when
//! its word is 0), inlined into the generated code (`ready`, `get_raw`;
//! lean2rr's `cafAccessor`).
//!
//! Single-threaded, like the rest of the runtime. A constant being computed
//! by a context of the scheduler that blocked meanwhile is waited for by the
//! others through lean-runtime's keyed claims (`claim`; its wait cores, core
//! 3.1: `step_keyed`, `done_keyed`), under the key `(slot << 1) | 1`, odd so
//! that it never meets an object's address. The words are plain loads and
//! stores: the initializers run on the process's main thread before `main`'s
//! thread starts, and Lean code then runs on `main`'s thread only. Lean code
//! on several threads at once would need the word's store to release and
//! its load to acquire (as `lean_obj_once` does natively).

use lean_runtime::sched as ls;
use std::cell::UnsafeCell;
use std::mem::{size_of, ManuallyDrop};

struct Slots(UnsafeCell<Vec<usize>>, UnsafeCell<Vec<bool>>);
unsafe impl Sync for Slots {}

static SLOTS: Slots = Slots(UnsafeCell::new(Vec::new()), UnsafeCell::new(Vec::new()));

/// The slots below `FAST_SLOTS` also keep their word in `FAST` and their
/// set flag in `FLAGS`, two tables at fixed addresses (in `.bss`: untouched
/// pages cost no memory). The slot number is a literal at every read, so,
/// with the textures inlined, a read of a set constant whose word is not 0
/// is one load from a constant address and a test (`has`, `get_raw`); a
/// set slot whose word is 0 (a value whose bits are all 0: a `UInt64`,
/// `Float`, `Int64` or `UInt8` 0, `false`, ...) is two loads and two tests.
/// `SLOTS` stays the record, which the tables mirror. A slot from
/// `FAST_SLOTS` on (a program with that many constants) is read through
/// `SLOTS` in line, as before the tables (`rec_has`, `rec_get`).
pub const FAST_SLOTS: usize = 1 << 18;

#[repr(transparent)]
struct Word(UnsafeCell<usize>);
struct Fast([Word; FAST_SLOTS]);
unsafe impl Sync for Fast {}

static FAST: Fast = Fast([const { Word(UnsafeCell::new(0)) }; FAST_SLOTS]);

#[repr(transparent)]
struct Flag(UnsafeCell<bool>);
struct Flags([Flag; FAST_SLOTS]);
unsafe impl Sync for Flags {}

static FLAGS: Flags = Flags([const { Flag(UnsafeCell::new(false)) }; FAST_SLOTS]);

/// Write slot `slot`'s word and flag in the tables (if it has them).
#[inline(always)]
fn fast_store(slot: u64, w: usize, set: bool) {
    let i = slot as usize;
    if i < FAST_SLOTS {
        unsafe {
            *FAST.0[i].0.get() = w;
            *FLAGS.0[i].0.get() = set;
        }
    }
}

/// Whether slot `slot` is set: its word in `FAST` when not 0 (one load),
/// else its flag in `FLAGS` (a second load); for a slot without them, the
/// record (`rec_has`). No call either way. The flag's path is marked cold,
/// so that LLVM keeps its load behind the word's test instead of loading
/// both and selecting.
#[inline(always)]
pub fn has(slot: u64) -> bool {
    let i = slot as usize;
    if i < FAST_SLOTS {
        if unsafe { *FAST.0[i].0.get() } != 0 {
            return true;
        }
        std::hint::cold_path();
        unsafe { *FLAGS.0[i].0.get() }
    } else {
        rec_has(slot)
    }
}

/// Whether constant `slot` has its value: the test of every read of a
/// constant (`l2r_once_ready`); `has`. `false` sends the read to `claim`.
#[inline(always)]
pub fn ready(slot: u64) -> bool {
    has(slot)
}

/// `has` from the record (the slots without a word in the tables).
#[inline(always)]
fn rec_has(slot: u64) -> bool {
    let set = unsafe { &*SLOTS.1.get() };
    set.get(slot as usize).copied().unwrap_or(false)
}

/// The word that stores `v`, whose reference moves into it: `v`'s bytes at
/// its start, the rest 0. The readers copy back `size_of::<T>()` bytes from
/// the start (the prelude's `transmute_copy`).
#[inline(always)]
pub fn word_of<T>(v: T) -> usize {
    assert!(size_of::<T>() <= size_of::<usize>());
    let keep = ManuallyDrop::new(v);
    let mut w: usize = 0;
    unsafe {
        std::ptr::copy_nonoverlapping(&*keep as *const T as *const u8, &mut w as *mut usize as *mut u8, size_of::<T>())
    };
    w
}

/// The key of constant `slot` in lean-runtime's keyed table (odd).
#[inline]
fn key(slot: u64) -> usize {
    ((slot as usize) << 1) | 1
}

/// Whether constant `slot` has its value (the accessor of a constant or
/// closed term, `l2r_once_claim`). If not, the running context is to
/// compute it and then set it, unless another context is computing it
/// (it blocked in the computation, or in waiting for the tasks the value
/// holds): then this one waits until the value is set, as natively a
/// thread waits for the one computing it (`lean_obj_once_cold` takes a
/// lock). Needed again by the context computing it (by a task its
/// computation needs, which natively runs on another thread), it waits
/// forever, as natively (lean-runtime's `step_keyed`). The test for a value
/// is inlined into the accessor (every read of a constant), as `has` was
/// before the scheduler.
#[inline(always)]
pub fn claim(slot: u64) -> bool {
    has(slot) || claim_cold(slot)
}

#[cold]
#[inline(never)]
fn claim_cold(slot: u64) -> bool {
    crate::drop::assert_not_in_free("a constant's claim");
    loop {
        if has(slot) {
            return true;
        }
        if ls::step_keyed(key(slot)) {
            return false;
        }
    }
}

/// The word of a set slot (reading an unset slot is a runtime bug:
/// reported, not undefined behaviour). Inline: its word in `FAST`, and when
/// that is 0 its flag (the word is then the value's); after `ready(slot)`
/// the tests fold away. For a slot without a word in the tables, the record
/// (`rec_get`).
#[inline(always)]
pub fn get_raw(slot: u64) -> usize {
    let i = slot as usize;
    if i < FAST_SLOTS {
        let w = unsafe { *FAST.0[i].0.get() };
        if w != 0 {
            return w;
        }
        std::hint::cold_path();
        if unsafe { *FLAGS.0[i].0.get() } {
            0
        } else {
            unset(slot)
        }
    } else {
        rec_get(slot)
    }
}

/// `get_raw` from the record.
#[inline(always)]
fn rec_get(slot: u64) -> usize {
    if !rec_has(slot) {
        unset(slot)
    }
    let vals = unsafe { &*SLOTS.0.get() };
    match vals.get(slot as usize) {
        Some(&w) => w,
        None => unset(slot),
    }
}

/// A read of an unset slot. `extern "C"`: it cannot unwind (it exits), so
/// the inlined reads need no landing pad.
#[cold]
#[inline(never)]
extern "C" fn unset(slot: u64) -> ! {
    crate::internal_panic(&format!("leanrt: read of the unset once slot {}", slot))
}

/// Replace the value of a set slot, returning the previous bit pattern
/// (whose reference passes to the caller). Used for mutable global cells
/// (the current standard streams).
#[inline(never)]
pub fn swap_raw(slot: u64, raw: usize) -> usize {
    note_mutable(slot);
    let vals = unsafe { &mut *SLOTS.0.get() };
    assert!(has(slot), "leanrt: swap of an unset cell {}", slot);
    fast_store(slot, raw, true);
    std::mem::replace(&mut vals[slot as usize], raw)
}

/// Empty a set slot, returning its bit pattern (whose reference passes to
/// the caller).
#[inline(never)]
pub fn take_raw(slot: u64) -> usize {
    note_mutable(slot);
    if !has(slot) {
        unset(slot)
    }
    let set = unsafe { &mut *SLOTS.1.get() };
    set[slot as usize] = false;
    fast_store(slot, 0, false);
    let vals = unsafe { &*SLOTS.0.get() };
    vals[slot as usize]
}

/// Saved contents of cells `base..base + n` (`None`: empty; `n <= 3`),
/// innermost last.
struct Saved(UnsafeCell<Vec<[Option<usize>; 3]>>);
unsafe impl Sync for Saved {}
static SAVED: Saved = Saved(UnsafeCell::new(Vec::new()));

/// The slots used as mutable cells (the current standard streams): they
/// belong to the running context of lean-runtime's scheduler (switched by
/// the glue, `sched::LeanrtGlue::switched`), as natively each thread has its
/// own current streams.
struct Mutable(UnsafeCell<Vec<u64>>);
unsafe impl Sync for Mutable {}
static MUTABLE: Mutable = Mutable(UnsafeCell::new(Vec::new()));

fn note_mutable(slot: u64) {
    let m = unsafe { &mut *MUTABLE.0.get() };
    if !m.contains(&slot) {
        m.push(slot);
    }
}

/// A suspended context's mutable cells and saved contexts.
#[derive(Default)]
pub struct CtxState {
    saved: Vec<[Option<usize>; 3]>,
    cells: Vec<(u64, Option<usize>)>,
}

/// Exchange the running context's mutable cells and saved contexts with
/// `st` (the glue's `switched`: `st` is the arriving context's record, and
/// gets the leaving context's state). A cell missing from `st` is empty.
pub fn swap_ctx_state(st: &mut CtxState) {
    std::mem::swap(unsafe { &mut *SAVED.0.get() }, &mut st.saved);
    let m = unsafe { (*MUTABLE.0.get()).clone() };
    let mut cells = Vec::with_capacity(m.len());
    for &slot in m.iter() {
        let cur = if has(slot) { Some(take_raw(slot)) } else { None };
        if let Some(&(_, Some(v))) = st.cells.iter().find(|(s, _)| *s == slot) {
            set_raw(slot, v);
        }
        cells.push((slot, cur));
    }
    st.cells = cells;
}

/// A pool worker's mutable cells (its current standard streams), kept from
/// one task to the next (`sched::LeanrtGlue::task_begin`, `task_end`).
#[derive(Default)]
pub struct CellSet {
    cells: Vec<(u64, Option<usize>)>,
}

/// Exchange the running thread's mutable cells with `set` (a pool task's
/// begin and end: its worker's cells come in, the cells of the thread below
/// go to `set`, and back). A cell missing from `set` is empty. The saved
/// stream contexts stay.
pub fn swap_cells(set: &mut CellSet) {
    let m = unsafe { (*MUTABLE.0.get()).clone() };
    let mut cells = Vec::with_capacity(m.len());
    for &slot in m.iter() {
        let cur = if has(slot) { Some(take_raw(slot)) } else { None };
        if let Some(&(_, Some(v))) = set.cells.iter().find(|(s, _)| *s == slot) {
            set_raw(slot, v);
        }
        cells.push((slot, cur));
    }
    set.cells = cells;
}

/// The cells `base..base + 3` of `set` become the current ones, the running
/// thread's set aside as by `push_context` (the end of a pool worker at the
/// task manager's finalization: the generated `l2r_std_leave` then drops
/// them and gives the thread's back). Cells of `set` outside that range
/// (none: only the standard streams are mutable cells) are left alone.
pub fn enter_cells(base: u64, set: CellSet) {
    push_context(base, 3);
    for (slot, v) in set.cells {
        if let Some(v) = v {
            if slot >= base && slot < base + 3 {
                set_raw(slot, v);
            }
        }
    }
}

/// Set the cells `base..base + n` aside, leaving them empty: a new context
/// (a task starting, which natively runs on its own thread with its own
/// current standard streams). The references move to the saved context.
#[inline(never)]
pub fn push_context(base: u64, n: u64) {
    assert!(n <= 3, "leanrt: context of {} cells", n);
    let mut ctx = [None; 3];
    for i in 0..n {
        let slot = base + i;
        note_mutable(slot);
        ctx[i as usize] = if has(slot) { Some(take_raw(slot)) } else { None };
    }
    unsafe { &mut *SAVED.0.get() }.push(ctx);
}

/// Restore the cells set aside by the matching `push_context`; the caller
/// has emptied them. A cell that is set again meanwhile is left as it is
/// (its reference leaks): the leave's drop of another cell ran code that
/// used it (a stream's closure held a promise's last reference, whose
/// deferred resolution ran a `sync` dependent that printed), as natively a
/// thread-local stream made again during the thread's finalization is never
/// finalized (hunt HST-02: an assertion aborted the program here).
#[inline(never)]
pub fn pop_context(base: u64, n: u64) {
    let ctx = unsafe { &mut *SAVED.0.get() }.pop().expect("leanrt: no saved context");
    for i in 0..n {
        let slot = base + i;
        if has(slot) {
            let _leaked = take_raw(slot);
        }
        if let Some(raw) = ctx[i as usize] {
            set_raw(slot, raw);
        }
    }
}

#[inline(never)]
pub fn set_raw(slot: u64, raw: usize) {
    let vals = unsafe { &mut *SLOTS.0.get() };
    let set = unsafe { &mut *SLOTS.1.get() };
    let i = slot as usize;
    if vals.len() <= i {
        vals.resize(i + 1, 0);
        set.resize(i + 1, false);
    }
    assert!(!set[i], "leanrt: once slot {} set twice", slot);
    vals[i] = raw;
    set[i] = true;
    fast_store(slot, raw, true);
    // whoever waits for the constant goes on (one thread-local load when
    // nothing is claimed)
    ls::done_keyed(key(slot));
}

#[cfg(test)]
mod tests {
    use super::*;

    fn back<T: Copy>(w: usize) -> T {
        unsafe { std::mem::transmute_copy::<usize, T>(&w) }
    }

    #[test]
    fn words() {
        // A value's bytes, the rest 0: a value whose bits are all 0 has the
        // word 0, whatever its size.
        assert_eq!(word_of(0u8), 0);
        assert_eq!(word_of(false), 0);
        assert_eq!(word_of(0u64), 0);
        assert_eq!(back::<u8>(word_of(200u8)), 200);
        assert_eq!(back::<u32>(word_of(7u32)), 7);
        assert_eq!(back::<u64>(word_of(7u32)), 7);
        assert_eq!(back::<u64>(word_of(u64::MAX)), u64::MAX);
        assert_eq!(back::<f64>(word_of(-0.0f64)).to_bits(), (-0.0f64).to_bits());
    }

    // Slots far above any test's others (the tables and record are global).
    #[test]
    fn fast_table() {
        let s = (FAST_SLOTS - 10) as u64;
        assert!(!ready(s) && !has(s));
        set_raw(s, word_of(5u16));
        assert!(ready(s) && has(s) && claim(s));
        assert_eq!(back::<u16>(get_raw(s)), 5);
        // A set slot whose word is 0: set by its flag, read as 0.
        assert!(!has(s + 1));
        set_raw(s + 1, word_of(0u64));
        assert!(ready(s + 1) && has(s + 1) && claim(s + 1));
        assert_eq!(get_raw(s + 1), 0);
        // A mutable cell: emptied by `take_raw`, the tables too.
        let w = take_raw(s);
        assert_eq!(back::<u16>(w), 5);
        assert!(!ready(s) && !has(s));
        set_raw(s, w);
        assert_eq!(back::<u16>(swap_raw(s, word_of(6u16))), 5);
        assert_eq!(back::<u16>(get_raw(s)), 6);
        assert_eq!(swap_raw(s, word_of(0u16)), word_of(6u16));
        assert!(has(s) && get_raw(s) == 0);
        assert_eq!(take_raw(s), 0);
        assert!(!has(s));
        // A slot without a word in the tables: through the record.
        let h = FAST_SLOTS as u64 + 3;
        assert!(!has(h));
        set_raw(h, word_of(0u64));
        assert!(ready(h) && has(h));
        assert_eq!(get_raw(h), 0);
        let h2 = h + 1;
        set_raw(h2, word_of(9u64));
        assert_eq!(get_raw(h2), 9);
    }
}
