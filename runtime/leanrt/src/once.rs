//! Once-cells for constants (CAFs and closed terms): each slot holds one
//! reference to a value forever. Values are stored type-erased as their
//! pointer-sized bit pattern (the prelude's generic wrappers transmute; the
//! caller guarantees that a slot is always used at one type).
//!
//! Single-threaded, like the rest of the runtime.

use std::cell::UnsafeCell;

struct Slots(UnsafeCell<Vec<usize>>, UnsafeCell<Vec<bool>>);
unsafe impl Sync for Slots {}

static SLOTS: Slots = Slots(UnsafeCell::new(Vec::new()), UnsafeCell::new(Vec::new()));

#[inline]
pub fn has(slot: u64) -> bool {
    let set = unsafe { &*SLOTS.1.get() };
    set.get(slot as usize).copied().unwrap_or(false)
}

/// The value of a set slot (reading an unset slot is a runtime bug:
/// reported, not undefined behaviour).
#[inline]
pub fn get_raw(slot: u64) -> usize {
    if !has(slot) {
        unset(slot)
    }
    let vals = unsafe { &*SLOTS.0.get() };
    vals[slot as usize]
}

#[cold]
#[inline(never)]
fn unset(slot: u64) -> ! {
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
    let vals = unsafe { &*SLOTS.0.get() };
    vals[slot as usize]
}

/// Saved contents of cells `base..base + n` (`None`: empty; `n <= 3`),
/// innermost last.
struct Saved(UnsafeCell<Vec<[Option<usize>; 3]>>);
unsafe impl Sync for Saved {}
static SAVED: Saved = Saved(UnsafeCell::new(Vec::new()));

/// The slots used as mutable cells (the current standard streams): they
/// belong to the running context of the scheduler (`sched`), as natively
/// each thread has its own current streams.
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
/// `st` (see `sched::switch_to`: the leaving context's go to its record,
/// whose own were emptied when it last arrived; then the arriving
/// context's come from its record). A cell missing from `st` is empty.
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
/// has emptied them.
#[inline(never)]
pub fn pop_context(base: u64, n: u64) {
    let ctx = unsafe { &mut *SAVED.0.get() }.pop().expect("leanrt: no saved context");
    for i in 0..n {
        let slot = base + i;
        assert!(!has(slot), "leanrt: context cell {} still set", slot);
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
}
