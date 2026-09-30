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
    let vals = unsafe { &mut *SLOTS.0.get() };
    assert!(has(slot), "leanrt: swap of an unset cell {}", slot);
    std::mem::replace(&mut vals[slot as usize], raw)
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
