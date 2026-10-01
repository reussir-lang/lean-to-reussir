//! Conversion origins: the identity of values that lean2rr converts to
//! another representation (translation plan §5.1, §9).
//!
//! A structural conversion (`l2r_conv_S_D`, `l2r_vconv_N`: a `List Nat`
//! stored at a uniform `List α`, an `Array Nat` at `Array α`) builds a new
//! object, where natively the value is the same object. So the conversion
//! records the new object here, keyed by its address, with the value it was
//! converted from (its *origin*; for a value converted from a converted
//! value, the first origin), kept alive by the record, and the origin's
//! address. Then:
//! - `ptrAddrUnsafe` of a converted value is its origin's address (`addr`),
//!   so the same value converted twice is `ptrEq` to itself, and to the
//!   original;
//! - converting a converted value back to its origin's representation gives
//!   the origin itself (`back`, `take`): a value that crosses into uniform
//!   code and back (a fixpoint step through a wrapper) is the same object.
//!
//! A record holds a reference to the converted object too, so that its
//! address is not reused while the record exists, and so that the object
//! stays unchanged: every update of a shared object copies it. Records whose
//! converted object only the record still holds are dead; each new record
//! first checks two records, in turn, and releases the dead ones (with their
//! origins). So at most about as many dead records as live ones exist.
//!
//! Values are pointer-sized handles whose reference count is the `u32` at
//! the address they point to (Reussir records, `RVec`, the runtime's
//! `Rc`-based arrays). Static cells and immediates (tagged in the top byte)
//! are not recorded. One table per thread (tasks run on the main thread).

use std::cell::RefCell;
use std::collections::HashMap;
use std::hash::{BuildHasherDefault, Hasher};
use std::mem::size_of;
use std::sync::atomic::{AtomicBool, Ordering};

/// Whether anything was ever recorded (the fast path of `addr`).
static ANY: AtomicBool = AtomicBool::new(false);

#[derive(Default)]
struct AddrHasher(u64);

impl Hasher for AddrHasher {
    fn finish(&self) -> u64 {
        self.0
    }
    fn write(&mut self, bytes: &[u8]) {
        for &b in bytes {
            self.0 = (self.0 ^ b as u64).wrapping_mul(0x100000001b3);
        }
    }
    fn write_usize(&mut self, n: usize) {
        self.0 = (n as u64 >> 3).wrapping_mul(0x9e3779b97f4a7c15);
    }
}

struct Entry {
    conv_drop: unsafe fn(usize),
    orig: usize,
    orig_drop: unsafe fn(usize),
    orig_code: u64,
    orig_addr: u64,
}

#[derive(Default)]
struct Table {
    map: HashMap<usize, Entry, BuildHasherDefault<AddrHasher>>,
    keys: Vec<usize>,
    cursor: usize,
}

thread_local! {
    static TABLE: RefCell<Table> = RefCell::new(Table::default());
}

#[inline(always)]
fn handle<T>(x: &T) -> usize {
    unsafe { *(x as *const T as *const usize) }
}

#[inline(always)]
fn heap(p: usize) -> bool {
    p != 0 && (p >> 56) == 0
}

unsafe fn drop_as<T>(p: usize) {
    drop(std::ptr::read(&p as *const usize as *const T))
}

/// Check up to `n` records, in turn, and take out the dead ones: their
/// converted object is held by the record alone. The references to release
/// are returned, to be released once the table is no longer borrowed.
fn sweep(t: &mut Table, n: usize, out: &mut Vec<(unsafe fn(usize), usize)>) {
    for _ in 0..n {
        if t.keys.is_empty() {
            return;
        }
        if t.cursor >= t.keys.len() {
            t.cursor = 0;
        }
        let k = t.keys[t.cursor];
        if unsafe { *(k as *const u32) } == 1 {
            t.keys.swap_remove(t.cursor);
            if let Some(e) = t.map.remove(&k) {
                out.push((e.conv_drop, k));
                out.push((e.orig_drop, e.orig));
            }
        } else {
            t.cursor += 1;
        }
    }
}

fn release(refs: Vec<(unsafe fn(usize), usize)>) {
    for (d, p) in refs {
        unsafe { d(p) }
    }
}

/// `l2r_origin_note(src, dst, code)`: `dst` was just converted from `src`,
/// whose representation lean2rr numbers `code`. Returns `dst`.
#[inline(never)]
pub fn note<S, D>(src: S, dst: D, code: u64) -> D {
    if size_of::<S>() != size_of::<usize>() || size_of::<D>() != size_of::<usize>() {
        drop(src);
        return dst;
    }
    let sp = handle(&src);
    let dp = handle(&dst);
    if !heap(sp) || !heap(dp) || sp == dp {
        drop(src);
        return dst;
    }
    let mut refs = Vec::new();
    let mut src = Some(src);
    TABLE.with(|t| {
        let mut t = t.borrow_mut();
        sweep(&mut t, 2, &mut refs);
        let entry = match t.map.get(&sp) {
            // Converted from a converted value: the first origin.
            Some(e) => {
                unsafe { *(e.orig as *mut u32) += 1 };
                Entry { conv_drop: drop_as::<D>, orig: e.orig, orig_drop: e.orig_drop, orig_code: e.orig_code, orig_addr: e.orig_addr }
            }
            None => {
                // The record keeps the reference `src` came with.
                std::mem::forget(src.take());
                Entry { conv_drop: drop_as::<D>, orig: sp, orig_drop: drop_as::<S>, orig_code: code, orig_addr: sp as u64 }
            }
        };
        // The record's own reference to the converted object.
        unsafe { *(dp as *mut u32) += 1 };
        if let Some(old) = t.map.insert(dp, entry) {
            refs.push((old.conv_drop, dp));
            refs.push((old.orig_drop, old.orig));
        } else {
            t.keys.push(dp);
        }
    });
    ANY.store(true, Ordering::Relaxed);
    drop(src);
    release(refs);
    dst
}

/// `l2r_origin_back(x, code)`: whether `x` was converted from a value whose
/// representation lean2rr numbers `code`.
#[inline(never)]
pub fn back<S>(x: S, code: u64) -> bool {
    if !ANY.load(Ordering::Relaxed) || size_of::<S>() != size_of::<usize>() {
        drop(x);
        return false;
    }
    let p = handle(&x);
    let r = TABLE.with(|t| t.borrow().map.get(&p).map(|e| e.orig_code == code).unwrap_or(false));
    drop(x);
    r
}

/// `l2r_origin_take(x)`: the value `x` was converted from (see `back`).
#[inline(never)]
pub fn take<S, D>(x: S) -> D {
    let p = handle(&x);
    let o = TABLE.with(|t| {
        let t = t.borrow();
        let e = t.map.get(&p).expect("l2r_origin_take: no origin");
        unsafe { *(e.orig as *mut u32) += 1 };
        e.orig
    });
    drop(x);
    unsafe { std::ptr::read(&o as *const usize as *const D) }
}

/// The identity (`ptrAddrUnsafe`) of the object at address `p`, when it was
/// converted from another value: that value's address.
#[inline(always)]
pub fn addr(p: usize) -> Option<u64> {
    if !ANY.load(Ordering::Relaxed) {
        return None;
    }
    addr_slow(p)
}

#[inline(never)]
fn addr_slow(p: usize) -> Option<u64> {
    TABLE.with(|t| t.borrow().map.get(&p).map(|e| e.orig_addr))
}
