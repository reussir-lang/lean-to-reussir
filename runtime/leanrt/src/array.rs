//! Arrays: `crate::drop::Vec<T>` (`RVec`), one block holding the reference
//! count, the size, the capacity and the elements (`drop::Hdr`), freed
//! without recursion (`crate::drop`).
//!
//! Arrays are values: every mutation goes through `make_mut`, which copies
//! a shared block first, so an array is updated in place only when it is
//! uniquely referenced, like Lean's. A unique block grows in place with
//! `mi_realloc` (at least doubling).
//!
//! `ByteArray` and `FloatArray` are `RVec<u8>`/`RVec<f64>`, and lean2rr's
//! compact scalar arrays `RVec<u8>`, `RVec<u16>`, `RVec<u32>`, `RVec<u64>`,
//! `RVec<f32>` and `RVec<f64>` (every function here is generic over the
//! element type; a scalar's clone is its bits, its release nothing). An
//! `LRef` (`ref_*` below) is a 0/1-element `RVec` mutated through every
//! alias.

pub use crate::drop::Vec as RVec;
use crate::drop::{elems, Hdr, HDR};
use lean_runtime::semantics as sem;
use std::ffi::c_void;
use std::mem::size_of;

extern "C" {
    fn mi_malloc(size: usize) -> *mut c_void;
    fn mi_realloc(p: *mut c_void, size: usize) -> *mut c_void;
}

#[cold]
#[inline(never)]
fn oom() -> ! {
    crate::lean_internal_panic(sem::panic::InternalPanic::OutOfMemory)
}

/// The size of a block with room for `cap` elements, rounded up to a
/// multiple of 8 (mimalloc's blocks are: the rounding costs nothing and
/// becomes capacity).
#[inline(always)]
fn bytes_for<T>(cap: usize) -> usize {
    match cap.checked_mul(size_of::<T>()).and_then(|b| b.checked_add(HDR + 7)) {
        Some(b) => b & !7,
        None => oom(),
    }
}

/// The room in a block of `bytes` bytes.
#[inline(always)]
fn cap_of<T>(bytes: usize) -> usize {
    (bytes - HDR) / size_of::<T>()
}

/// A fresh unique block with room for (at least) `cap` elements, empty.
#[inline(always)]
fn alloc<T: Clone>(cap: usize) -> RVec<T> {
    let bytes = bytes_for::<T>(cap);
    unsafe {
        let o = mi_malloc(bytes) as *mut Hdr;
        if o.is_null() {
            oom();
        }
        std::ptr::write(o, Hdr::new(cap_of::<T>(bytes)));
        RVec::from_raw(o)
    }
}

/// Grow a unique block to room for at least `need` elements, at least
/// doubling (`max(need, 2 * cap, 8)`, so pushes are amortized O(1)). The
/// capacity is the whole block: mimalloc's size class for small blocks
/// (`alloc::good_size`), a power of two beyond 4 KiB (with
/// the header added to a power of two, large blocks would fall just past
/// mimalloc's size steps, and realloc copies a block's whole usable size).
#[cold]
#[inline(never)]
extern "C" fn grow<T: Clone>(v: RVec<T>, need: usize) -> RVec<T> {
    debug_assert!(v.is_unique());
    // The block moves: the unique handle is given up for the result.
    let o = v.into_raw();
    unsafe {
        let want = need.max((*o).cap.saturating_mul(2)).max(8);
        let b = bytes_for::<T>(want);
        let bytes = if b > 4096 { b.checked_next_power_of_two().unwrap_or(b) } else { crate::alloc::good_size(b) };
        // `bytes >= b >= HDR + want * size`: the capacity is at least
        // `want`; realloc keeps the header and the `len` elements.
        let n = mi_realloc(o as *mut c_void, bytes) as *mut Hdr;
        if n.is_null() {
            oom();
        }
        (*n).cap = cap_of::<T>(bytes);
        RVec::from_raw(n)
    }
}

/// Clones of `src` written to `dst` (uninitialized room for them).
trait CloneInto: Sized {
    unsafe fn clone_to(src: &[Self], dst: *mut Self);
}

impl<T: Clone> CloneInto for T {
    #[inline(always)]
    default unsafe fn clone_to(src: &[T], dst: *mut T) {
        if !std::mem::needs_drop::<T>() {
            // The element types without drop glue are plain data
            // (integers, floats, `bool`, enumeration indices): a clone is
            // the bits. Every counted type (handles, records) has a `Drop`.
            std::ptr::copy_nonoverlapping(src.as_ptr(), dst, src.len());
        } else {
            for (i, x) in src.iter().enumerate() {
                std::ptr::write(dst.add(i), x.clone());
            }
        }
    }
}

/// A Reussir record crossing the boundary is `Bridge<Inner>`, a pointer to
/// its box, and `Clone` is the compiler-emitted `<record>_ffi_acquire`, an
/// `rc.inc` (inlined into the copy loop). Under the aarch64 encoding of
/// nullary variants (TBI) a nullary constructor is an immediate whose top
/// byte is a tag and whose address is a static dummy box shared by all of
/// them, and `rc.inc` increments its count unguarded: copying an array full
/// of `nil`s (hash map buckets) made all those increments one serial chain
/// through a single word. The dummy's count is never decremented (Reussir
/// steers decrements of immediates away) and never frees, so these
/// increments are skipped here; real boxes are incremented as `rc.inc` does
/// (the 32-bit count at offset 0; these records are not atomic). The
/// `immortal` encoding (other targets, and aarch64 under
/// `--nullary-variant-encoding arch-independent`) makes an immediate the
/// plain address of its dummy, whose count is `drop::IMMORTAL` or more and
/// stays as it is, as Reussir's own increment leaves it (review HRT-04): the
/// loop adds `c < IMMORTAL` to the count it loads, without a branch, and so
/// stores a dummy's count back unchanged (the dummy is a writable global).
/// Other targets: the generic clone.
impl<X: Clone> CloneInto for reussir_rt::bridge::Bridge<X> {
    #[inline(always)]
    unsafe fn clone_to(src: &[Self], dst: *mut Self) {
        if cfg!(target_arch = "aarch64") && size_of::<Self>() == 8 {
            let mut scratch: u32 = 0;
            for x in src {
                let p = std::mem::transmute_copy::<Self, *mut u32>(x);
                let q = if (p as usize) >> 56 == 0 { p } else { &mut scratch as *mut u32 };
                let c = *q;
                *q = c + (c < crate::drop::IMMORTAL) as u32;
            }
            std::hint::black_box(scratch);
            std::ptr::copy_nonoverlapping(src.as_ptr(), dst, src.len());
        } else {
            for (i, x) in src.iter().enumerate() {
                std::ptr::write(dst.add(i), x.clone());
            }
        }
    }
}

/// A box (`any::LAny`): the words are copied as they are (`memcpy`), then
/// each pointer's payload count goes up, as `LAny`'s `Clone` does it; an
/// immediate needs nothing. (The generic loop cloned and stored each box in
/// turn.)
impl CloneInto for crate::any::LAny {
    #[inline(always)]
    unsafe fn clone_to(src: &[Self], dst: *mut Self) {
        std::ptr::copy_nonoverlapping(src.as_ptr(), dst, src.len());
        for x in src {
            let w = x.word();
            if !crate::any::is_imm(w) {
                let p = crate::any::addr_of(w) as *mut u32;
                let c = *p;
                std::hint::assert_unchecked(c != 0);
                *p = c + 1;
            }
        }
    }
}

/// A fresh unique block holding clones of `s`, with room for `extra` more.
#[inline(always)]
fn clone_of_slice<T: Clone>(s: &[T], extra: usize) -> RVec<T> {
    let cap = match s.len().checked_add(extra) {
        Some(c) => c,
        None => oom(),
    };
    let c = alloc::<T>(cap);
    unsafe {
        <T as CloneInto>::clone_to(s, elems::<T>(c.hdr()));
        (*c.hdr()).len = s.len();
    }
    c
}

/// A private copy of a shared array (with room for `extra` more), releasing
/// the shared one.
#[cold]
#[inline(never)]
extern "C" fn copy_shared<T: Clone>(v: RVec<T>, extra: usize) -> RVec<T> {
    let c = clone_of_slice(v.as_slice(), extra);
    drop(v);
    c
}

/// Unique access with room for `extra` more elements: a shared array is
/// copied first, a full one grown.
#[inline(always)]
pub fn make_mut<T: Clone>(v: &mut RVec<T>, extra: usize) -> *mut Hdr {
    // By value: the address of `v` (often a local of the Reussir caller once
    // this is inlined) must not escape, or tail calls are lost.
    if !v.is_unique() {
        unsafe { std::ptr::write(v, copy_shared(std::ptr::read(v), extra)) };
    } else if extra > 0 {
        let o = v.hdr();
        let need = match unsafe { (*o).len }.checked_add(extra) {
            Some(n) => n,
            None => oom(),
        };
        if need > unsafe { (*o).cap } {
            unsafe { std::ptr::write(v, grow(std::ptr::read(v), need)) };
        }
    }
    v.hdr()
}

/// Give up an array handle that a texture received (every FFI call
/// consumes its arguments): a decrement, the last reference freed out of
/// line (`RVec`'s `Drop`), so textures stay small enough for LLVM to inline
/// into Reussir code.
#[inline(always)]
pub fn release<T: Clone>(v: RVec<T>) {
    drop(v)
}

#[inline(always)]
pub fn as_slice<T: Clone>(v: &RVec<T>) -> &[T] {
    v.as_slice()
}

/// An index that the Lean-level proof (or the prelude's bounds check)
/// guarantees to be in range was not: a lean2rr/runtime bug. Also the
/// failing branch of the prelude's reads (`l2r_array_index_bug`).
#[cold]
#[inline(never)]
pub extern "C" fn index_bug(i: u64, n: usize) -> ! {
    crate::internal_panic(&format!("array index {} out of bounds {} (runtime invariant)", i, n))
}

#[inline]
pub fn with_capacity<T: Clone>(n: usize) -> RVec<T> {
    alloc(n)
}

/// Allocations of more elements than this are checked against what the
/// native allocation would do (`check_alloc_slow`, `capacity_slow`) first.
pub const CHECK_THRESHOLD: u64 = 1 << 24;

/// Lean's allocation of an array object of `n` elements of `elem` bytes
/// (`lean_alloc_array`, `lean_alloc_sarray`): lean-runtime's size rule
/// (`sem::array::alloc_bytes`: `24 + elem * n` bytes, an overflow being the
/// internal panic `integer overflow in runtime computation`), then a failed
/// `malloc` is `out of memory`.
#[inline(always)]
pub fn check_alloc(n: u64, elem: u64) {
    if n > CHECK_THRESHOLD {
        check_alloc_slow(n, elem)
    }
}

/// The capacity to reserve for `Array.mkEmpty n` and `emptyWithCapacity n`
/// (`elem` bytes per element): lean-runtime's rule for it
/// (`sem::array::empty_with_capacity`: `n`, or 0 when the object size
/// `24 + elem * n` is above 2^64 - 1 or `isize::MAX`, every `n` of 2^63 or
/// more among them), then 0 too when the native allocation of that size
/// would fail. The capacity is only a hint: the Lean definitions give the
/// empty array whatever `n` is, so no capacity ends the process
/// (lean-runtime's LB-37; natively `out of memory` or `integer overflow in
/// runtime computation`).
#[inline(always)]
pub fn check_capacity(n: u64, elem: u64) -> usize {
    if n > CHECK_THRESHOLD {
        capacity_slow(n, elem)
    } else {
        n as usize
    }
}

#[cold]
#[inline(never)]
extern "C" fn check_alloc_slow(n: u64, elem: u64) {
    match sem::array::alloc_bytes(elem, n) {
        Err(p) => crate::lean_internal_panic(p),
        Ok(bytes) if !native_alloc_ok(bytes) => {
            crate::lean_internal_panic(sem::panic::InternalPanic::OutOfMemory)
        }
        Ok(_) => {}
    }
}

#[cold]
#[inline(never)]
extern "C" fn capacity_slow(n: u64, elem: u64) -> usize {
    match sem::array::empty_with_capacity(elem, n) {
        0 => 0,
        // `empty_with_capacity` has checked that this does not overflow.
        c if native_alloc_ok(sem::array::ARRAY_HEADER_BYTES + elem * c as u64) => c,
        _ => 0,
    }
}

/// Would the native allocation of an object of `bytes` bytes succeed? It is
/// only reserved, not touched, so this costs no memory.
fn native_alloc_ok(bytes: u64) -> bool {
    // Lean allocates big objects with mimalloc too.
    extern "C" {
        #[link_name = "mi_malloc"]
        fn malloc(n: usize) -> *mut std::ffi::c_void;
        #[link_name = "mi_free"]
        fn free(p: *mut std::ffi::c_void);
    }
    // `black_box` keeps the compiler from eliding the malloc/free pair.
    let p = std::hint::black_box(unsafe { malloc(std::hint::black_box(bytes as usize)) });
    if p.is_null() {
        return false;
    }
    unsafe { free(p) };
    true
}

/// `Array.mkEmpty n` (and the scalar-array variants, `elem` bytes per
/// element): the capacity `check_capacity` gives, as natively (reserved
/// address space: untouched pages cost no memory), or none.
#[inline(never)]
pub fn with_capacity_checked<T: Clone>(n: u64, elem: u64) -> RVec<T> {
    alloc(check_capacity(n, elem))
}

#[inline]
pub fn empty<T: Clone>() -> RVec<T> {
    alloc(0)
}

#[inline(always)]
pub fn size<T: Clone>(v: &RVec<T>) -> u64 {
    v.len() as u64
}

/// Element `i`, which must be in bounds.
#[inline(always)]
pub fn get<T: Clone>(v: &RVec<T>, i: u64) -> T {
    let s = v.as_slice();
    match s.get(i as usize) {
        Some(x) => x.clone(),
        None => index_bug(i, s.len()),
    }
}

/// The first step of every read (the prelude's `l2r_array_give`): the
/// caller gives up its handle, which the read received (every FFI call
/// consumes its arguments), before anything else, and gets a view of the
/// array: the block's address, with bit 0 set when the array is shared.
///
/// A shared array (count above 1) is decremented now: another reference
/// keeps the block and its elements alive until the read's end (one thread
/// runs Lean code, and nothing else runs until `view_take` or `view_end`).
/// One exception: `get!` out of bounds (the prelude's `lean_array_get`)
/// panics between the give and `view_end`, as natively (review HA-01), and
/// the message goes to the current stderr stream, which `IO.setStderr` may
/// have made a stream of Lean functions: Lean code can run there and drop
/// the reference that keeps a shared array alive. So nothing reads through
/// a view after a panic: `view_end` of a shared view reads nothing, and the
/// last reference's view is the read's own.
/// So no call and no other store come between the caller's increment and
/// this decrement on any path (the bounds check and its panic come after),
/// and LLVM removes both. The last reference keeps its count of 1, and
/// `view_take`/`view_end` free the block. Bit 0 is set for the shared
/// case, not the last reference: after the caller's increment, LLVM sees
/// a shared view `o | 1`, and the test of bit 0 folds (it does not know
/// that the address `o` is even, which a set bit for the last reference
/// would need).
#[inline(always)]
pub fn give<T: Clone>(v: RVec<T>) -> u64 {
    let o = v.into_raw();
    unsafe {
        let c = (*o).count;
        if c != 1 {
            (*o).count = c - 1;
            o as u64 | 1
        } else {
            o as u64
        }
    }
}

#[inline(always)]
fn view_block(p: u64) -> *mut Hdr {
    (p & !1) as *mut Hdr
}

/// The size of the array of a view (`give`).
///
/// # Safety
/// `p` is a view from `give` that neither `view_take` nor `view_end` has
/// ended.
#[inline(always)]
pub unsafe fn view_size(p: u64) -> u64 {
    unsafe { (*view_block(p)).len as u64 }
}

/// Element `i` of the array of a view, which ends here: the block is freed
/// out of line (`drop::free_vec`, as `release` does) when the view holds
/// the last reference (bit 0 clear). The element is cloned in line on both
/// paths, so that a release of the element later in the caller cancels
/// against the clone; the free is the one cold call.
///
/// # Safety
/// `p` is a view from `give` that neither `view_take` nor `view_end` has
/// ended, and `i` is below its size (the caller's check).
#[inline(always)]
pub unsafe fn view_take<T: Clone>(p: u64, i: u64) -> T {
    let o = view_block(p);
    unsafe {
        debug_assert!((i as usize) < (*o).len);
        let r = (*elems::<T>(o).add(i as usize)).clone();
        if (p & 1) == 0 {
            crate::drop::free_vec::<T>(o);
        }
        r
    }
}

/// The end of a view without a read (`get!` out of bounds): the block is
/// freed when the view holds the last reference.
///
/// # Safety
/// `p` is a view from `give` that neither `view_take` nor `view_end` has
/// ended.
#[inline(always)]
pub unsafe fn view_end<T: Clone>(p: u64) {
    if (p & 1) == 0 {
        crate::drop::free_vec::<T>(view_block(p));
    }
}

/// `push`: in place when unique with spare capacity; otherwise grow or copy
/// out of line.
#[inline(always)]
pub fn push<T: Clone>(v: RVec<T>, x: T) -> RVec<T> {
    if v.is_unique() {
        let o = v.hdr();
        unsafe {
            let n = (*o).len;
            if n < (*o).cap {
                std::ptr::write(elems::<T>(o).add(n), x);
                (*o).len = n + 1;
                return v;
            }
        }
    }
    push_slow(v, x)
}

/// `push` when shared or full. A shared array is copied with the capacity
/// `lean_array_push` gives it (its own, unless that is below `2 * size + 1`:
/// then `(capacity + 1) * 2`), so a literal pushing onto a shared empty
/// array of capacity `k` allocates a block of `k` elements once.
#[cold]
#[inline(never)]
extern "C" fn push_slow<T: Clone>(mut v: RVec<T>, x: T) -> RVec<T> {
    let n = v.len();
    let extra = if v.is_unique() {
        n.max(4)
    } else {
        let cap = unsafe { (*v.hdr()).cap };
        let want = if cap < 2 * n + 1 { (cap + 1) * 2 } else { cap };
        want.max(n + 1) - n
    };
    let o = make_mut(&mut v, extra);
    unsafe {
        std::ptr::write(elems::<T>(o).add(n), x);
        (*o).len = n + 1;
    }
    v
}

/// How a set or a pop releases the element it removes, as `lean_dec` does
/// natively (`lean_array_uset`, `lean_array_pop`): by default the element's
/// own drop, in line (a handle's decrement, its free out of line). A Reussir
/// record (`Bridge`, see `CloneInto`) has only its decrement in line, as
/// `rc.dec` does it: a count above 1 is decremented here, and the last
/// reference goes to `release_last`, out of line, which frees the record
/// as `drop::release` does (`drop::release_unique`, without testing the
/// count again): inside a free the runtime starts, so its
/// fields go in Lean's order, its last field first, and the `sync`
/// dependents of the promises it drops unresolved run when that free ends,
/// before the set returns (the record's own `_ffi_release`, which the set
/// called before, releases the first cell's fields in field order; review
/// RS10-01: a structure of two handles closed them in the opposite order to
/// native's). The decrement is `rc.dec`'s, as the increments of
/// `CloneInto` are `rc.inc`'s and the array free's decrements are
/// (`drop::ReleaseElems`): the 32-bit count at offset 0 (these records are
/// not atomic); an immediate (a nullary constructor under the aarch64
/// encoding, a nonzero top byte) has no count of its own and is never
/// decremented (`rc.dec` steers away from it). On other targets (the
/// immortal encoding) every record goes to `release_last`.
///
/// With the record's release in the texture (its fields' decrements and
/// frees, `__reussir_deallocate`), the set texture was too big for LLVM to
/// inline into Reussir code (an instruction-count profile: unionfind's
/// `l2r_array_set<nodeData>`, 6.9 % of its instructions, about 12 of 29 per
/// call the call's own cost); now it is inlined. A set that frees the
/// replaced record pays for the free the runtime starts, with the record
/// as one pending cell (`drop::free_unique`): about 74 instructions
/// (cachegrind: Reussir's `drain_one` 26, `__reussir_drop_drain` 18,
/// `__reussir_drop_defer` 17, `release_last` 7, `drop::release_record` 6
/// with the record's own free), as a reference set that frees its old
/// value does (`l2r_rc_set`).
trait ReleaseElem: Sized {
    unsafe fn release_elem(x: Self);
}

impl<T> ReleaseElem for T {
    #[inline(always)]
    default unsafe fn release_elem(x: T) {
        drop(x)
    }
}

impl<X> ReleaseElem for reussir_rt::bridge::Bridge<X> {
    #[inline(always)]
    unsafe fn release_elem(x: Self) {
        if cfg!(target_arch = "aarch64") && size_of::<Self>() == 8 {
            let p = std::mem::transmute_copy::<Self, *mut u32>(&x);
            if (p as usize) >> 56 != 0 {
                // An immediate (`tbi`).
                std::mem::forget(x);
                return;
            }
            let c = *p;
            if c != 1 {
                // Shared; an immediate's dummy (`immortal`) stays as it is
                // (`drop::IMMORTAL`).
                if c < crate::drop::IMMORTAL {
                    *p = c - 1;
                }
                std::mem::forget(x);
                return;
            }
        }
        release_last(x)
    }
}

/// The last reference to an element that a set or a pop removes (or any
/// record on a target without the aarch64 encoding): freed inside a free
/// the runtime starts (`drop::release_unique`: the count, found at 1 by
/// `ReleaseElem`, is not tested again). `extern "C"`: the free may unwind,
/// and a Rust call would be an invoke with a landing pad in the texture,
/// which then stayed a call at six sites of `RtArraySets`.
#[cold]
#[inline(never)]
extern "C" fn release_last<T>(x: T) {
    unsafe { crate::drop::release_unique(x) }
}

/// Replace element `i` of the unique block `o` (in bounds: else a runtime
/// bug), releasing the old one first, as `lean_array_uset` (`ReleaseElem`).
#[inline(always)]
unsafe fn set_in<T>(o: *mut Hdr, i: u64, x: T) {
    let n = (*o).len;
    if (i as usize) >= n {
        index_bug(i, n);
    }
    let slot = elems::<T>(o).add(i as usize);
    <T as ReleaseElem>::release_elem(std::ptr::read(slot));
    std::ptr::write(slot, x);
}

/// Replace element `i` (in bounds): in place when unique.
#[inline(always)]
pub fn set<T: Clone>(v: RVec<T>, i: u64, x: T) -> RVec<T> {
    if v.is_unique() {
        unsafe { set_in(v.hdr(), i, x) };
        return v;
    }
    set_slow(v, i, x)
}

#[cold]
#[inline(never)]
extern "C" fn set_slow<T: Clone>(mut v: RVec<T>, i: u64, x: T) -> RVec<T> {
    let o = make_mut(&mut v, 0);
    unsafe { set_in(o, i, x) };
    v
}

/// Remove the last element of the unique block `o` (non-empty) and release
/// it, as `lean_array_pop` (`ReleaseElem`).
#[inline(always)]
unsafe fn pop_in<T>(o: *mut Hdr) {
    let n = (*o).len - 1;
    (*o).len = n;
    <T as ReleaseElem>::release_elem(std::ptr::read(elems::<T>(o).add(n)));
}

/// Drop the last element (no-op when empty).
#[inline(always)]
pub fn pop<T: Clone>(v: RVec<T>) -> RVec<T> {
    if v.len() == 0 {
        return v;
    }
    if v.is_unique() {
        unsafe { pop_in::<T>(v.hdr()) };
        return v;
    }
    pop_slow(v)
}

#[cold]
#[inline(never)]
extern "C" fn pop_slow<T: Clone>(mut v: RVec<T>) -> RVec<T> {
    let o = make_mut(&mut v, 0);
    unsafe { pop_in::<T>(o) };
    v
}

/// Swap elements `i` and `j` (both in bounds).
#[inline(always)]
pub fn swap<T: Clone>(v: RVec<T>, i: u64, j: u64) -> RVec<T> {
    let n = v.len();
    if (i as usize) >= n || (j as usize) >= n {
        index_bug(i.max(j), n);
    }
    if v.is_unique() {
        let e = unsafe { elems::<T>(v.hdr()) };
        unsafe { std::ptr::swap(e.add(i as usize), e.add(j as usize)) };
        return v;
    }
    swap_slow(v, i, j)
}

#[cold]
#[inline(never)]
extern "C" fn swap_slow<T: Clone>(mut v: RVec<T>, i: u64, j: u64) -> RVec<T> {
    let o = make_mut(&mut v, 0);
    unsafe {
        let e = elems::<T>(o);
        std::ptr::swap(e.add(i as usize), e.add(j as usize));
    }
    v
}

/// `Array.replicate n x`: `n - 1` clones of `x`, then `x` itself.
#[inline(never)]
pub fn replicate<T: Clone>(n: u64, x: T) -> RVec<T> {
    check_alloc(n, 8);
    let v = alloc::<T>(n as usize);
    if n == 0 {
        drop(x);
        return v;
    }
    let o = v.hdr();
    unsafe {
        let e = elems::<T>(o);
        for i in 0..n as usize - 1 {
            std::ptr::write(e.add(i), x.clone());
            (*o).len = i + 1;
        }
        std::ptr::write(e.add(n as usize - 1), x);
        (*o).len = n as usize;
    }
    v
}

/// Drop elements from index `n` on, the last first, each as `pop` drops it
/// (natively a loop of `Array.pop`, `lean_array_pop`; review HA-01's note:
/// it released them first to last). The prelude's `l2r_array_truncate`,
/// which generated code does not call.
#[inline]
pub fn truncate<T: Clone>(v: RVec<T>, n: u64) -> RVec<T> {
    if (n as usize) >= v.len() {
        return v;
    }
    let mut v = v;
    let o = make_mut(&mut v, 0);
    unsafe {
        while (*o).len > n as usize {
            pop_in::<T>(o);
        }
    }
    v
}

/// `a ++ b`.
#[inline(never)]
pub fn append<T: Clone>(a: RVec<T>, b: RVec<T>) -> RVec<T> {
    let k = b.len();
    if k == 0 {
        return a;
    }
    let mut a = a;
    // When `a` and `b` are the same array its count is at least 2, so
    // `make_mut` copies it: `b`'s block is never the one written.
    let o = make_mut(&mut a, k);
    unsafe {
        let n = (*o).len;
        <T as CloneInto>::clone_to(b.as_slice(), elems::<T>(o).add(n));
        (*o).len = n + k;
    }
    a
}

/// Elements `[start, stop)` (clamped), for `Array.extract`-like primitives.
#[inline(never)]
pub fn extract<T: Clone>(v: RVec<T>, start: u64, stop: u64) -> RVec<T> {
    let s = v.as_slice();
    let stop = (stop as usize).min(s.len());
    let start = (start as usize).min(stop);
    if start == 0 && stop == s.len() {
        return v;
    }
    clone_of_slice(&s[start..stop], 0)
}

/// Reverse in place.
#[inline(never)]
pub fn reverse<T: Clone>(v: RVec<T>) -> RVec<T> {
    let mut v = v;
    let o = make_mut(&mut v, 0);
    unsafe { std::slice::from_raw_parts_mut(elems::<T>(o), (*o).len).reverse() };
    v
}

/// An array of the elements of `v`, moved (one copy of the bits).
#[inline]
pub fn from_vec<T: Clone>(v: Vec<T>) -> RVec<T> {
    let mut v = std::mem::ManuallyDrop::new(v);
    let n = v.len();
    let a = alloc::<T>(n);
    unsafe {
        std::ptr::copy_nonoverlapping(v.as_ptr(), elems::<T>(a.hdr()), n);
        (*a.hdr()).len = n;
        // The elements moved: free `v`'s buffer only.
        v.set_len(0);
        std::mem::ManuallyDrop::drop(&mut v);
    }
    a
}

/// An array of clones of `s`.
#[inline]
pub fn from_slice<T: Clone>(s: &[T]) -> RVec<T> {
    clone_of_slice(s, 0)
}

/// A byte array of room `n` whose bytes `fill(p, n)` writes at `p`,
/// answering how many (at most `n`; an error frees the block). For
/// readers (`Handle.read`, `IO.getRandomBytes`): the bytes land in the
/// array itself, as natively, instead of a buffer copied afterwards (which
/// doubled the peak of reading a file, RVA-01).
#[inline]
pub fn bytes_filled<E>(n: usize, fill: impl FnOnce(*mut u8, usize) -> Result<usize, E>) -> Result<RVec<u8>, E> {
    let a = alloc::<u8>(n);
    let got = fill(unsafe { elems::<u8>(a.hdr()) }, n)?;
    if got > n {
        crate::internal_panic("byte array filled past its room (runtime invariant)");
    }
    unsafe { (*a.hdr()).len = got };
    Ok(a)
}

// ---- byte arrays and strings -----------------------------------------------

/// A byte vector as a `ByteArray` (a copy).
#[inline]
pub fn bytes_of_vec(v: Vec<u8>) -> RVec<u8> {
    from_slice(&v)
}

/// `String.toUTF8`: a copy of the bytes, as natively.
#[inline(never)]
pub fn bytes_of_string(s: crate::string::LStr) -> RVec<u8> {
    use crate::string::Utf8;
    let b = from_slice(s.utf8());
    crate::rc_release(s);
    b
}

/// `String.fromUTF8` of valid UTF-8 (counting the characters): a copy of
/// the bytes, as natively.
#[inline(never)]
pub fn string_of_bytes(b: RVec<u8>) -> crate::string::LStr {
    let s = crate::string::from_bytes(b.as_slice());
    drop(b);
    s
}

/// `ByteArray.copySlice src srcOff dest destOff len exact`, as lean-runtime's
/// plan (`sem::array::copy_slice`); the offsets and the length are taken
/// saturated (`u64::MAX` for 2^64 or more: LB-06 lifted). `exact` only
/// chooses the capacity of a grown result natively; here a grown block gets
/// `make_mut`'s.
#[inline(never)]
pub fn copy_slice(src: RVec<u8>, src_off: u64, dest: RVec<u8>, dest_off: u64, len: u64, exact: bool) -> RVec<u8> {
    let _ = exact;
    let dsz = dest.len();
    let Some(plan) = sem::array::copy_slice(src.len(), src_off, dsz, dest_off, len) else {
        return dest;
    };
    let mut dest = dest;
    // When `src` and `dest` are the same array its count is at least 2, so
    // `make_mut` copies it: the bytes are read from `src`'s own block.
    let o = make_mut(&mut dest, plan.new_len - dsz);
    unsafe {
        let d = elems::<u8>(o);
        std::ptr::write_bytes(d.add(dsz), 0, plan.new_len - dsz);
        std::ptr::copy(elems::<u8>(src.hdr()).add(plan.src_start), d.add(plan.dest_start), plan.len);
        (*o).len = plan.new_len;
    }
    dest
}

// ---- `ByteArray`/`FloatArray` and `Array UInt8`/`Array Float` ---------------
//
// `ByteArray.data`, `ByteArray.mk`, `FloatArray.data`, `FloatArray.mk`
// (`lean_byte_array_data`, ...): a new array of exactly the source's size
// (natively `lean_alloc_array(n, n)`, `lean_alloc_sarray(.., n, n)`), the
// elements converted in one loop, then the source released. An `Array`
// holds boxes (`LAny`, rule 1) unless lean2rr stores it compactly (an
// `RVec` of its scalars: `RVec<u8>` and `RVec<f64>` as here, `RVec<u16>`,
// `RVec<u32>`, `RVec<u64>`, `RVec<f32>`; `any::NUM_BYTES` to
// `any::NUM_F32S`).

/// `ByteArray.data`: each byte as its box, an immediate.
#[inline(never)]
pub fn boxes_of_bytes(src: RVec<u8>) -> RVec<crate::any::LAny> {
    let n = src.len();
    check_alloc(n as u64, 8);
    let v = alloc::<crate::any::LAny>(n);
    unsafe {
        let s = elems::<u8>(src.hdr());
        let d = elems::<u64>(v.hdr());
        for i in 0..n {
            *d.add(i) = ((*s.add(i) as u64) << 1) | 1;
        }
        (*v.hdr()).len = n;
    }
    drop(src);
    v
}

/// `ByteArray.mk`: each box read as a `UInt8` (`l2r_any_as_u8`: an
/// immediate's value, truncated; a pointer is `any::mismatch`, a panic, as
/// the generated unboxing in a program without casts). One pass that also
/// gathers the words' low bits (vectorized): a pointer is found after it.
#[inline(never)]
pub fn bytes_of_boxes(src: RVec<crate::any::LAny>) -> RVec<u8> {
    let n = src.len();
    let v = alloc::<u8>(n);
    unsafe {
        let s = elems::<u64>(src.hdr());
        let d = elems::<u8>(v.hdr());
        let mut all = 1u64;
        for i in 0..n {
            let w = *s.add(i);
            all &= w;
            *d.add(i) = (w >> 1) as u8;
        }
        if all & 1 == 0 {
            not_immediates(src.as_slice());
        }
        (*v.hdr()).len = n;
    }
    drop(src);
    v
}

/// A pointer among boxes read as scalars: the generated unboxing's panic
/// (`any::mismatch`) for the first one.
#[cold]
#[inline(never)]
fn not_immediates(s: &[crate::any::LAny]) -> ! {
    let w = s.iter().map(|a| a.word()).find(|w| w & 1 == 0).unwrap_or(0);
    crate::any::mismatch(w, 0)
}

/// Whether every box is an immediate (what `bytes_of_boxes` reads without
/// a panic): in a program that casts, a pointer is read by the generated
/// cast instead (`l2r_unbox_u8`).
#[inline(never)]
pub fn boxes_all_imm(src: RVec<crate::any::LAny>) -> bool {
    let all = unsafe {
        let s = elems::<u64>(src.hdr());
        (0..src.len()).fold(1u64, |a, i| a & *s.add(i))
    };
    drop(src);
    all & 1 == 1
}

/// `FloatArray.data`: each float in its box, a cell (`any::of_f64`), as
/// natively (`lean_box_float`).
#[inline(never)]
pub fn boxes_of_floats(src: RVec<f64>) -> RVec<crate::any::LAny> {
    let n = src.len();
    check_alloc(n as u64, 8);
    let v = alloc::<crate::any::LAny>(n);
    unsafe {
        let s = elems::<f64>(src.hdr());
        let d = elems::<crate::any::LAny>(v.hdr());
        for i in 0..n {
            std::ptr::write(d.add(i), crate::any::of_f64(*s.add(i)));
            // The block holds exactly the boxes made so far (a cell's
            // allocation can end the process, never unwind).
            (*v.hdr()).len = i + 1;
        }
    }
    drop(src);
    v
}

/// `FloatArray.mk`: each box read as a `Float` (`l2r_any_as_f64`: a float's
/// or a large `UInt64`'s cell gives its bits, an immediate its value's
/// bits, `box(0)` 0.0; any other pointer is `any::mismatch`), the boxes
/// read in place and released with the source.
#[inline(never)]
pub fn floats_of_boxes(src: RVec<crate::any::LAny>) -> RVec<f64> {
    let n = src.len();
    let v = alloc::<f64>(n);
    unsafe {
        let s = elems::<u64>(src.hdr());
        let d = elems::<f64>(v.hdr());
        for i in 0..n {
            *d.add(i) = f64::from_bits(crate::any::bits_of_word(*s.add(i)));
        }
        (*v.hdr()).len = n;
    }
    drop(src);
    v
}

/// A scalar that a compact array stores, boxed as lean2rr boxes a value of
/// its Lean types (`LowerBase.boxValue`): `UInt8`, `Bool`, an enumeration's
/// index (`u8`), `UInt16`, `UInt32` and `Char` as immediates; a `Float32`'s
/// bits as an immediate (the prelude's `l2r_any_of_f32`); a `UInt64` or
/// `USize` as `any::of_u64` (a cell from 2^63); a `Float` as `any::of_f64`
/// (a cell).
pub trait BoxScalar: Clone + Copy {
    fn boxed(self) -> crate::any::LAny;
}

impl BoxScalar for u8 {
    #[inline(always)]
    fn boxed(self) -> crate::any::LAny {
        crate::any::LAny::imm(self as u64)
    }
}

impl BoxScalar for u16 {
    #[inline(always)]
    fn boxed(self) -> crate::any::LAny {
        crate::any::LAny::imm(self as u64)
    }
}

impl BoxScalar for u32 {
    #[inline(always)]
    fn boxed(self) -> crate::any::LAny {
        crate::any::LAny::imm(self as u64)
    }
}

impl BoxScalar for f32 {
    #[inline(always)]
    fn boxed(self) -> crate::any::LAny {
        crate::any::LAny::imm(self.to_bits() as u64)
    }
}

impl BoxScalar for u64 {
    #[inline(always)]
    fn boxed(self) -> crate::any::LAny {
        crate::any::of_u64(self)
    }
}

impl BoxScalar for f64 {
    #[inline(always)]
    fn boxed(self) -> crate::any::LAny {
        crate::any::of_f64(self)
    }
}

/// A compact array of scalars as an array of boxes (`BoxScalar`): a new
/// array of exactly the source's size, then the source released, as
/// `boxes_of_bytes` and `boxes_of_floats` (the same boxes at `u8` and
/// `f64`). The safety net of `any`'s unboxing at `RVec<LAny>`
/// (`any::boxes_of_compact`).
#[inline(never)]
pub fn boxes_of_scalars<T: BoxScalar>(src: RVec<T>) -> RVec<crate::any::LAny> {
    let n = src.len();
    check_alloc(n as u64, 8);
    let v = alloc::<crate::any::LAny>(n);
    unsafe {
        let s = elems::<T>(src.hdr());
        let d = elems::<crate::any::LAny>(v.hdr());
        for i in 0..n {
            std::ptr::write(d.add(i), (*s.add(i)).boxed());
            // The block holds exactly the boxes made so far (a cell's
            // allocation can end the process, never unwind).
            (*v.hdr()).len = i + 1;
        }
    }
    drop(src);
    v
}

/// Whether every box is one `floats_of_boxes` reads without a panic (an
/// immediate, a float's or a large `UInt64`'s cell): in a program that
/// casts, another pointer is read by the generated cast instead.
#[inline(never)]
pub fn boxes_all_float_words(src: RVec<crate::any::LAny>) -> bool {
    let r = src.as_slice().iter().all(|a| crate::any::is_word_box(a.word()));
    drop(src);
    r
}

// ---- reference cells (`LRef`) -----------------------------------------------
//
// A 0-or-1 element array of capacity 1 or more, mutated in place through
// every alias (not copy-on-write). Not used by generated code any more.

/// A cell holding `v`.
#[inline(never)]
pub fn ref_new<T: Clone>(v: T) -> RVec<T> {
    push(alloc(1), v)
}

/// An empty cell.
#[inline(never)]
pub fn ref_empty<T: Clone>() -> RVec<T> {
    alloc(1)
}

/// The value of a cell (a new reference).
#[inline(never)]
pub fn ref_get<T: Clone>(r: RVec<T>) -> T {
    r.as_slice().first().cloned().expect("leanrt: read of an empty ST.Ref (after take)")
}

/// Whether a cell is empty.
#[inline(never)]
pub fn ref_is_empty<T: Clone>(r: RVec<T>) -> bool {
    r.len() == 0
}

/// Store `v` in a cell and give back its old value (if any), in place.
#[inline(always)]
unsafe fn ref_replace<T: Clone>(r: &RVec<T>, v: T) -> Option<T> {
    let o = r.hdr();
    let e = elems::<T>(o);
    let old = if (*o).len == 1 { Some(std::ptr::read(e)) } else { None };
    std::ptr::write(e, v);
    (*o).len = 1;
    old
}

/// `ST.Ref.set`: the old value is released after the new one is stored, as
/// `lean_dec` does (`crate::drop::release`).
#[inline(never)]
pub fn ref_set<T: Clone>(r: RVec<T>, v: T) {
    if let Some(old) = unsafe { ref_replace(&r, v) } {
        crate::drop::release(old);
    }
}

/// `ST.Ref.swap`: store `v`, give back the old value.
#[inline(never)]
pub fn ref_swap<T: Clone>(r: RVec<T>, v: T) -> T {
    unsafe { ref_replace(&r, v) }.expect("leanrt: swap of an empty ST.Ref (after take)")
}

/// `ST.Prim.Ref.take`: move the value out, leaving the cell empty until the
/// next `set` (so the value stays uniquely referenced, as in Lean).
#[inline(never)]
pub fn ref_take<T: Clone>(r: RVec<T>) -> T {
    let o = r.hdr();
    unsafe {
        if (*o).len == 0 {
            panic!("leanrt: take of an empty ST.Ref");
        }
        (*o).len = 0;
        std::ptr::read(elems::<T>(o))
    }
}

/// Whether two cells are the same.
#[inline(never)]
pub fn ref_ptr_eq<T: Clone>(a: RVec<T>, b: RVec<T>) -> bool {
    a.hdr() == b.hdr()
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::RefCell;

    thread_local! {
        static LOG: RefCell<Vec<u32>> = RefCell::new(Vec::new());
    }

    /// An element that logs its releases.
    #[derive(Clone)]
    struct E(u32);

    impl Drop for E {
        fn drop(&mut self) {
            LOG.with(|l| l.borrow_mut().push(self.0));
        }
    }

    fn take_log() -> Vec<u32> {
        LOG.with(|l| std::mem::take(&mut *l.borrow_mut()))
    }

    fn count<T: Clone>(v: &RVec<T>) -> u32 {
        unsafe { (*v.hdr()).count }
    }

    fn cap<T: Clone>(v: &RVec<T>) -> usize {
        unsafe { (*v.hdr()).cap }
    }

    #[test]
    fn layout() {
        assert_eq!(HDR, 24);
        assert_eq!(size_of::<RVec<u8>>(), 8);
        assert_eq!(std::mem::offset_of!(Hdr, count), 0);
        // Rounding to 8 bytes becomes capacity.
        assert_eq!(cap(&with_capacity::<u8>(3)), 8);
        assert_eq!(cap(&with_capacity::<u64>(3)), 3);
        assert_eq!(cap(&empty::<u64>()), 0);
        assert_eq!(cap(&with_capacity::<u32>(1)), 2);
    }

    #[test]
    fn copy_on_write_and_growth() {
        let mut a: RVec<u64> = empty();
        for i in 0..10000 {
            a = push(a, i);
        }
        assert_eq!(size(&a), 10000);
        assert!(cap(&a) >= 10000);
        assert_eq!(get(&a, 9999), 9999);
        let b = a.clone();
        assert_eq!(count(&a), 2);
        let c = set(b, 5, 77); // shared: copied
        assert_eq!(get(&a, 5), 5);
        assert_eq!(get(&c, 5), 77);
        assert_eq!(count(&a), 1);
        assert_eq!(count(&c), 1);
        let c = swap(pop(c), 0, 1);
        assert_eq!(size(&c), 9999);
        assert_eq!(get(&c, 0), 1);
        let d = append(a.clone(), a.clone()); // the same array twice
        assert_eq!(size(&d), 20000);
        assert_eq!(get(&d, 10003), 3);
        assert_eq!(count(&a), 1);
        let e = extract(d, 9998, 10002);
        assert_eq!(e.as_slice(), &[9998, 9999, 0, 1]);
        let e = reverse(truncate(e, 3));
        assert_eq!(e.as_slice(), &[0, 9999, 9998]);
        // A literal: a shared empty array of capacity 3, copied once.
        let lit: RVec<u64> = with_capacity(3);
        let x = push(push(push(lit.clone(), 1), 2), 3);
        assert_eq!(cap(&x), 3);
        assert_eq!(size(&lit), 0);
        let r = replicate(5, 9u64);
        assert_eq!(r.as_slice(), &[9; 5]);
        let r0: RVec<u64> = replicate(0, 9);
        assert_eq!(size(&r0), 0);
        // Bytes: growth by pushes from empty.
        let mut b: RVec<u8> = empty();
        for i in 0..100000u32 {
            b = push(b, i as u8);
        }
        assert_eq!(get(&b, 99999), 99999u32 as u8);
    }

    #[test]
    fn views() {
        // A shared array: `give` decrements now, `view_take` clones the
        // element, and the block stays with the other reference.
        let a = from_vec(vec![E(1), E(2)]);
        let p = give(a.clone());
        assert_eq!(p & 1, 1);
        assert_eq!(count(&a), 1);
        assert_eq!(unsafe { view_size(p) }, 2);
        let x = unsafe { view_take::<E>(p, 1) };
        assert_eq!(x.0, 2);
        assert_eq!(take_log(), Vec::<u32>::new());
        drop(x);
        assert_eq!(take_log(), vec![2]);
        // The last reference: the view holds it, keeping the count of 1;
        // `view_take` clones the element, then frees the block.
        let p = give(a);
        assert_eq!(p & 1, 0);
        assert_eq!(unsafe { (*view_block(p)).count }, 1);
        let y = unsafe { view_take::<E>(p, 0) };
        assert_eq!(take_log(), vec![2, 1]);
        assert_eq!(y.0, 1);
        drop(y);
        assert_eq!(take_log(), vec![1]);
        // `view_end`: nothing more for a shared array, the free for the last
        // reference.
        let c = from_vec(vec![E(5)]);
        unsafe { view_end::<E>(give(c.clone())) };
        assert_eq!(count(&c), 1);
        assert_eq!(take_log(), Vec::<u32>::new());
        unsafe { view_end::<E>(give(c)) };
        assert_eq!(take_log(), vec![5]);
    }

    #[test]
    fn element_releases() {
        let a = from_vec(vec![E(1), E(2), E(3)]);
        assert_eq!(take_log(), Vec::<u32>::new());
        // Copy-on-write clones every element; the set releases the copy's
        // element 1.
        let b = set(a.clone(), 1, E(9));
        assert_eq!(take_log(), vec![2]);
        // Freed from the last element.
        drop(a);
        assert_eq!(take_log(), vec![3, 2, 1]);
        let b = pop(b);
        assert_eq!(take_log(), vec![3]);
        let b = truncate(push(push(b, E(4)), E(5)), 1);
        assert_eq!(take_log(), vec![5, 4, 9]);
        drop(replicate(3, E(7)));
        assert_eq!(take_log(), vec![7, 7, 7]);
        drop(b);
        assert_eq!(take_log(), vec![1]);
        let c: RVec<E> = replicate(0, E(8));
        assert_eq!(take_log(), vec![8]);
        drop(c);
    }

    #[test]
    fn nested_free_order() {
        // An array of arrays is freed through the stack of pending work:
        // the last inner array, its elements from the last, first.
        let inner1 = from_vec(vec![E(1), E(2)]);
        let inner2 = from_vec(vec![E(3), E(4)]);
        let outer = from_vec(vec![inner1, inner2]);
        drop(outer);
        assert_eq!(take_log(), vec![4, 3, 2, 1]);
        // A shared inner array is only decremented.
        let inner = from_vec(vec![E(5)]);
        let outer = from_vec(vec![inner.clone(), inner.clone()]);
        drop(outer);
        assert_eq!(take_log(), Vec::<u32>::new());
        assert_eq!(count(&inner), 1);
        drop(inner);
        assert_eq!(take_log(), vec![5]);
    }

    /// `ByteArray.data`/`mk`, `FloatArray.data`/`mk`: the exact size, the
    /// elements' boxes, the round trips, and what the checks accept.
    #[test]
    fn byte_and_float_array_conversions() {
        use crate::any::{of, of_f64, of_u64, LAny, NUM_STR};
        let b = bytes_of_vec((0..=255u8).collect());
        let d = boxes_of_bytes(b.clone());
        assert_eq!((size(&d), cap(&d)), (256, 256));
        assert!(d.as_slice().iter().enumerate().all(|(i, a)| a.word() == ((i as u64) << 1) | 1));
        assert!(boxes_all_imm(d.clone()));
        let b2 = bytes_of_boxes(d);
        assert_eq!(b2.as_slice(), b.as_slice());
        assert_eq!(cap(&b2), 256);
        assert_eq!(count(&b), 1);
        assert_eq!(size(&boxes_of_bytes(empty())), 0);
        assert_eq!(size(&bytes_of_boxes(empty())), 0);
        let f = from_slice(&[1.5f64, -0.0, f64::INFINITY, f64::NAN, 2.0]);
        let fd = boxes_of_floats(f.clone());
        assert_eq!((size(&fd), cap(&fd)), (5, 5));
        assert!(boxes_all_float_words(fd.clone()));
        let f2 = floats_of_boxes(fd);
        assert!(f2.as_slice().iter().zip(f.as_slice()).all(|(x, y)| x.to_bits() == y.to_bits()));
        // `box(0)`, a `UInt64` immediate and cell, a float cell: their bits.
        let mixed = from_vec(vec![LAny::unit(), of_u64(u64::MAX), of_u64(3), of_f64(0.5)]);
        assert!(boxes_all_float_words(mixed.clone()));
        assert!(!boxes_all_imm(mixed.clone()));
        let fm = floats_of_boxes(mixed);
        assert_eq!(fm.as_slice().iter().map(|x| x.to_bits()).collect::<Vec<_>>(), vec![0, u64::MAX, 3, 0.5f64.to_bits()]);
        let s = from_vec(vec![LAny::imm(1), of(crate::string::from_bytes(b"s"), NUM_STR)]);
        assert!(!boxes_all_imm(s.clone()));
        assert!(!boxes_all_float_words(s));
    }

    /// Every array operation at a scalar element type of the compact
    /// arrays (`u8`, `u16`, `u32`, `u64`, `f32`, `f64`): the elements' bits
    /// kept, and a shared array copied for every update, the other
    /// reference's array unchanged.
    fn scalar_ops<T: Clone + Copy + PartialEq + std::fmt::Debug>(x: [T; 4]) {
        let a = from_slice(&x[..3]);
        assert_eq!((size(&a), a.as_slice()), (3, &x[..3]));
        assert_eq!(get(&a, 2), x[2]);
        let p = give(a.clone());
        assert_eq!((p & 1, unsafe { view_size(p) }), (1, 3));
        assert_eq!(unsafe { view_take::<T>(p, 1) }, x[1]);
        // Updates of a shared array: each one a copy.
        let s = set(a.clone(), 0, x[3]);
        assert_eq!((s.as_slice(), a.as_slice()), (&[x[3], x[1], x[2]][..], &x[..3]));
        let w = swap(a.clone(), 0, 2);
        assert_eq!(w.as_slice(), &[x[2], x[1], x[0]]);
        let q = push(a.clone(), x[3]);
        assert_eq!(q.as_slice(), &x[..]);
        let o = pop(a.clone());
        assert_eq!(o.as_slice(), &x[..2]);
        let r = reverse(a.clone());
        assert_eq!(r.as_slice(), &[x[2], x[1], x[0]]);
        let t = truncate(a.clone(), 1);
        assert_eq!(t.as_slice(), &x[..1]);
        assert_eq!(a.as_slice(), &x[..3]);
        assert_eq!(count(&a), 1);
        // Unique: in place, the same block.
        let h = a.hdr();
        let a = set(a, 1, x[0]);
        let a = swap(a, 0, 2);
        let a = pop(a);
        assert_eq!((a.hdr(), a.as_slice()), (h, &[x[2], x[0]][..]));
        let e = extract(append(a.clone(), q.clone()), 1, 4);
        assert_eq!(e.as_slice(), &[x[0], x[0], x[1]]);
        let m = replicate(3, x[3]);
        assert_eq!(m.as_slice(), &[x[3]; 3]);
        let mut g: RVec<T> = with_capacity_checked(2, 8);
        for i in 0..1000 {
            g = push(g, x[i % 4]);
        }
        assert!((0..1000).all(|i| get(&g, i as u64) == x[i % 4]));
        assert_eq!(size(&empty::<T>()), 0);
        drop((s, w, q, o, r, t, e, m, g));
    }

    #[test]
    fn scalar_element_types() {
        scalar_ops([0u8, 1, 0x7f, 0xff]);
        scalar_ops([0u16, 1, 0x8000, 0xffff]);
        scalar_ops([0u32, 0x10ffff, 0x8000_0000, u32::MAX]);
        scalar_ops([0u64, 1, 1 << 63, u64::MAX]);
        scalar_ops([1.5f32, -0.0, f32::INFINITY, f32::MIN_POSITIVE]);
        scalar_ops([1.5f64, -0.0, f64::INFINITY, f64::MIN_POSITIVE]);
        // NaNs keep their bits.
        let n = from_slice(&[f32::from_bits(0x7fc0_0001), f32::from_bits(0xffc0_0002)]);
        let c = set(n.clone(), 0, 2.0);
        assert_eq!(n.as_slice().iter().map(|x| x.to_bits()).collect::<Vec<_>>(), vec![0x7fc0_0001, 0xffc0_0002]);
        assert_eq!(get(&c, 1).to_bits(), 0xffc0_0002);
    }

    /// A compact array as boxes (`boxes_of_scalars`): the size, each
    /// scalar boxed as lean2rr boxes it, the source released (a shared one
    /// decremented, unchanged).
    #[test]
    fn scalar_arrays_as_boxes() {
        use crate::any::{as_f64, as_u64, LAny, NUM_F64, NUM_U64};
        let words = |v: &RVec<LAny>| v.as_slice().iter().map(|a| a.word()).collect::<Vec<_>>();
        let imm = |x: u64| (x << 1) | 1;
        let b = from_slice(&[0u8, 7, 255]);
        let d = boxes_of_scalars(b.clone());
        assert_eq!((words(&d), cap(&d), count(&b)), (vec![1, imm(7), imm(255)], 3, 1));
        let d = boxes_of_scalars(from_slice(&[0u16, 0xffff]));
        assert_eq!(words(&d), vec![1, imm(0xffff)]);
        let d = boxes_of_scalars(from_slice(&[0x41u32, u32::MAX]));
        assert_eq!(words(&d), vec![imm(0x41), imm(u32::MAX as u64)]);
        let d = boxes_of_scalars(from_slice(&[1.5f32, -0.0, f32::from_bits(0x7fc0_0001)]));
        assert_eq!(words(&d), vec![imm(1.5f32.to_bits() as u64), imm(0x8000_0000), imm(0x7fc0_0001)]);
        // `UInt64`: an immediate below 2^63, a cell from there.
        let d = boxes_of_scalars(from_slice(&[0u64, (1 << 63) - 1, 1 << 63, u64::MAX]));
        assert_eq!(&words(&d)[..2], &[1, imm((1 << 63) - 1)]);
        assert_eq!(d.as_slice().iter().map(|a| a.num()).collect::<Vec<_>>(), vec![0, 0, NUM_U64, NUM_U64]);
        assert_eq!(d.as_slice().iter().map(|a| as_u64(a.clone())).collect::<Vec<_>>(), vec![0, (1 << 63) - 1, 1 << 63, u64::MAX]);
        // `Float`: a cell each.
        let d = boxes_of_scalars(from_slice(&[2.5f64, -0.0]));
        assert!(d.as_slice().iter().all(|a| a.num() == NUM_F64));
        assert_eq!(d.as_slice().iter().map(|a| as_f64(a.clone()).to_bits()).collect::<Vec<_>>(), vec![2.5f64.to_bits(), (-0.0f64).to_bits()]);
        assert_eq!(size(&boxes_of_scalars(empty::<u16>())), 0);
    }

    #[test]
    fn bytes_and_refs() {
        let b = bytes_of_vec(vec![1, 2, 3, 4]);
        let d = copy_slice(b.clone(), 1, b.clone(), 3, 10, false);
        assert_eq!(d.as_slice(), &[1, 2, 3, 2, 3, 4]);
        assert_eq!(b.as_slice(), &[1, 2, 3, 4]);
        let e = copy_slice(b.clone(), 9, b.clone(), 0, 1, true);
        assert_eq!(e.as_slice(), &[1, 2, 3, 4]);
        let r = ref_new(E(1));
        ref_set(r.clone(), E(2));
        assert_eq!(take_log(), vec![1]);
        assert_eq!(ref_get(r.clone()).0, 2);
        take_log();
        let t = ref_take(r.clone());
        assert!(ref_is_empty(r.clone()));
        ref_set(r.clone(), E(3));
        assert_eq!(ref_swap(r.clone(), E(4)).0, 3);
        assert!(ref_ptr_eq(r.clone(), r.clone()));
        drop((t, r));
        take_log();
    }

    /// `mkEmpty`'s capacity (lean-runtime's LB-37): the capacity asked for
    /// while it can be reserved, else none; never an end. A byte array of
    /// 2^62 passes lean-runtime's size rule, and the native allocation's
    /// probe fails; the other big ones fail the rule (an object size above
    /// 2^64 - 1 or `isize::MAX`).
    #[test]
    fn capacities() {
        assert_eq!(check_capacity(0, 8), 0);
        assert_eq!(check_capacity(3, 8), 3);
        assert_eq!(check_capacity(CHECK_THRESHOLD, 8), CHECK_THRESHOLD as usize);
        assert_eq!(check_capacity(1 << 25, 8), 1 << 25);
        let unreservable = [
            (1 << 62, 1),
            ((1 << 61) - 4, 8),
            ((1 << 61) - 3, 8),
            ((1 << 63) - 1, 8),
            (1 << 63, 1),
            (u64::MAX, 8),
            (u64::MAX, 1),
        ];
        for (n, elem) in unreservable {
            assert_eq!(check_capacity(n, elem), 0, "{n} elements of {elem} bytes");
        }
        let a: RVec<u64> = with_capacity_checked(1 << 63, 8);
        assert_eq!((size(&a), cap(&a)), (0, 0));
        let b: RVec<u8> = with_capacity_checked(1 << 62, 1);
        assert_eq!((size(&b), cap(&b)), (0, 0));
        let c: RVec<u64> = with_capacity_checked(1 << 25, 8);
        assert_eq!(size(&c), 0);
        assert!(cap(&c) >= 1 << 25);
    }
}
