//! Releasing containers without recursion: arrays (`RVec`), references
//! (`LRef`) and thunk/task cells (`LCell`).
//!
//! Native Lean frees an object iteratively (`lean_dec_ref_cold`): the
//! children whose count drops to zero go onto a stack of objects to free,
//! popped last first. Reussir's drop glue does the same with the local
//! patch 13-b: a record member it frees is pushed on a stack of pending
//! work per thread (`reussir_rt::drop`), which the outermost drop empties.
//! A record releases a container field through the container's Rust `Drop`
//! (the opaque type's drop hook), which releases the elements, records
//! again: a tree whose children are in arrays, a chain of thunks.
//!
//! So the containers of the prelude are this module's types, with a `Drop`
//! that frees their last reference through that same stack: one worklist
//! per thread for records, containers and leaves. A container freed while
//! another free runs (from an element's release, or from a record's glue)
//! is pushed instead of freed; the outermost free, glue or container, pops
//! the stack until it is empty. An array is emptied from its last element:
//! each popped element is released, and whatever that release pushes is
//! done before the next element. Releases of leaves (file handles,
//! promises: releases that can be observed) reached while a free runs are
//! pushed too (`active`/`defer`, used by `fs` and `task`). So the order of
//! observable releases is Lean's: the last element first, a nested array's
//! elements before the elements that precede it, a record's last field
//! first. Except at the top of a free that starts at a record that user
//! code drops (a list, tree or structure of handles dropped by itself):
//! Reussir releases that first cell's fields inline, in field order, each
//! completely (in Lean's order within it) before the next, so a list's head
//! handle is closed first. Natively that depends on where the value is
//! dropped (plan §10).
//!
//! The types are `#[repr(transparent)]` pointers whose block starts with
//! the `u32` reference count, all Reussir relies on for an opaque type (the
//! FFI contract): `Vec` is the runtime's own one-block array (`Hdr`, then
//! the elements), `Cell` wraps Reussir's `Rc`.

use std::mem::ManuallyDrop;
use std::ops::{Deref, DerefMut};

/// One unit of pending work: `step(p)` does part of it and answers whether
/// it is finished (then the entry is removed).
type Step = unsafe fn(usize) -> bool;

/// Whether a free is running on this thread (a release now is pushed).
#[inline(always)]
pub fn active() -> bool {
    reussir_rt::drop::active()
}

/// One of lean-runtime's wait cores is reached (a reference's wait, a busy
/// thunk's or a constant's claim): never inside a free, which runs no Lean
/// code (promises dropped there are resolved after it, `task::Promise`), so
/// no wait core can block in lean-runtime's no-suspend scope (its W3, "W3 is
/// unreachable from Lean code"). Checked in debug builds
/// (`L2R_LEANRT_RUSTFLAGS="-C debug-assertions"`).
#[inline(always)]
pub fn assert_not_in_free(what: &str) {
    debug_assert!(!active(), "leanrt: {what} inside a free (lean-runtime's W3)");
}

/// Push work for the running free (see `active`).
pub fn defer(p: usize, step: Step) {
    reussir_rt::drop::defer_step(p, step);
}

/// Run `step` on `p` until it is finished, and everything it pushes; or,
/// inside a running free, push it. No context may suspend inside a free
/// (the free is the thread's, `reussir_rt::drop`: the other contexts would
/// push their frees onto it); lean-runtime's glue item 11 asks for its
/// no-suspend scope over the whole free path. leanrt enters it around the
/// one step of a free that can wait: a stream handle's drop (its flush,
/// `fs::close`). The rest never waits: a task's release, Reussir's own
/// frees, and a promise's drop, whose resolution with `none` (its cell's
/// store, then lean-runtime's walk of its dependents) is put off until the
/// drain is over (`task::defer_promise_drop`; the drain's end runs it,
/// `task::drained`).
#[inline(never)]
pub fn run(p: usize, step: Step) {
    reussir_rt::drop::run_step(p, step);
}

/// Release `x`, a value a reference or a task cell gave up (the prelude's
/// `l2r_rc_set_ref`, `l2r_ref_set`, `l2r_lcell_set`), as native `lean_dec`
/// does. A shared value is only decremented. The last reference to a
/// record is freed inside a free the runtime starts (`free_record`): its members go
/// on the stack of pending work (Reussir's glue releases the first cell of
/// a free it starts itself in field order), so what it holds is released
/// in Lean's order, its last field first, and the promises it drops
/// unresolved are resolved, their `sync` dependents walked, when that free
/// ends (`task::defer_promise_drop`, `task::drained`), before the caller
/// goes on. Other
/// values are dropped: the runtime's containers free themselves that way,
/// and the other runtime objects hold no Lean values whose order shows.
#[inline(always)]
pub fn release<T>(x: T) {
    ReleaseValue::release_value(x)
}

/// `release` of the last reference to `x`, for `array::release_last`: on
/// aarch64 the caller has found a record's count at 1 and the record no
/// immediate, so it is freed without testing them again (`free_unique`).
/// Any other value, or any record on other targets: `release`.
#[inline(always)]
pub(crate) unsafe fn release_unique<T>(x: T) {
    ReleaseValue::release_unique(x)
}

trait ReleaseValue: Sized {
    fn release_value(self);
    unsafe fn release_unique(self);
}

impl<T> ReleaseValue for T {
    #[inline(always)]
    default fn release_value(self) {
        drop(self)
    }
    #[inline(always)]
    default unsafe fn release_unique(self) {
        self.release_value()
    }
}

/// A record (`Bridge<Inner>`: a pointer to its cell, whose 32-bit count is
/// at offset 0, see `ReleaseElems`).
impl<X> ReleaseValue for reussir_rt::bridge::Bridge<X> {
    #[inline(always)]
    fn release_value(self) {
        if std::mem::size_of::<Self>() != std::mem::size_of::<usize>() {
            return drop(self);
        }
        let p: usize = unsafe { std::mem::transmute_copy(&self) };
        if cfg!(target_arch = "aarch64") {
            // An immediate (nonzero top byte, never freed: local patch
            // 06-a) changes nothing; a shared cell is decremented in line.
            if p >> 56 != 0 {
                std::mem::forget(self);
                return;
            }
            let c = count(p);
            if c != 1 {
                unsafe { *(p as *mut u32) = c.wrapping_sub(1) };
                std::mem::forget(self);
                return;
            }
        }
        std::mem::forget(self);
        free_record::<X>(p);
    }
    #[inline(always)]
    unsafe fn release_unique(self) {
        if !(cfg!(target_arch = "aarch64") && std::mem::size_of::<Self>() == std::mem::size_of::<usize>()) {
            return self.release_value();
        }
        let p: usize = std::mem::transmute_copy(&self);
        std::mem::forget(self);
        free_unique::<X>(p);
    }
}

/// Free the record `p` (`release_value`): on aarch64 `free_unique`, on
/// other targets (the immortal encoding: the count is not tested, so it
/// may be shared) a step that runs the record's release (`run`).
#[cold]
#[inline(never)]
fn free_record<X>(p: usize) {
    if cfg!(target_arch = "aarch64") {
        return unsafe { free_unique::<X>(p) };
    }
    run(p, step_record::<X>);
}

/// Free the record `p`, whose count is 1 and which is no immediate. The
/// record goes on the stack of pending work as one deferred cell
/// (`__reussir_drop_defer`, which does not write the cell), and the drain
/// releases it (`__reussir_drop_drain`). Outside a free that is Reussir's
/// drain of one pending cell (`drain_one`): the drain starts, the record's
/// `<record>_ffi_release` runs inside it (so its fields go on the stack and
/// are released last first), and the drain ends, through the general loop
/// only when the release pushed work. Inside a free the cell is only
/// pushed, as a step would be, and released when the free pops it. The
/// order is the same as with a step (`run`); the cost is lower: no entry
/// in the stack's vector, no step dispatch, no `memmove` of the entries
/// above it.
#[inline(always)]
unsafe fn free_unique<X>(p: usize) {
    free_deferred(p, release_record::<X>);
}

/// Free, as one pending cell (`free_unique`'s rule), a record whose last
/// reference is given up and whose release is `release(p)`. Reussir's
/// `__reussir_drop_defer` neither reads nor writes `p` (a deferral that is
/// not `_wide`: the record's layout is not known here), so the drain calls
/// `release` with the cell as it was. (A box's program payload is deferred
/// by `any::release_last` itself, with `_wide` when its type allows.)
#[inline(always)]
pub(crate) unsafe fn free_deferred(p: usize, release: unsafe extern "C" fn(*mut u8)) {
    reussir_rt::drop::__reussir_drop_defer(p as *mut u8, release);
    reussir_rt::drop::__reussir_drop_drain();
}

/// Release the record whose handle is `p` (its `<record>_ffi_release`).
unsafe fn step_record<X>(p: usize) -> bool {
    drop(std::mem::transmute_copy::<usize, reussir_rt::bridge::Bridge<X>>(&p));
    true
}

/// The release function of a record deferred by `free_unique`: its
/// `<record>_ffi_release`, called by the drain.
unsafe extern "C" fn release_record<X>(cell: *mut u8) {
    let p = cell as usize;
    drop(std::mem::transmute_copy::<usize, reussir_rt::bridge::Bridge<X>>(&p));
}

#[inline(always)]
fn count(p: usize) -> u32 {
    unsafe { *(p as *const u32) }
}

/// The header of an array block (`Vec`): the reference count (the `u32`
/// at the handle's address, which Reussir's `rc.inc` bumps and its
/// uniqueness analysis reads), the number of elements and the room for
/// them. The elements follow at `HDR`.
///
/// ```text
///   0: count: u32, (padding)
///   8: len: usize
///  16: cap: usize
///  24: elements: [T; cap], the first `len` initialized
/// ```
///
/// One block per array, elements inline: a read is the handle plus an
/// offset. The cost: an array asked for with a payload of exactly 16 MiB
/// (a hash table's 2^21 buckets) is, with the header, past mimalloc's
/// large-object limit, so a huge segment of its own, which mimalloc purges
/// only 100 ms after it is freed (`arena_purge_mult`): `Std.HashMap` with
/// 0.8M to 2M keys peaks up to 24% higher than with the elements in a
/// buffer apart (as natively: Lean's array has the same header). Keeping
/// large elements apart (a test on the capacity in every access) cost 7-19%
/// more instructions in array loops.
#[repr(C)]
pub struct Hdr {
    pub count: u32,
    _pad: u32,
    pub len: usize,
    pub cap: usize,
}

impl Hdr {
    /// The header of a fresh unique block with room for `cap` elements.
    #[inline(always)]
    pub fn new(cap: usize) -> Hdr {
        Hdr { count: 1, _pad: 0, len: 0, cap }
    }
}

pub const HDR: usize = std::mem::size_of::<Hdr>();

/// The elements of the block `o`. Element types are at most 8-aligned
/// (integers, floats, `bool`, handles): `HDR` keeps them aligned, and
/// mimalloc's blocks are 8-aligned (Reussir builds it with
/// `MI_MAX_ALIGN_SIZE=8`).
#[inline(always)]
pub unsafe fn elems<T>(o: *mut Hdr) -> *mut T {
    const { assert!(std::mem::align_of::<T>() <= 8 && std::mem::size_of::<T>() > 0) };
    (o as *mut u8).add(HDR) as *mut T
}

extern "C" {
    fn mi_free(p: *mut std::ffi::c_void);
}

/// An array (`RVec`) or reference cell (`LRef`): a `#[repr(transparent)]`
/// pointer to one block (`Hdr`, then the elements), owning one reference.
/// Reussir treats it as an opaque rc pointer: `rc.inc` increments the
/// count inline and `rc.dec` calls the drop hook, which drops the value;
/// so `Clone` and `Drop` here do the counting. `crate::array` allocates,
/// grows (`mi_realloc`) and copies the blocks.
///
/// Safety argument: a `Vec` points at a live block from `array::alloc` or
/// `array::grow` (`mi_malloc`/`mi_realloc`) of `HDR + cap * size_of::<T>()`
/// bytes or more, whose first `len <= cap` elements are initialized; it is
/// written or moved only through a unique handle (count 1), and freed only
/// by the reference that finds the count at 1.
#[repr(transparent)]
pub struct Vec<T: Clone>(*mut Hdr, std::marker::PhantomData<T>);

impl<T: Clone> Vec<T> {
    /// The handle of a block whose reference the caller gives up.
    #[inline(always)]
    pub unsafe fn from_raw(o: *mut Hdr) -> Self {
        Vec(o, std::marker::PhantomData)
    }

    /// The block, the handle's reference given up to the caller.
    #[inline(always)]
    pub fn into_raw(self) -> *mut Hdr {
        let o = self.0;
        std::mem::forget(self);
        o
    }

    #[inline(always)]
    pub fn hdr(&self) -> *mut Hdr {
        self.0
    }

    #[inline(always)]
    pub fn is_unique(&self) -> bool {
        unsafe { (*self.0).count == 1 }
    }

    #[inline(always)]
    pub fn len(&self) -> usize {
        unsafe { (*self.0).len }
    }

    #[inline(always)]
    pub fn as_slice(&self) -> &[T] {
        unsafe { std::slice::from_raw_parts(elems::<T>(self.0), (*self.0).len) }
    }
}

impl<T: Clone> Clone for Vec<T> {
    #[inline(always)]
    fn clone(&self) -> Self {
        // A clone is taken from a live reference: the count is at least
        // 1. Told to LLVM, a release right after (a read's `give`) folds
        // to nothing: no store at all for a shared block, such as a
        // constant's (`l2r_once_get` then a read).
        unsafe {
            let c = (*self.0).count;
            std::hint::assert_unchecked(c != 0);
            (*self.0).count = c + 1;
        }
        Vec(self.0, std::marker::PhantomData)
    }
}

impl<T: Clone> Drop for Vec<T> {
    /// A shared handle is a decrement; the last reference is freed out of
    /// line (keeps the textures that read an array small enough to inline).
    /// The test is `count == 1` (a live count is never 0): after Reussir's
    /// `rc.inc`, which asserts that the old count was neither 0 nor
    /// `u32::MAX`, LLVM then knows that a read's release only decrements,
    /// and cancels the pair; with `count > 1` the free check, and with it
    /// the bounds check, stayed in every read (1.6x the instructions of an
    /// in-place quicksort).
    #[inline(always)]
    fn drop(&mut self) {
        let o = self.0;
        unsafe {
            let c = (*o).count;
            if c == 1 {
                free_vec::<T>(o);
            } else {
                (*o).count = c - 1;
            }
        }
    }
}

/// Free the block `o` of a vector whose last reference the caller gives up
/// (count 1). `extern "C"`: it cannot unwind, so the textures that release
/// an array need no landing pad for it.
#[cold]
#[inline(never)]
pub extern "C" fn free_vec<T: Clone>(o: *mut Hdr) {
    if !std::mem::needs_drop::<T>() {
        unsafe { mi_free(o as *mut std::ffi::c_void) };
        return;
    }
    // Outside a free, `run` would release the elements now, from the last
    // one: those whose release only decrements (shared ones: the old
    // version of an array that was copied for an update) are released here
    // first, which is the same. If all are, the block is freed without the
    // stack; else the stack's work goes on from the first element whose
    // release frees it. Inside a free the array is only pushed, and its
    // elements are released when it is popped, after the work pushed before
    // it (a later field of the record being freed may hold one of them).
    if !active() && unsafe { T::release_shared_from_end(o) } {
        unsafe { mi_free(o as *mut std::ffi::c_void) };
        return;
    }
    run(o as usize, step_vec::<T>);
}

/// Release the elements of the block at `p` from the last one, until one
/// of them pushes work (done first) or none is left (then free the block).
unsafe fn step_vec<T: Clone>(p: usize) -> bool {
    let depth = reussir_rt::drop::depth();
    let o = p as *mut Hdr;
    if !T::release_from_end(o, depth) {
        return false;
    }
    mi_free(o as *mut std::ffi::c_void);
    true
}

/// Releasing the elements of a block being freed (`step_vec`). Each
/// element leaves the block (`len` decremented) before it is released, so
/// the block always holds exactly the elements still to release.
trait ReleaseElems: Sized {
    /// Release elements from the last one until the block is empty
    /// (`true`) or a release pushed work, which is done first (`false`;
    /// the elements left stay in the block). `depth` is the stack's depth
    /// before.
    unsafe fn release_from_end(o: *mut Hdr, depth: usize) -> bool;
    /// Release elements from the last one while their release frees
    /// nothing; answers whether the block is then empty. (For element types
    /// whose releases cannot be told apart, none: the block stays as it is.)
    unsafe fn release_shared_from_end(o: *mut Hdr) -> bool;
}

#[inline(always)]
unsafe fn release_from_end_each<T>(o: *mut Hdr, depth: usize) -> bool {
    let e = elems::<T>(o);
    let mut n = (*o).len;
    while n > 0 {
        n -= 1;
        (*o).len = n;
        drop(std::ptr::read(e.add(n)));
        if n == 0 {
            break;
        }
        if reussir_rt::drop::depth() != depth {
            return false;
        }
    }
    true
}

impl<T> ReleaseElems for T {
    #[inline(always)]
    default unsafe fn release_from_end(o: *mut Hdr, depth: usize) -> bool {
        release_from_end_each::<T>(o, depth)
    }
    #[inline(always)]
    default unsafe fn release_shared_from_end(o: *mut Hdr) -> bool {
        (*o).len == 0
    }
}

/// A Reussir record (`Bridge<Inner>`, see `array::CloneInto`): its
/// `Drop` is the compiler-emitted `<record>_ffi_release`, an out-of-line
/// call per element, which decrements the 32-bit count at offset 0 (not
/// stored for an immediate, whose top byte is a tag under the aarch64
/// encoding of nullary variants) and frees the box when the count was 1.
/// Here a shared element is decremented inline, as `lean_del` does
/// natively, and an immediate is skipped (its release changes nothing:
/// Reussir never frees one, local patch 06-a); only an element whose count
/// is 1 goes through `<record>_ffi_release`, which frees it, so the order
/// of releases and the stack's work are as with the generic loop.
impl<X> ReleaseElems for reussir_rt::bridge::Bridge<X> {
    #[inline(always)]
    unsafe fn release_from_end(o: *mut Hdr, depth: usize) -> bool {
        if !(cfg!(target_arch = "aarch64") && std::mem::size_of::<Self>() == 8) {
            return release_from_end_each::<Self>(o, depth);
        }
        let e = elems::<Self>(o);
        let mut n = (*o).len;
        while n > 0 {
            let p = *(e.add(n - 1) as *const usize);
            if p >> 56 != 0 {
                n -= 1;
                (*o).len = n;
                continue;
            }
            let c = *(p as *const u32);
            if c != 1 {
                *(p as *mut u32) = c.wrapping_sub(1);
                n -= 1;
                (*o).len = n;
                continue;
            }
            n -= 1;
            (*o).len = n;
            drop(std::ptr::read(e.add(n)));
            if n == 0 {
                break;
            }
            if reussir_rt::drop::depth() != depth {
                return false;
            }
        }
        true
    }
    #[inline(always)]
    unsafe fn release_shared_from_end(o: *mut Hdr) -> bool {
        if !(cfg!(target_arch = "aarch64") && std::mem::size_of::<Self>() == 8) {
            return (*o).len == 0;
        }
        let e = elems::<Self>(o);
        let mut n = (*o).len;
        while n > 0 {
            let p = *(e.add(n - 1) as *const usize);
            if p >> 56 == 0 {
                let c = *(p as *const u32);
                if c == 1 {
                    return false;
                }
                *(p as *mut u32) = c.wrapping_sub(1);
            }
            n -= 1;
            (*o).len = n;
        }
        true
    }
}

/// A box (`any::LAny`, the element of every `Array` of a Lean type): an
/// immediate releases nothing and is skipped; a shared payload is
/// decremented in line; only a payload whose count is 1 goes to
/// `any::release_last` (which frees one of leanrt's leaves at once and
/// pushes anything else), after the block's `len` is set to the elements
/// before it, and only then is the stack's depth read. So the order of
/// releases and the stack's work are as with the generic loop
/// (`release_from_end_each`), which stored `len` and read the depth for
/// every element (12 instructions an element of an array of immediates;
/// sieve frees a million-element `Array Bool` that way).
impl ReleaseElems for crate::any::LAny {
    #[inline(always)]
    unsafe fn release_from_end(o: *mut Hdr, depth: usize) -> bool {
        let e = elems::<u64>(o);
        let mut n = (*o).len;
        while n > 0 {
            n -= 1;
            let w = *e.add(n);
            if crate::any::is_imm(w) {
                continue;
            }
            let p = crate::any::addr_of(w) as *mut u32;
            let c = *p;
            if c != 1 {
                *p = c - 1;
                continue;
            }
            (*o).len = n;
            crate::any::release_last(w);
            if n == 0 {
                break;
            }
            if reussir_rt::drop::depth() != depth {
                return false;
            }
        }
        true
    }
    #[inline(always)]
    unsafe fn release_shared_from_end(o: *mut Hdr) -> bool {
        let e = elems::<u64>(o);
        let mut n = (*o).len;
        while n > 0 {
            let w = *e.add(n - 1);
            if !crate::any::is_imm(w) {
                let p = crate::any::addr_of(w) as *mut u32;
                let c = *p;
                if c == 1 {
                    (*o).len = n;
                    return false;
                }
                *p = c - 1;
            }
            n -= 1;
        }
        true
    }
}

/// A thunk or task cell: Reussir's `Rc` around the state.
#[repr(transparent)]
pub struct Cell<T>(ManuallyDrop<reussir_rt::rc::Rc<T>>);

impl<T> Cell<T> {
    #[inline(always)]
    pub fn from_inner(c: reussir_rt::rc::Rc<T>) -> Self {
        Cell(ManuallyDrop::new(c))
    }
}

impl<T> Clone for Cell<T> {
    #[inline(always)]
    fn clone(&self) -> Self {
        Cell(ManuallyDrop::new((*self.0).clone()))
    }
}

impl<T> Deref for Cell<T> {
    type Target = reussir_rt::rc::Rc<T>;
    #[inline(always)]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T> DerefMut for Cell<T> {
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<T> Drop for Cell<T> {
    /// A shared handle is a decrement; the last reference is freed out of
    /// line. The test is `count == 1`, as `Vec`'s: after Reussir's `rc.inc`
    /// LLVM then cancels a read's increment and release (forcing a finished
    /// thunk, reading a task's state).
    #[inline(always)]
    fn drop(&mut self) {
        let p = unsafe { *(self as *const Self as *const usize) };
        let c = count(p);
        if c == 1 {
            free_cell::<T>(p);
        } else {
            unsafe { *(p as *mut u32) = c - 1 };
        }
    }
}

/// The value of a cell (a new reference), the cell's own reference given
/// up (`l2r_lcell_get`: forcing a finished thunk, reading a task's state).
/// The release is decided before the value is copied: a shared cell is
/// decremented first, right after the caller's `rc.inc`, so LLVM cancels
/// the pair (copying the value first increments the state record, which
/// LLVM cannot tell from the cell, and the cell's count was reloaded and
/// tested). The last reference moves the value out and frees the cell's
/// block, which releases nothing, as the copy and the free did.
#[inline(always)]
pub fn cell_get<T: Clone>(c: Cell<T>) -> T {
    let p = unsafe { *(&c as *const Cell<T> as *const usize) };
    std::mem::forget(c);
    let n = count(p);
    if n == 1 {
        return cell_take_last::<T>(p);
    }
    unsafe { *(p as *mut u32) = n - 1 };
    // Others still hold the cell, so it outlives the copy.
    let r = std::mem::ManuallyDrop::new(unsafe { std::mem::transmute::<usize, reussir_rt::rc::Rc<T>>(p) });
    r.data_ref().clone()
}

/// The value of the cell at `p` (count 1), moved out; its block is freed.
#[cold]
#[inline(never)]
fn cell_take_last<T>(p: usize) -> T {
    unsafe { crate::alloc::rc_into_inner(std::mem::transmute::<usize, reussir_rt::rc::Rc<T>>(p)) }
}

/// `extern "C"`: it cannot unwind, so the textures that release a cell
/// need no landing pad for it. The last reference to an unfinished task
/// goes to the task glue first (`task::on_last_reference`: lean-runtime's
/// `release`), which may keep the cell for a task lean-runtime still runs.
#[cold]
#[inline(never)]
extern "C" fn free_cell<T>(p: usize) {
    if crate::task::on_last_reference(p) {
        return;
    }
    run(p, step_cell::<T>);
}

/// Free the cell at `p` (count 1), then release its value.
unsafe fn step_cell<T>(p: usize) -> bool {
    let v = crate::alloc::rc_into_inner(std::mem::transmute::<usize, reussir_rt::rc::Rc<T>>(p));
    drop(v);
    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::RefCell;

    thread_local! {
        static LOG: RefCell<std::vec::Vec<u32>> = RefCell::new(std::vec::Vec::new());
    }

    /// A value that logs its releases.
    #[derive(Clone)]
    struct E(u32);

    impl Drop for E {
        fn drop(&mut self) {
            LOG.with(|l| l.borrow_mut().push(self.0));
        }
    }

    fn take_log() -> std::vec::Vec<u32> {
        LOG.with(|l| std::mem::take(&mut *l.borrow_mut()))
    }

    fn cell_count<T>(c: &Cell<T>) -> u32 {
        count(unsafe { *(c as *const Cell<T> as *const usize) })
    }

    /// A record cell as Reussir lays it out for `free_record`: the 32-bit
    /// count at offset 0. `id` is logged when the cell is freed, and the
    /// members are released then, in field order, as Reussir's glue does.
    #[repr(C)]
    struct TCell {
        count: u32,
        id: u32,
        members: std::vec::Vec<TRec>,
    }

    /// A record handle (`Bridge<TRec>`): its drop is the record's
    /// `<record>_ffi_release` (a count of 1 frees the cell, else a
    /// decrement). Inside a free a member is released through `release`,
    /// so a member freed goes on the stack, as the glue defers it.
    struct TRec(*mut TCell);

    type B = reussir_rt::bridge::Bridge<TRec>;

    fn rec(id: u32, members: std::vec::Vec<TRec>) -> TRec {
        TRec(Box::into_raw(Box::new(TCell { count: 1, id, members })))
    }

    impl Drop for TRec {
        fn drop(&mut self) {
            let c = unsafe { &mut *self.0 };
            if c.count != 1 {
                c.count -= 1;
                return;
            }
            // 1000 + id: freed outside a free (the order would be the glue's
            // top-level one, field order).
            LOG.with(|l| l.borrow_mut().push(if active() { c.id } else { 1000 + c.id }));
            let cell = unsafe { Box::from_raw(self.0) };
            for m in cell.members {
                release(B::new(m));
            }
        }
    }

    /// `free_record` releases a record inside a free: its members in Lean's
    /// order (the last first, a member's members before the members that
    /// precede it), a shared member only decremented; the free is over when
    /// `release` returns.
    #[test]
    fn record_free_order() {
        let shared = rec(9, vec![]);
        let s2 = TRec(shared.0);
        unsafe { (*shared.0).count = 2 };
        let a = rec(2, vec![rec(3, vec![]), rec(4, vec![])]);
        let b = rec(5, vec![s2, rec(6, vec![rec(7, vec![])])]);
        release(B::new(rec(1, vec![a, b])));
        assert_eq!(take_log(), vec![1, 5, 6, 7, 2, 4, 3]);
        assert!(!active());
        assert_eq!(reussir_rt::drop::depth(), 0);
        assert_eq!(unsafe { (*shared.0).count }, 1);
        release(B::new(shared));
        assert_eq!(take_log(), vec![9]);
        // Shared: a decrement only.
        let r = rec(8, vec![]);
        unsafe { (*r.0).count = 2 };
        let r2 = TRec(r.0);
        release(B::new(r));
        assert_eq!(take_log(), std::vec::Vec::<u32>::new());
        release(B::new(r2));
        assert_eq!(take_log(), vec![8]);
        // The last reference, the count not tested again (a set's or a
        // pop's `release_last`): the same free.
        let a = rec(12, vec![rec(13, vec![])]);
        unsafe { release_unique(B::new(rec(11, vec![a, rec(14, vec![rec(15, vec![])])]))) };
        assert_eq!(take_log(), vec![11, 14, 15, 12, 13]);
        assert!(!active());
        assert_eq!(reussir_rt::drop::depth(), 0);
    }

    thread_local! {
        static PENDING: RefCell<Option<TRec>> = const { RefCell::new(None) };
    }

    /// A step that releases the record left in `PENDING`, logging 100
    /// before and 101 after.
    unsafe fn step_release(_: usize) -> bool {
        LOG.with(|l| l.borrow_mut().push(100));
        let r = PENDING.with(|p| p.borrow_mut().take()).unwrap();
        release(B::new(r));
        LOG.with(|l| l.borrow_mut().push(101));
        true
    }

    /// Inside a free, `free_record` only pushes the record: it is released
    /// after the step that released it, before the work pushed earlier.
    #[test]
    fn record_free_inside_a_free() {
        PENDING.with(|p| *p.borrow_mut() = Some(rec(1, vec![rec(2, vec![]), rec(3, vec![])])));
        let first = rec(4, vec![]);
        // The free: a step releasing `first` (pushed below), then one
        // releasing the pending record.
        unsafe fn step_first(p: usize) -> bool {
            LOG.with(|l| l.borrow_mut().push(50));
            defer(0, step_release);
            release(B::new(TRec(p as *mut TCell)));
            true
        }
        let p = first.0 as usize;
        std::mem::forget(first);
        run(p, step_first);
        assert_eq!(take_log(), vec![50, 4, 100, 101, 1, 3, 2]);
        assert!(!active());
        assert_eq!(reussir_rt::drop::depth(), 0);
    }

    #[test]
    fn cell_get_shared_and_last() {
        let c = Cell::from_inner(reussir_rt::rc::Rc::new(E(7)));
        let d = c.clone();
        assert_eq!(cell_count(&c), 2);
        // Shared: decremented, the value copied; nothing released.
        let v = cell_get(d);
        assert_eq!(v.0, 7);
        assert_eq!(cell_count(&c), 1);
        assert_eq!(take_log(), std::vec::Vec::<u32>::new());
        drop(v);
        assert_eq!(take_log(), vec![7]);
        // The last reference: the value moves out, nothing released.
        let w = cell_get(c);
        assert_eq!(w.0, 7);
        assert_eq!(take_log(), std::vec::Vec::<u32>::new());
        drop(w);
        assert_eq!(take_log(), vec![7]);
    }
}
