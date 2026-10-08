//! Allocation of runtime objects through mimalloc's plain entry points.
//!
//! Reussir's global allocator (`reussir_rt::alloc::ReussirGlobalAlloc`)
//! raises every Rust allocation to 16-byte alignment, above what it treats as
//! mimalloc's natural alignment (8), so *every* Rust `Box`/`Vec` allocation
//! takes mimalloc's aligned path (`mi_malloc_aligned`, `mi_realloc_aligned`).
//! Without Reussir patch 03-a, a size that is not a multiple of 16 could be
//! moved inside a larger block, and later frees in that page went down
//! mimalloc's generic path (reussir-bugs/03-global-alloc-align.md); with it,
//! the size is rounded up to a multiple of 16. Strings, arrays and big
//! numbers are allocated here instead with `mi_malloc`/`mi_realloc`, whose
//! blocks are 8-aligned (Reussir builds mimalloc with `MI_MAX_ALIGN_SIZE=8`),
//! which is all runtime objects need, in blocks no larger than they need.
//! They are freed normally: the global allocator frees any mimalloc block
//! with `mi_free`.
//!
//! Types aligned above 8 fall back to the standard allocation.
//!
//! This requires reussir_rt's (default) mimalloc allocator backend: with a
//! libc-backed global allocator (sanitizer builds), these blocks would be
//! freed with `free`.

use reussir_rt::rc::Rc;
use std::ffi::{c_int, c_long, c_void};
use std::mem::{align_of, size_of};

extern "C" {
    fn mi_malloc(size: usize) -> *mut c_void;
    fn mi_malloc_small(size: usize) -> *mut c_void;
    fn mi_zalloc(size: usize) -> *mut c_void;
    fn mi_realloc(p: *mut c_void, size: usize) -> *mut c_void;
    fn mi_free(p: *mut c_void);
    fn mi_good_size(size: usize) -> usize;
    fn mi_version() -> c_int;
    fn mi_option_set(option: c_int, value: c_long);
}

/// The mimalloc versions (`mi_version()`, `MI_MALLOC_VERSION`: 218 for
/// v2.1.8) whose `mi_arenas_try_purge` (`src/arena.c`) tests the arenas'
/// purge time the wrong way round: `if (!force && (arenas_expire == 0 ||
/// arenas_expire < now)) return;` (v2.2.4, line 624) returns when the
/// time is past, which is when it should purge. v2.1.8 added the test with
/// the global purge time; v2.3.0 fixed it (`> now`, mimalloc's commit
/// "fix inverted purge expire comparison"), and from v2.3.0 on the version
/// also has two digits of patch (20300). mimalloc v3 (300 and up) never had
/// the error. Checked in the `src/arena.c` of every v2.1, v2.2, v2.3 and
/// v3.0/v3.1 tag.
const ARENA_PURGE_INVERTED: std::ops::RangeInclusive<c_int> = 218..=227;

/// `mi_option_arena_purge_mult` in `mi_option_t`: 24 in the
/// `include/mimalloc.h` of every version of [`ARENA_PURGE_INVERTED`]
/// (`mi_option_purge_delay` is 15).
const MI_OPTION_ARENA_PURGE_MULT: c_int = 24;

/// Whether [`purge_arenas_at_once`] sets the option for a mimalloc of
/// `version` (`mi_version()`) when the environment does not set it.
fn arena_purge_inverted(version: c_int) -> bool {
    ARENA_PURGE_INVERTED.contains(&version)
}

/// Whether the environment has the variable `name` in any case, as
/// mimalloc finds its options (`MIMALLOC_...`; `_mi_prim_getenv`: the
/// entries of C's `environ`, names compared without case). It reads
/// `environ` itself: `std::env::vars_os` copies every variable (two
/// allocations each at every start, 136 more in the pay-nothing counts).
/// Called before the program starts a thread or changes the environment
/// (`rt::run_main2`'s first call), and by a unit test.
fn env_has(name: &[u8]) -> bool {
    extern "C" {
        static environ: *const *const std::ffi::c_char;
    }
    unsafe {
        let mut p = environ;
        while !p.is_null() && !(*p).is_null() {
            let e = std::ffi::CStr::from_ptr(*p).to_bytes();
            if e.len() > name.len() && e[name.len()] == b'=' && e[..name.len()].eq_ignore_ascii_case(name) {
                return true;
            }
            p = p.add(1);
        }
    }
    false
}

/// Let mimalloc give free arena memory back to the OS at once: it sets
/// `arena_purge_mult` to 0, on a mimalloc whose delayed arena purges do
/// not run ([`ARENA_PURGE_INVERTED`]; Reussir's `libmimalloc-sys` 0.1.44
/// bundles v2.2.4). Called first in `rt::run_main2`, before the module
/// initializers.
///
/// mimalloc purges a free range of an arena (a huge block of more than
/// 16 MiB, or a whole segment) `purge_delay` x `arena_purge_mult` ms
/// (10 x 10) after its free, but the inverted test lets the delayed purges
/// run almost never, so the memory stays in the process until it is used
/// again. With the multiplier at 0 the arena purges each such range when it
/// is freed; the purges inside segments keep their delay. lean-zip's peak
/// went from 422 to 330 MiB (native 394 MiB), wall time +0.9 % (system
/// time); no other benchmark changed. `MIMALLOC_PURGE_DELAY=-1` still turns
/// purging off: mimalloc's OS layer tests it.
///
/// Not set when the environment sets `MIMALLOC_ARENA_PURGE_MULT` (any
/// case, as mimalloc reads it), or on another mimalloc version, so a
/// Reussir with a fixed mimalloc turns it off by itself.
pub fn purge_arenas_at_once() {
    if arena_purge_inverted(unsafe { mi_version() }) && !env_has(b"MIMALLOC_ARENA_PURGE_MULT") {
        unsafe { mi_option_set(MI_OPTION_ARENA_PURGE_MULT, 0) }
    }
}

#[cold]
#[inline(never)]
fn oom() -> ! {
    crate::lean_internal_panic(lean_runtime::semantics::panic::InternalPanic::OutOfMemory)
}

/// The bytes a mimalloc block asked for with `bytes` bytes (a multiple of
/// 8) can hold, mimalloc's size class (`mi_good_size`): the capacity big
/// numbers, strings and arrays take for a block. Up to 64 bytes it is
/// `bytes` itself, without the call: mimalloc's classes there are every
/// multiple of 8 (one per word count, `mi_bin`), so `mi_good_size` would
/// return its argument (unit test `alloc::tests::small_good_size`); and were
/// a class bigger, a capacity of `bytes` would still lie inside the block,
/// with room left unused. In an instruction-count profile of the classic
/// programs the call (with mimalloc's `_mi_bin_size`) was 1.9 % of
/// liasolver's instructions (one-limb big numbers) and 0.65 % of qsort's
/// (array growth).
#[inline(always)]
pub fn good_size(bytes: usize) -> usize {
    debug_assert!(bytes % 8 == 0);
    if bytes <= 64 {
        bytes
    } else {
        unsafe { mi_good_size(bytes) }
    }
}

/// Mirror of `reussir_rt::rc::RcBox` (`#[repr(C)] { count: Cell<u32>, data }`).
#[repr(C)]
struct RcBoxMirror<T> {
    count: u32,
    data: T,
}

#[inline(always)]
fn plain<T>() -> bool {
    align_of::<T>() <= 8 && size_of::<T>() > 0
}

/// mimalloc's `MI_SMALL_SIZE_MAX` (128 words): `mi_malloc_small` takes
/// sizes up to it.
const SMALL_SIZE_MAX: usize = 128 * size_of::<usize>();

/// `Rc::new(v)` allocated with `mi_malloc`, or `mi_malloc_small` when the
/// box is small (every scalar cell: a boxed `Float` or large `UInt64`),
/// which skips mimalloc's test of the size (the size is a constant here,
/// so the choice costs nothing).
#[inline(always)]
pub fn rc_new<T>(v: T) -> Rc<T> {
    if !plain::<RcBoxMirror<T>>() {
        return Rc::new(v);
    }
    unsafe {
        let size = size_of::<RcBoxMirror<T>>();
        let p = if size <= SMALL_SIZE_MAX { mi_malloc_small(size) } else { mi_malloc(size) } as *mut RcBoxMirror<T>;
        if p.is_null() {
            oom();
        }
        std::ptr::write(p, RcBoxMirror { count: 1, data: v });
        // `Rc<T>` is a `#[repr(transparent)]` pointer to its box.
        std::mem::transmute::<*mut RcBoxMirror<T>, Rc<T>>(p)
    }
}

/// The value of a uniquely referenced `Rc`, moved out; its box is freed
/// without dropping the value. Boxes from `rc_new` and from `Rc::new` (the
/// global allocator) are both mimalloc blocks.
///
/// # Safety
/// `r` must be unique (count 1).
#[inline(always)]
pub unsafe fn rc_into_inner<T>(r: Rc<T>) -> T {
    debug_assert!(r.is_unique());
    let p = std::mem::transmute::<Rc<T>, *mut RcBoxMirror<T>>(r);
    let v = std::ptr::read(&(*p).data);
    mi_free(p as *mut c_void);
    v
}

/// Free a mimalloc block whose contents need no drop (a scalar cell).
///
/// # Safety
/// `p` is a live mimalloc block that nothing references any more.
#[inline(always)]
pub unsafe fn free(p: *mut u8) {
    unsafe { mi_free(p as *mut c_void) }
}

/// The value in the box `p` of an `Rc<T>` (`RcBoxMirror`'s `data`), for
/// reads of a cell by its address.
#[inline(always)]
pub fn rc_data<T>(p: *mut u8) -> *mut T {
    p.wrapping_add(std::mem::offset_of!(RcBoxMirror<T>, data)) as *mut T
}

/// `Box::new(v)` allocated with `mi_malloc`.
#[inline(always)]
pub fn box_new<T>(v: T) -> Box<T> {
    if !plain::<T>() {
        return Box::new(v);
    }
    unsafe {
        let p = mi_malloc(size_of::<T>()) as *mut T;
        if p.is_null() {
            oom();
        }
        std::ptr::write(p, v);
        Box::from_raw(p)
    }
}

/// An empty vector with room for `cap` elements.
#[inline(always)]
pub fn vec_with_capacity<T>(cap: usize) -> Vec<T> {
    if cap == 0 || !plain::<T>() {
        return Vec::with_capacity(cap);
    }
    unsafe {
        let p = mi_malloc(cap.checked_mul(size_of::<T>()).unwrap_or_else(|| oom())) as *mut T;
        if p.is_null() {
            oom();
        }
        Vec::from_raw_parts(p, 0, cap)
    }
}

/// `n` zero words.
#[inline(always)]
pub fn vec_zeroed_u64(n: usize) -> Vec<u64> {
    if n == 0 {
        return Vec::new();
    }
    unsafe {
        let p = mi_zalloc(n.checked_mul(8).unwrap_or_else(|| oom())) as *mut u64;
        if p.is_null() {
            oom();
        }
        Vec::from_raw_parts(p, n, n)
    }
}

/// A copy of a slice, with room for `extra` more elements.
#[inline(always)]
pub fn vec_from_slice<T: Clone>(s: &[T], extra: usize) -> Vec<T> {
    let mut v = vec_with_capacity(s.len() + extra);
    v.extend_from_slice(s);
    v
}

/// Make room for `extra` more elements, growing geometrically (so appends
/// are amortized O(1)) with `mi_realloc` instead of the aligned realloc.
#[inline(always)]
pub fn reserve<T>(v: &mut Vec<T>, extra: usize) {
    let need = v.len() + extra;
    if need > v.capacity() {
        grow(v, need)
    }
}

#[cold]
#[inline(never)]
fn grow<T>(v: &mut Vec<T>, need: usize) {
    if !plain::<T>() {
        v.reserve(need - v.len());
        return;
    }
    let new_cap = need.max(v.capacity().saturating_mul(2)).max(8);
    let bytes = new_cap.checked_mul(size_of::<T>()).unwrap_or_else(|| oom());
    let mut old = std::mem::ManuallyDrop::new(std::mem::take(v));
    let (ptr, len, cap) = (old.as_mut_ptr(), old.len(), old.capacity());
    unsafe {
        let np = if cap == 0 { mi_malloc(bytes) } else { mi_realloc(ptr as *mut c_void, bytes) } as *mut T;
        if np.is_null() {
            oom();
        }
        *v = Vec::from_raw_parts(np, len, new_cap);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    extern "C" {
        fn mi_option_get(option: c_int) -> c_long;
    }

    /// The workaround's gate: the versions with the inverted purge test
    /// (v2.1.8 to v2.2.7) and no other; v2.3 numbers its versions with
    /// two digits of patch.
    #[test]
    fn arena_purge_gate() {
        for v in [218, 219, 222, 223, 224, 226, 227] {
            assert!(arena_purge_inverted(v), "{v}");
        }
        for v in [212, 217, 228, 300, 315, 20300, 20302, 30302] {
            assert!(!arena_purge_inverted(v), "{v}");
        }
    }

    /// `env_has` finds a variable whatever the case of its name, as
    /// mimalloc does, and only a whole name.
    #[test]
    fn env_has_ignores_case() {
        assert!(env_has(b"PATH") && env_has(b"path") && env_has(b"PaTh"));
        assert!(!env_has(b"PAT") && !env_has(b"PATH_") && !env_has(b"L2R_NO_SUCH_VARIABLE"));
    }

    /// On the linked mimalloc (Reussir's: v2.2.4, in the gate),
    /// `purge_arenas_at_once` turns `arena_purge_mult` from its default 10
    /// (its neighbours `arena_reserve` and `purge_extend_delay` default to
    /// 1 GiB and 1, so a wrong index shows) to 0 and leaves `purge_delay`
    /// (15) alone; on a version out of the gate, or when the environment
    /// sets the option, it changes nothing. The option only times arena
    /// purges, so setting it here does not disturb the other tests.
    #[test]
    fn arena_purge_mult_set() {
        let v = unsafe { mi_version() };
        let delay = unsafe { mi_option_get(15) };
        let before = unsafe { mi_option_get(MI_OPTION_ARENA_PURGE_MULT) };
        purge_arenas_at_once();
        let after = unsafe { mi_option_get(MI_OPTION_ARENA_PURGE_MULT) };
        if arena_purge_inverted(v) && !env_has(b"MIMALLOC_ARENA_PURGE_MULT") {
            assert_eq!((before, after), (10, 0), "mimalloc {v}");
        } else {
            assert_eq!(after, before, "mimalloc {v}");
        }
        assert_eq!(unsafe { mi_option_get(15) }, delay, "purge_delay");
    }

    /// `good_size` skips `mi_good_size` up to 64 bytes: there mimalloc's
    /// size class of a multiple of 8 is that size, so no capacity is lost;
    /// above, it is the call.
    #[test]
    fn small_good_size() {
        for b in (8..=4096).step_by(8) {
            assert_eq!(good_size(b), unsafe { mi_good_size(b) }, "{b} bytes");
        }
    }
}
