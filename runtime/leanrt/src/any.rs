//! `LAny`: a value whose type is not known at compile time (Lean's `lcAny`,
//! lean2rr's uniform `Box`), in one machine word, as Lean's `lean_object*`.
//!
//! - An odd word is an immediate, `(v << 1) | 1` (`v` below 2^63): `Bool`,
//!   an enumeration's index, `UInt8/16/32`, `Char`, the bits of a `Float32`,
//!   a `UInt64`/`USize` below 2^63, unit (`1`, Lean's `box(0)`), a nullary
//!   constructor of a Reussir enum (its variant index), and a small `Nat` or
//!   `Int`, whose words are already this encoding (`nat`).
//! - An even word owns one reference to a counted object: the low 48 bits
//!   are the object's address, the top 16 bits the number of the payload's
//!   type (`num`). Every object that can be boxed is one pointer to a block
//!   whose `u32` count is at offset 0 (Reussir records and enums, function
//!   values, `LStr`, `RVec`, `LCell`, big numbers, the cells below), so a
//!   copy of an `LAny` is a copy of its payload: the payload's count goes
//!   up, and an unboxed payload is the same object (uniqueness carries
//!   over).
//!
//! On the Reussir side `LAny` is a `tagged` opaque type
//! (`#[ffi(rust = "::leanrt::any::LAny", tagged)]`): Reussir's `rc.inc`
//! skips an odd word and, with the local Reussir patch 38-a (issue 38),
//! clears the top 16 bits before it increments the count in line; its
//! `rc.dec` calls the drop hook (`Drop` below) for an even word.
//!
//! Payload numbers: 0 is never used; 1 to 15 are leanrt's own payload kinds
//! (`NUM_*`), released here: 1 a big `Nat`, 2 a big `Int`, 3 a `String`, 4
//! a `Float`'s cell, 5 a large `UInt64`'s cell, 6 an array of boxes, 7 to
//! 12 the arrays of scalars (7 `RVec<u8>`, a `ByteArray` or a compact
//! `Array` of `UInt8`, `Bool` or a small enumeration; 8 `RVec<f64>`, a
//! `FloatArray` or a compact `Array Float`; 9 `RVec<u16>`, 10 `RVec<u32>`,
//! 11 `RVec<u64>`, 12 `RVec<f32>`: compact `Array`s of `UInt16`, of
//! `UInt32` or `Char`, of `UInt64` or `USize`, of `Float32`); 13 to 15 are
//! free. 16 and up are the program's (lean2rr numbers the payload types of
//! a program). An array of boxes unboxed from an array of scalars is
//! converted (`boxes_of_compact`, the safety net). The last reference to a
//! program payload goes to the program's release function of its type (a
//! table by payload number, `RELEASES`: lean2rr's
//! `l2r_any_rel_<num>_c(cell)`, an `extern "C" trampoline` of a generated
//! Reussir function that drops the payload at its type), through the drop
//! worklist: the payload's cell is deferred as one pending cell, so a chain
//! of a million nested boxes is freed without deep recursion and what the
//! payload holds is released in native Lean's order. A payload whose number
//! has `WIDE_BIT` (lean2rr gives it to types whose Reussir cell starts with
//! an 8-byte header) is deferred with `__reussir_drop_defer_wide`: a run of
//! such cells deferred one after the other (the heads of a list that a
//! free releases whole) is linked through the cells and takes no memory. A
//! leaf payload (a number with `LEAF_BIT`: lean2rr gives it to records and
//! enums whose fields are all scalars) is released by a direct call, also
//! inside a free: it holds nothing to order. The array free calls a payload's
//! release directly where the deferred cell would be popped next anyway
//! (`release_last_in_step`, and an array that keeps one element:
//! `drop::ReleaseElems::free_single`).
//!
//! A payload that is not one counted pointer is boxed in a cell first: an
//! `f64` and a `UInt64`/`USize` from 2^63 here (`NUM_F64`, `NUM_U64`, a
//! `reussir_rt::rc::Rc`, as native Lean allocates for them); a multi-word
//! `[value]` record in a one-field shared record that lean2rr generates.
//!
//! The 48-bit address is checked when a pointer is boxed (a panic if a top
//! bit is set). User-space addresses are below 2^48 on aarch64 (48-bit
//! virtual addresses; with 52-bit ones only for mappings asked for above
//! 2^48) and x86-64 (47 bits; 5-level paging gives more only on request),
//! and mimalloc's address hints lie between 2 and 32 TiB.
//!
//! Nullary variants. Reussir represents a nullary constructor of a shared
//! enum as an immediate that points at a static dummy box: on aarch64 (the
//! `tbi` encoding) with the top byte set to `tag + 1`, elsewhere (the
//! `immortal` encoding) with a dummy count of at least 2^31. `of` turns
//! both into the immediate of the variant's index (Lean's `lean_box(i)` for
//! a nullary constructor); unboxing an immediate at an enum type is the
//! program's code (a constructor by index), since only Reussir can make
//! the dummy's handle.

use crate::big::LBig;
use crate::nat::{LInt, LNat};
use crate::string::LStr;
use reussir_rt::rc::Rc;
use std::mem::{forget, size_of, transmute_copy};
use std::sync::atomic::{AtomicPtr, Ordering};

// A box is one 64-bit word (the encoding needs 16 spare bits above a
// 48-bit address).
const _: () = assert!(usize::BITS == 64);

/// The bits of a pointer word that hold the address.
pub const ADDR_BITS: u32 = 48;
pub const ADDR_MASK: u64 = (1 << ADDR_BITS) - 1;

/// leanrt's payload kinds (the program's start at `FIRST_PROGRAM_NUM`).
/// A big `Nat` (an even `LNat` word: `LBig`).
pub const NUM_NAT: u64 = 1;
/// A big `Int` (an even `LInt` word: `LBig`).
pub const NUM_INT: u64 = 2;
/// A `String` (`LStr`).
pub const NUM_STR: u64 = 3;
/// A `Float` in a cell (`Rc<f64>`).
pub const NUM_F64: u64 = 4;
/// A `UInt64`/`USize` from 2^63 in a cell (`Rc<u64>`).
pub const NUM_U64: u64 = 5;
/// An `Array` of boxes (`RVec<LAny>`).
pub const NUM_ARRAY: u64 = 6;
/// A `ByteArray` (`RVec<u8>`); also a compact `Array` of `UInt8`, `Bool` or
/// an enumeration of at most 256 constructors (lean2rr's compact scalar
/// arrays: the elements as their storage type, not boxes).
pub const NUM_BYTES: u64 = 7;
/// A `FloatArray` (`RVec<f64>`); also a compact `Array Float`.
pub const NUM_FLOATS: u64 = 8;
/// A compact `Array UInt16` (`RVec<u16>`).
pub const NUM_U16S: u64 = 9;
/// A compact `Array UInt32` or `Array Char` (`RVec<u32>`).
pub const NUM_U32S: u64 = 10;
/// A compact `Array UInt64` or `Array USize` (`RVec<u64>`).
pub const NUM_U64S: u64 = 11;
/// A compact `Array Float32` (`RVec<f32>`).
pub const NUM_F32S: u64 = 12;
pub const FIRST_PROGRAM_NUM: u64 = 16;
/// The bit of a program payload number that marks a leaf type: a record or
/// enum without counted or observable members (its fields are scalars), so
/// that freeing it frees nothing else. lean2rr numbers leaf types with it
/// (`release_last`).
pub const LEAF_BIT: u64 = 0x8000;
/// The bit of a program payload number without `LEAF_BIT` that marks a
/// type whose Reussir cell has a wide header: its first 8 bytes are the
/// 32-bit count, then a 32-bit word that is padding or a fused tag below
/// 2^16 (Reussir's `hasWideHeader`: a shared enum of at most 2^16
/// constructors, or a shared struct whose alignment is 8). lean2rr numbers
/// such types with it (`boxIsWide`); `release_last` defers their cells with
/// `__reussir_drop_defer_wide`, which links a cell to the run on top
/// through that header. Not meaningful on a leaf number (a leaf is never
/// deferred; leaf numbers from `LEAF_BIT | WIDE_BIT` up have the bit set
/// as part of their count).
pub const WIDE_BIT: u64 = 0x4000;
pub const MAX_NUM: u64 = (1 << (64 - ADDR_BITS)) - 1;

/// A boxed value (see the module comment): one word, owning one reference
/// when it is even.
#[repr(transparent)]
pub struct LAny(*mut u8);

#[inline(always)]
fn ptr_of(w: u64) -> *mut u8 {
    std::ptr::with_exposed_provenance_mut(w as usize)
}

/// Whether `w` is an immediate.
#[inline(always)]
pub fn is_imm(w: u64) -> bool {
    w & 1 == 1
}

/// The payload number of a pointer word.
#[inline(always)]
pub fn num_of(w: u64) -> u64 {
    w >> ADDR_BITS
}

/// The address of a pointer word's object.
#[inline(always)]
pub fn addr_of(w: u64) -> usize {
    (w & ADDR_MASK) as usize
}

impl LAny {
    /// The word (the handle keeps its reference).
    #[inline(always)]
    pub fn word(&self) -> u64 {
        self.0.expose_provenance() as u64
    }

    /// The word, owning the handle's reference.
    #[inline(always)]
    pub fn into_raw(self) -> u64 {
        let w = self.word();
        forget(self);
        w
    }

    /// The handle of a word that owns its reference (or is an immediate).
    #[inline(always)]
    pub unsafe fn from_raw(w: u64) -> LAny {
        LAny(ptr_of(w))
    }

    /// The immediate of `v` (below 2^63).
    #[inline(always)]
    pub fn imm(v: u64) -> LAny {
        debug_assert!(v >> 63 == 0);
        LAny(ptr_of((v << 1) | 1))
    }

    /// Lean's `box(0)`.
    #[inline(always)]
    pub fn unit() -> LAny {
        LAny::imm(0)
    }

    #[inline(always)]
    pub fn is_imm(&self) -> bool {
        is_imm(self.word())
    }

    /// The value of an immediate.
    #[inline(always)]
    pub fn imm_value(&self) -> u64 {
        debug_assert!(self.is_imm());
        self.word() >> 1
    }

    /// The payload number of a pointer (0 for an immediate).
    #[inline(always)]
    pub fn num(&self) -> u64 {
        let w = self.word();
        if is_imm(w) { 0 } else { num_of(w) }
    }

    /// The payload's count (a pointer only).
    #[inline(always)]
    fn count_ptr(&self) -> *mut u32 {
        self.0.mask(ADDR_MASK as usize) as *mut u32
    }

    /// Whether the handle is the only reference to its payload (an
    /// immediate is never shared).
    #[inline(always)]
    pub fn is_exclusive(&self) -> bool {
        self.is_imm() || unsafe { *self.count_ptr() == 1 }
    }

    /// `ptrAddrUnsafe`: the payload's address, or an immediate's own word
    /// (natively the word of a boxed scalar).
    #[inline(always)]
    pub fn addr(&self) -> u64 {
        let w = self.word();
        if is_imm(w) { w } else { w & ADDR_MASK }
    }
}

impl Clone for LAny {
    /// An immediate is copied; a pointer's payload count goes up (the
    /// count is at least 1 for a live reference).
    #[inline(always)]
    fn clone(&self) -> LAny {
        // The word is read once: after the store to the count, a second
        // read of `self` (which may alias the count, as far as LLVM knows)
        // would be a second load.
        let w = self.0;
        if w.addr() & 1 == 0 {
            unsafe {
                let p = w.mask(ADDR_MASK as usize) as *mut u32;
                let c = *p;
                std::hint::assert_unchecked(c != 0);
                *p = c + 1;
            }
        }
        LAny(w)
    }
}

impl Drop for LAny {
    /// A shared payload is a decrement; the last reference goes to
    /// `release_last`, out of line. The test is `count == 1`, as for the
    /// other handles (`drop::Vec`).
    #[inline(always)]
    fn drop(&mut self) {
        if !self.is_imm() {
            unsafe {
                let p = self.count_ptr();
                let c = *p;
                if c == 1 {
                    release_last(self.word());
                } else {
                    *p = c - 1;
                }
            }
        }
    }
}

impl crate::Release for LAny {
    #[inline(always)]
    fn release(self) {
        drop(self)
    }
}

/// A program payload type's release, as the program gives it (`install`):
/// its payload number and the release of a cell of it whose count is 1
/// (lean2rr's `l2r_any_rel_<num>_c(cell)`, an `extern "C" trampoline` of a
/// generated Reussir function that takes the payload at its type and drops
/// it).
pub struct Rel(pub u16, pub unsafe extern "C" fn(*mut u8));

/// The program's release of each payload number (16 to 65535; leanrt's own
/// kinds, 1 to 15, have none; null: none installed). Filled before `main`
/// (`init_releases`, from `rt::run_main2`); a program never changes it
/// afterwards. Only tests install entries later: leanrt's unit tests (their
/// own numbers), and the box probe (`tests/runtime/any-probe`),
/// whose `probe_install` runs after `main` has started, for its numbers
/// 1016 to 1029, which its host program does not use. In `.bss`: only the
/// pages of the numbers in use are touched.
static RELEASES: [AtomicPtr<()>; 1 << 16] = [const { AtomicPtr::new(std::ptr::null_mut()) }; 1 << 16];

/// Install a program's releases (lean2rr's generated `l2r_any_releases`, a
/// texture that the trampoline `l2r_any_init_c` calls, before `main`; a
/// test's own, also later: see `RELEASES`). An entry installed again gets
/// the same value. 0.
pub fn install(rels: &[Rel]) -> u64 {
    for r in rels {
        let n = r.0 as usize;
        assert!(n as u64 >= FIRST_PROGRAM_NUM, "leanrt: a release for payload number {n} (below 16)");
        RELEASES[n].store(r.1 as *mut (), Ordering::Release);
    }
    0
}

extern "C" {
    /// The program's installation of its releases: lean2rr's generated
    /// `l2r_any_init() -> u64` (it calls the texture `l2r_any_releases`,
    /// whose static table names every `l2r_any_rel_<num>_c`), exported as
    /// `extern "C" trampoline "l2r_any_init_c" = l2r_any_init;`. Weak:
    /// null in a program that boxes no payload of its own.
    #[linkage = "extern_weak"]
    static l2r_any_init_c: *const std::ffi::c_void;
}

static INIT: std::sync::Once = std::sync::Once::new();

/// Install the program's releases, once (`rt::run_main2` calls this first,
/// before the initializers and before any other thread runs).
pub fn init_releases() {
    INIT.call_once(|| {
        let f = unsafe { l2r_any_init_c };
        if !f.is_null() {
            let f = unsafe { std::mem::transmute::<*const std::ffi::c_void, unsafe extern "C" fn() -> u64>(f) };
            unsafe { f() };
        }
    });
}

/// Release the payload of the pointer word `w`, whose count is 1 (the
/// reference given up). A program payload (tested first) goes to the
/// release of its type (`RELEASES`) through the worklist: its cell (the
/// word without the number) is deferred as one pending cell, the rule of
/// `drop::free_unique` for records (`drop::free_deferred`: Reussir's
/// `__reussir_drop_defer`, which neither reads nor writes the cell, then
/// its drain; `drop::free_deferred_wide` for a number with `WIDE_BIT`).
/// Inside a free it is only pushed; outside one Reussir's drain releases
/// it and then what it pushed (`drain_one`). So nested boxes are released
/// one after the other, not by recursion, and what a payload holds in
/// native Lean's order. A leaf payload is released directly, inside a free
/// too (`LEAF_BIT`: its release frees its own cell and nothing else, so it
/// has no member to order, cannot recurse and pushes nothing). leanrt's
/// own kinds are dropped as their types (`release_kind`). `extern "C"`: no
/// unwinding, so the textures that drop an `LAny` need no landing pad.
/// `#[cold]`, though the last reference of a boxed record is common: the
/// drops in a loop then keep their decrement in line and the call out of
/// the way (without it, sieve +0.5 % instructions from the loop's layout;
/// monadic-interp, which frees a boxed record per step, -0.1 %).
#[cold]
#[inline(never)]
pub extern "C" fn release_last(w: u64) {
    let num = num_of(w);
    if num >= FIRST_PROGRAM_NUM {
        let f = RELEASES[num as usize].load(Ordering::Relaxed);
        if f.is_null() {
            return release_unregistered(w);
        }
        let f = unsafe { std::mem::transmute::<*mut (), unsafe extern "C" fn(*mut u8)>(f) };
        let cell = ptr_of(w).mask(ADDR_MASK as usize);
        if num & LEAF_BIT != 0 {
            return unsafe { f(cell) };
        }
        if num & WIDE_BIT != 0 {
            return unsafe { crate::drop::free_deferred_wide(cell as usize, f) };
        }
        return unsafe { crate::drop::free_deferred(cell as usize, f) };
    }
    release_kind(w, num)
}

/// `release_last` of a box's last reference in a step of a running free
/// that returns to the drain as soon as the stack's depth changes (the
/// array free's second pass, `drop::ReleaseElems for LAny`), for any kept
/// element but the last: a program payload's release, leaf or not, is
/// called at once instead of being deferred. Deferred, the cell would be
/// the only entry above the step, popped next with the step as the top
/// entry again: the same release, at the same point, with the same stack
/// (the argument is at the caller). leanrt's own kinds, and a payload
/// without a release: `release_last` (a leaf kind is freed at once, an
/// array pushes its step).
#[inline(always)]
pub(crate) unsafe fn release_last_in_step(w: u64) {
    let num = num_of(w);
    if num >= FIRST_PROGRAM_NUM {
        let f = RELEASES[num as usize].load(Ordering::Relaxed);
        if !f.is_null() {
            let f = unsafe { std::mem::transmute::<*mut (), unsafe extern "C" fn(*mut u8)>(f) };
            return unsafe { f(ptr_of(w).mask(ADDR_MASK as usize)) };
        }
    }
    release_last(w)
}

/// Whether `release_last` of the pointer word `w` outside a free frees it
/// without a step of its own and without recursion: a program payload (in
/// a drain of its own, `drop::free_deferred`, or a leaf's release directly)
/// or one of leanrt's leaves (a big number, a string, a scalar cell: one
/// block freed at once), for `drop::ReleaseElems::free_single`. Not an
/// array of boxes (`NUM_ARRAY`): its release is `drop::free_vec` again,
/// which would recurse through a deep nesting of one-element arrays. Not an
/// array of scalars (`NUM_BYTES` to `NUM_F32S`: a `ByteArray`, a
/// `FloatArray`, a compact `Array` of scalars) either, whose free is one
/// `mi_free` without recursion: the case is rare, so it keeps the step.
#[inline(always)]
pub(crate) fn frees_flat(w: u64) -> bool {
    let num = num_of(w);
    num >= FIRST_PROGRAM_NUM || matches!(num, NUM_NAT | NUM_INT | NUM_STR | NUM_F64 | NUM_U64)
}

// A payload's cell is deferred with `__reussir_drop_defer_wide` only when
// lean2rr marks its number with `WIDE_BIT`, Reussir's own rule for the
// cell's header (a function value's enum too); the other cells (an array, a
// runtime object such as a thunk's or task's cell, a struct without an
// 8-byte member) with `__reussir_drop_defer`,
// one entry of the stack's vector each when they follow one another inside
// a free (24 bytes; Reussir's glue releases a list's heads one after the
// other before the drain pops any of them). The wide deferral costs about 3
// instructions more where the stack is empty (no link can form there:
// outside a free, where most payloads are released).

/// `release_last` of one of leanrt's kinds: leaves are freed at once,
/// arrays free their elements through the worklist themselves.
#[inline(never)]
extern "C" fn release_kind(w: u64, num: u64) {
    let p = ptr_of(w).mask(ADDR_MASK as usize);
    unsafe {
        match num {
            NUM_NAT | NUM_INT => drop(std::mem::transmute::<*mut u8, LBig>(p)),
            NUM_STR => drop(std::mem::transmute::<*mut u8, LStr>(p)),
            // A scalar cell holds nothing to drop.
            NUM_F64 | NUM_U64 => crate::alloc::free(p),
            NUM_ARRAY => drop(std::mem::transmute::<*mut u8, crate::drop::Vec<LAny>>(p)),
            // The arrays of scalars: one block, freed at once.
            NUM_BYTES => drop(std::mem::transmute::<*mut u8, crate::drop::Vec<u8>>(p)),
            NUM_FLOATS => drop(std::mem::transmute::<*mut u8, crate::drop::Vec<f64>>(p)),
            NUM_U16S => drop(std::mem::transmute::<*mut u8, crate::drop::Vec<u16>>(p)),
            NUM_U32S => drop(std::mem::transmute::<*mut u8, crate::drop::Vec<u32>>(p)),
            NUM_U64S => drop(std::mem::transmute::<*mut u8, crate::drop::Vec<u64>>(p)),
            NUM_F32S => drop(std::mem::transmute::<*mut u8, crate::drop::Vec<f32>>(p)),
            _ => mismatch(w, num),
        }
    }
}

/// A program payload without a release: the releases are installed now if
/// they were not yet (a box released before `rt::run_main2`), else a
/// runtime bug (a line on descriptor 2, then Lean's internal panic).
#[cold]
#[inline(never)]
extern "C" fn release_unregistered(w: u64) {
    init_releases();
    if !RELEASES[num_of(w) as usize].load(Ordering::Acquire).is_null() {
        return release_last(w);
    }
    use std::io::Write;
    let _ = writeln!(std::io::stderr(), "leanrt: no release for the boxed payload number {} (l2r_any_init_c)", num_of(w));
    crate::lean_internal_panic(lean_runtime::semantics::panic::InternalPanic::Unreachable)
}

/// A boxed pointer, from the word `p` of a handle whose reference it takes
/// over and a payload number.
#[inline(always)]
pub unsafe fn of_ptr(p: u64, num: u64) -> LAny {
    if p >> ADDR_BITS != 0 || p & 1 != 0 || num == 0 || num > MAX_NUM {
        bad_pointer(p, num);
    }
    LAny(ptr_of((num << ADDR_BITS) | p))
}

/// A pointer that cannot be boxed (an address above 48 bits, an odd one, a
/// number outside 1 to 65535): a line on descriptor 2, then Lean's internal
/// panic (`extern "C"`: a Rust panic here would abort without a message).
#[cold]
#[inline(never)]
extern "C" fn bad_pointer(p: u64, num: u64) -> ! {
    use std::io::Write;
    let _ = writeln!(
        std::io::stderr(),
        "leanrt: cannot box the pointer {p:#x} as payload {num}: an address must fit in 48 bits and be even, a number be 1 to 65535"
    );
    crate::lean_internal_panic(lean_runtime::semantics::panic::InternalPanic::Unreachable)
}

/// A value at type `num` that is not what the box holds: an unboxing that
/// lean2rr proved unreachable (`l2r_unreachable`), a panic, never a read.
#[cold]
#[inline(never)]
pub extern "C" fn mismatch(w: u64, num: u64) -> ! {
    if std::env::var_os("L2R_ANY_DEBUG").is_some() {
        use std::io::Write;
        let _ = writeln!(std::io::stderr(), "leanrt: unboxing {w:#x} at payload {num}");
    }
    crate::lean_internal_panic(lean_runtime::semantics::panic::InternalPanic::Unreachable)
}

/// How values of a type go into and out of a box: the generic textures
/// (`l2r_any_of<T>`, `l2r_any_as<T>`) call these. The default is a handle of
/// one word whose block starts with its `u32` count (an FFI type of the
/// prelude: `LStr`, `RVec`, `LCell`, `LHandle`).
pub trait Payload: Sized {
    /// Box `self` (its reference taken over) as payload `num`.
    fn into_any(self, num: u64) -> LAny;
    /// The payload of `w` (a word owning its reference) at payload `num`;
    /// a mismatch panics (`mismatch`).
    unsafe fn from_any_word(w: u64, num: u64) -> Self;
}

/// The word of a one-word handle, its reference taken over. Read as a
/// pointer and exposed (`take_word` gets it back with
/// `with_exposed_provenance`), so the address keeps its provenance.
#[inline(always)]
fn word_of<T>(x: T) -> u64 {
    const { assert!(size_of::<T>() == size_of::<u64>()) };
    let p: *mut u8 = unsafe { transmute_copy(&x) };
    forget(x);
    p.expose_provenance() as u64
}

#[inline(always)]
unsafe fn take_word<T>(w: u64) -> T {
    const { assert!(size_of::<T>() == size_of::<u64>()) };
    let a = ptr_of(w).mask(ADDR_MASK as usize);
    unsafe { transmute_copy::<*mut u8, T>(&a) }
}

impl<T> Payload for T {
    #[inline(always)]
    default fn into_any(self, num: u64) -> LAny {
        unsafe { of_ptr(word_of(self), num) }
    }
    #[inline(always)]
    default unsafe fn from_any_word(w: u64, num: u64) -> T {
        if is_imm(w) || num_of(w) != num {
            if w == 1 {
                unit_at_program_type(num);
            }
            mismatch(w, num);
        }
        unsafe { take_word(w) }
    }
}

/// A Reussir record or enum (`Bridge<Inner>`, a pointer to its box). A
/// nullary variant (a Reussir immediate, see the module comment) is boxed
/// as the immediate of its index; it cannot be unboxed here (the program
/// makes it), so `from_any_word` takes pointers only.
impl<X> Payload for reussir_rt::bridge::Bridge<X> {
    #[inline(always)]
    fn into_any(self, num: u64) -> LAny {
        let p = word_of(self);
        // `tbi`: the top byte is `tag + 1`.
        if p >> 56 != 0 {
            return LAny::imm((p >> 56) - 1);
        }
        // `immortal`: the dummy's count is at least 2^31 (a real box's never
        // is), and its tag the next `u32`.
        let c = unsafe { *(ptr_of(p) as *const u32) };
        if c >= crate::drop::IMMORTAL {
            return LAny::imm(unsafe { *(ptr_of(p) as *const u32).add(1) } as u64);
        }
        unsafe { of_ptr(p, num) }
    }
    #[inline(always)]
    unsafe fn from_any_word(w: u64, num: u64) -> Self {
        if is_imm(w) || num_of(w) != num {
            if w == 1 {
                unit_at_program_type(num);
            }
            mismatch(w, num);
        }
        unsafe { take_word(w) }
    }
}

/// `box(0)` met by the generic unbox at a program type: the program, not
/// leanrt, makes that type's zero, so a generated unbox must split
/// immediates first. A line on descriptor 2 that names the rule, then
/// Lean's internal panic.
#[cold]
#[inline(never)]
extern "C" fn unit_at_program_type(num: u64) -> ! {
    use std::io::Write;
    let _ = writeln!(
        std::io::stderr(),
        "leanrt: box(0) unboxed at program payload {num} by l2r_any_as: a generated unbox must split immediates first (l2r_any_raw_is_imm; the rule above l2r_any_as in the prelude)"
    );
    crate::lean_internal_panic(lean_runtime::semantics::panic::InternalPanic::Unreachable)
}

/// A `Nat`: a small one is its own word (an immediate), a big one a
/// pointer of kind `NUM_NAT` (the `num` argument is not used).
impl Payload for LNat {
    #[inline(always)]
    fn into_any(self, _num: u64) -> LAny {
        of_nat(self)
    }
    #[inline(always)]
    unsafe fn from_any_word(w: u64, _num: u64) -> Self {
        nat_of_word(w)
    }
}

impl Payload for LInt {
    #[inline(always)]
    fn into_any(self, _num: u64) -> LAny {
        of_int(self)
    }
    #[inline(always)]
    unsafe fn from_any_word(w: u64, _num: u64) -> Self {
        int_of_word(w)
    }
}

/// leanrt's own payload kinds have fixed numbers, whatever `num` says, so
/// that `release_last` drops each as its type. Lean's `box(0)` (word 1)
/// read at one of them is its zero (`$zero`; `None`: never asked, the
/// cells are read through `as_f64`/`as_u64`), as lean2rr's `b0` arm gives
/// the zero of the type; any other immediate is a mismatch.
macro_rules! leanrt_kind {
    ($t:ty, $num:expr, $zero:expr) => {
        impl Payload for $t {
            #[inline(always)]
            fn into_any(self, _num: u64) -> LAny {
                unsafe { of_ptr(word_of(self), $num) }
            }
            #[inline(always)]
            unsafe fn from_any_word(w: u64, _num: u64) -> Self {
                if is_imm(w) || num_of(w) != $num {
                    let zero: Option<fn() -> $t> = $zero;
                    match zero {
                        Some(z) if w == 1 => return z(),
                        _ => mismatch(w, $num),
                    }
                }
                unsafe { take_word(w) }
            }
        }
    };
}
leanrt_kind!(LStr, NUM_STR, Some(|| crate::string::from_bytes(b"")));
leanrt_kind!(Rc<f64>, NUM_F64, None);
leanrt_kind!(Rc<u64>, NUM_U64, None);
// The arrays of scalars. An array of boxes in one of these boxes is a
// mismatch (the reverse of the conversion below is not made).
leanrt_kind!(crate::drop::Vec<u8>, NUM_BYTES, Some(crate::array::empty::<u8>));
leanrt_kind!(crate::drop::Vec<f64>, NUM_FLOATS, Some(crate::array::empty::<f64>));
leanrt_kind!(crate::drop::Vec<u16>, NUM_U16S, Some(crate::array::empty::<u16>));
leanrt_kind!(crate::drop::Vec<u32>, NUM_U32S, Some(crate::array::empty::<u32>));
leanrt_kind!(crate::drop::Vec<u64>, NUM_U64S, Some(crate::array::empty::<u64>));
leanrt_kind!(crate::drop::Vec<f32>, NUM_F32S, Some(crate::array::empty::<f32>));

/// `RVec<LAny>` (number 6); also the prelude's `LRef<LAny>`, the same Rust
/// type (generated code does not use `LRef`). As `leanrt_kind!`: `box(0)`
/// unboxes to an empty array, any other immediate is a mismatch. One more
/// case, the safety net of lean2rr's compact scalar arrays: an array of
/// scalars (`NUM_BYTES` to `NUM_F32S`) unboxed here is converted to an
/// array of boxes (`boxes_of_compact`). lean2rr's whole-program check keeps
/// a compact array from every place that reads it as an array of boxes
/// (`Array lcAny`), so this does not happen; if it does, the result is the
/// same as with the boxes, at the cost of a copy.
impl Payload for crate::drop::Vec<LAny> {
    #[inline(always)]
    fn into_any(self, _num: u64) -> LAny {
        unsafe { of_ptr(word_of(self), NUM_ARRAY) }
    }
    #[inline(always)]
    unsafe fn from_any_word(w: u64, _num: u64) -> Self {
        if is_imm(w) || num_of(w) != NUM_ARRAY {
            if w == 1 {
                return crate::array::empty::<LAny>();
            }
            return boxes_of_compact(w);
        }
        unsafe { take_word(w) }
    }
}

/// The array of boxes of the array of scalars that the pointer word `w`
/// (owning its reference) holds: a new array of the same size whose
/// elements are the scalars boxed as lean2rr boxes them
/// (`array::boxes_of_scalars`), the reference to the source given up. Any
/// other word is a mismatch at `NUM_ARRAY`. With the environment variable
/// `L2R_DEBUG_ARRAY_CONVERT` set, each conversion writes a line on
/// descriptor 2 (`report_conversion`): tests check that none happens.
#[cold]
#[inline(never)]
extern "C" fn boxes_of_compact(w: u64) -> crate::drop::Vec<LAny> {
    use crate::drop::Vec as V;
    let num = if is_imm(w) { 0 } else { num_of(w) };
    unsafe {
        match num {
            NUM_BYTES => convert_compact(take_word::<V<u8>>(w), num),
            NUM_FLOATS => convert_compact(take_word::<V<f64>>(w), num),
            NUM_U16S => convert_compact(take_word::<V<u16>>(w), num),
            NUM_U32S => convert_compact(take_word::<V<u32>>(w), num),
            NUM_U64S => convert_compact(take_word::<V<u64>>(w), num),
            NUM_F32S => convert_compact(take_word::<V<f32>>(w), num),
            _ => mismatch(w, NUM_ARRAY),
        }
    }
}

#[inline(always)]
fn convert_compact<T: crate::array::BoxScalar>(src: crate::drop::Vec<T>, num: u64) -> crate::drop::Vec<LAny> {
    report_conversion(num, src.len());
    crate::array::boxes_of_scalars(src)
}

/// The line of a conversion (`boxes_of_compact`) when
/// `L2R_DEBUG_ARRAY_CONVERT` is set (read once).
fn report_conversion(num: u64, len: usize) {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    if *ON.get_or_init(|| std::env::var_os("L2R_DEBUG_ARRAY_CONVERT").is_some()) {
        use std::io::Write;
        let _ = writeln!(std::io::stderr(), "leanrt: compact array of kind {num} converted to boxes ({len} elements)");
    }
}

/// The 8-byte scalars a texture can be instantiated at: a `UInt64` or
/// `USize` (and the bits of an `Int64` or `ISize`) boxes as `of_u64` (an
/// immediate below 2^63, a cell from there), a `Float` as `of_f64` (a
/// cell). `num` is not used. Smaller scalars do not fit the generic impl
/// (a compile-time error in the texture): they have their own helpers.
macro_rules! word_scalar {
    ($t:ty) => {
        impl Payload for $t {
            #[inline(always)]
            fn into_any(self, _num: u64) -> LAny {
                of_u64(self as u64)
            }
            #[inline(always)]
            unsafe fn from_any_word(w: u64, _num: u64) -> Self {
                u64_of_word(w) as $t
            }
        }
    };
}
word_scalar!(u64);
word_scalar!(i64);
word_scalar!(usize);
word_scalar!(isize);

impl Payload for f64 {
    #[inline(always)]
    fn into_any(self, _num: u64) -> LAny {
        of_f64(self)
    }
    #[inline(always)]
    unsafe fn from_any_word(w: u64, _num: u64) -> Self {
        f64_of_word(w)
    }
}

/// A box boxed again is itself (`num` is not used).
impl Payload for LAny {
    #[inline(always)]
    fn into_any(self, _num: u64) -> LAny {
        self
    }
    #[inline(always)]
    unsafe fn from_any_word(w: u64, _num: u64) -> Self {
        unsafe { LAny::from_raw(w) }
    }
}

/// A function value (a lean2rr function-value enum) boxed as payload
/// `num` (`l2r_any_of_fn<T>`): a nullary variant becomes the immediate
/// `(num << 32) | index`, which keeps its type (the index means nothing at
/// another representation of the function type, which lean2rr's unboxing
/// converts from); `box(0)` stays the immediate 0. Other values: `of`.
#[inline(always)]
pub fn of_typed<T>(x: T, num: u64) -> LAny {
    let a = x.into_any(num);
    if a.is_imm() {
        let v = a.imm_value();
        forget(a);
        return LAny::imm((num << 32) | v);
    }
    a
}

/// The bytes of a boxed `ByteArray`, borrowed from the box (`box(0)`: none):
/// the elements of an `Array ByteArray` (an array of boxes) that the
/// runtime reads in place (`net`'s sends).
pub fn bytes_ref(a: &LAny) -> &[u8] {
    let w = a.word();
    if is_imm(w) {
        return &[];
    }
    if num_of(w) != NUM_BYTES {
        mismatch(w, NUM_BYTES);
    }
    let o = ptr_of(w).mask(ADDR_MASK as usize) as *mut crate::drop::Hdr;
    unsafe { std::slice::from_raw_parts(crate::drop::elems::<u8>(o), (*o).len) }
}

/// The bytes of a boxed `String`, borrowed from the box (`box(0)`: none):
/// the elements of an `Array String` (an array of boxes) that the runtime
/// reads in place (a spawn's arguments, `proc::with_args`).
pub fn str_ref(a: &LAny) -> &[u8] {
    let w = a.word();
    if is_imm(w) {
        return &[];
    }
    if num_of(w) != NUM_STR {
        mismatch(w, NUM_STR);
    }
    unsafe { crate::string::bytes_at(ptr_of(w).mask(ADDR_MASK as usize)) }
}

/// `x` boxed as payload `num` (`l2r_any_of<T>`).
#[inline(always)]
pub fn of<T>(x: T, num: u64) -> LAny {
    x.into_any(num)
}

/// The payload of `a` at payload `num` (`l2r_any_as<T>`).
#[inline(always)]
pub fn as_<T>(a: LAny, num: u64) -> T {
    unsafe { T::from_any_word(a.into_raw(), num) }
}

/// The payload of the word `w` (owning its reference) at payload `num`
/// (`l2r_any_raw_as<T>`).
#[inline(always)]
pub unsafe fn raw_as<T>(w: u64, num: u64) -> T {
    unsafe { T::from_any_word(w, num) }
}

/// The payload of the pointer word `w` (owning its reference), unchecked:
/// the program's release, which has dispatched on the number already.
#[inline(always)]
pub unsafe fn raw_take<T>(w: u64) -> T {
    debug_assert!(!is_imm(w));
    unsafe { take_word(w) }
}

#[inline(always)]
pub fn of_nat(n: LNat) -> LAny {
    let w = n.into_raw();
    if is_imm(w) { LAny(ptr_of(w)) } else { unsafe { of_ptr(w, NUM_NAT) } }
}

#[inline(always)]
pub fn of_int(i: LInt) -> LAny {
    let w = i.into_raw();
    if is_imm(w) { LAny(ptr_of(w)) } else { unsafe { of_ptr(w, NUM_INT) } }
}

#[inline(always)]
unsafe fn nat_of_word(w: u64) -> LNat {
    if is_imm(w) {
        return unsafe { LNat::from_raw(w) };
    }
    if num_of(w) != NUM_NAT {
        mismatch(w, NUM_NAT);
    }
    unsafe { LNat::from_raw(w & ADDR_MASK) }
}

#[inline(always)]
unsafe fn int_of_word(w: u64) -> LInt {
    if is_imm(w) {
        return unsafe { LInt::from_raw(w) };
    }
    if num_of(w) != NUM_INT {
        mismatch(w, NUM_INT);
    }
    unsafe { LInt::from_raw(w & ADDR_MASK) }
}

/// A `Float` in a box: a cell, as natively.
#[inline]
pub fn of_f64(x: f64) -> LAny {
    let c = crate::alloc::rc_new(x);
    unsafe { of_ptr(word_of(c), NUM_F64) }
}

#[inline]
pub fn as_f64(a: LAny) -> f64 {
    f64_of_word(a.into_raw())
}

/// `box(0)` (word 1) is `0.0`, the zero of `Float`. A boxed `UInt64` (an
/// immediate, or its cell) gives its bits, as `unsafeCast` between
/// `UInt64` and `Float` reads them natively.
#[inline(always)]
fn f64_of_word(w: u64) -> f64 {
    if is_imm(w) {
        return f64::from_bits(w >> 1);
    }
    f64::from_bits(take_cell_bits(w, NUM_F64))
}

/// Whether the word `w` is a box that `bits_of_word` reads: an immediate,
/// or a float's or a large `UInt64`'s cell.
#[inline(always)]
pub fn is_word_box(w: u64) -> bool {
    is_imm(w) || matches!(num_of(w), NUM_F64 | NUM_U64)
}

/// The 64 bits that the box `w` holds as a `Float` or `UInt64`, the box
/// borrowed: an immediate's value (`box(0)`: 0), a cell's contents (a
/// float's and a large `UInt64`'s cells have one layout,
/// `alloc::rc_data`). Any other pointer is `mismatch`.
#[inline(always)]
pub fn bits_of_word(w: u64) -> u64 {
    if is_imm(w) {
        return w >> 1;
    }
    if !matches!(num_of(w), NUM_F64 | NUM_U64) {
        mismatch(w, NUM_F64);
    }
    unsafe { *crate::alloc::rc_data::<u64>(ptr_of(w).mask(ADDR_MASK as usize)) }
}

/// A `UInt64`/`USize`: an immediate below 2^63, a cell from there.
#[inline(always)]
pub fn of_u64(x: u64) -> LAny {
    if x >> 63 == 0 { LAny::imm(x) } else { of_u64_cell(x) }
}

#[cold]
#[inline(never)]
extern "C" fn of_u64_cell(x: u64) -> LAny {
    let c = crate::alloc::rc_new(x);
    unsafe { of_ptr(word_of(c), NUM_U64) }
}

#[inline(always)]
pub fn as_u64(a: LAny) -> u64 {
    u64_of_word(a.into_raw())
}

/// A boxed `Float` read as a `UInt64` gives its bits (`unsafeCast`).
#[inline(always)]
fn u64_of_word(w: u64) -> u64 {
    if is_imm(w) { w >> 1 } else { take_cell_bits(w, NUM_U64) }
}

/// The bits of the float's or large `UInt64`'s cell `w` (a word owning its
/// reference; any other pointer is `mismatch(w, num)`), the reference given
/// up: read in line (the two cells have one layout, `alloc::rc_data`), and
/// the cell freed with `mi_free` when this was its last reference (it
/// holds a plain scalar), else decremented. It was a call into a generic
/// `Rc` read and drop, about 21 instructions and Rust's deallocator
/// (mergesort reads 145 000 `UInt64` cells).
#[inline(always)]
fn take_cell_bits(w: u64, num: u64) -> u64 {
    if !matches!(num_of(w), NUM_F64 | NUM_U64) {
        mismatch(w, num);
    }
    let p = ptr_of(w).mask(ADDR_MASK as usize);
    unsafe {
        let x = *crate::alloc::rc_data::<u64>(p);
        let c = *(p as *const u32);
        if c == 1 {
            crate::alloc::free(p);
        } else {
            *(p as *mut u32) = c - 1;
        }
        x
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::RefCell;

    thread_local! {
        static LOG: RefCell<std::vec::Vec<u32>> = RefCell::new(std::vec::Vec::new());
    }

    fn take_log() -> std::vec::Vec<u32> {
        LOG.with(|l| std::mem::take(&mut *l.borrow_mut()))
    }

    /// A program payload (number 100): logs its release, holds a box.
    struct Node {
        id: u32,
        #[allow(dead_code)]
        next: LAny,
    }

    impl Drop for Node {
        fn drop(&mut self) {
            LOG.with(|l| l.borrow_mut().push(self.id));
        }
    }

    const NODE: u64 = 100;
    /// The same payload type under another number.
    const NODE2: u64 = 101;
    /// A leaf number (a `Node` whose `next` is unit).
    const LEAF: u64 = LEAF_BIT | 20;

    /// The test program's release of a cell of payload 100 or 101: an
    /// `Rc<Node>`.
    unsafe extern "C" fn release_node(cell: *mut u8) {
        drop(unsafe { take_word::<Rc<Node>>(cell as u64) });
    }

    /// The release of the leaf number: called directly, never deferred.
    unsafe extern "C" fn release_leaf(cell: *mut u8) {
        drop(unsafe { take_word::<Rc<Node>>(cell as u64) });
    }

    /// `Node` and `Probe` under numbers with `WIDE_BIT`: an `Rc`'s cell is
    /// the count, then 4 bytes of padding before the payload (aligned to 8:
    /// it holds a box), a wide header.
    const WIDE_NODE: u64 = WIDE_BIT | 22;
    const WIDE_PROBE: u64 = WIDE_BIT | 23;

    /// A program payload (number 105) that holds boxes in a vector, dropped
    /// in index order after the payload logs its id.
    struct Many {
        id: u32,
        #[allow(dead_code)]
        items: std::vec::Vec<LAny>,
    }

    impl Drop for Many {
        fn drop(&mut self) {
            LOG.with(|l| l.borrow_mut().push(self.id));
        }
    }

    const MANY: u64 = 105;

    unsafe extern "C" fn release_many(cell: *mut u8) {
        drop(unsafe { take_word::<Rc<Many>>(cell as u64) });
    }

    /// A payload that holds two boxes (numbers 102 and 103); Rust drops its
    /// fields in order, `a` then `b`, as Reussir's glue releases a record's
    /// fields.
    struct Pair {
        id: u32,
        #[allow(dead_code)]
        a: LAny,
        #[allow(dead_code)]
        b: LAny,
    }

    impl Drop for Pair {
        fn drop(&mut self) {
            LOG.with(|l| l.borrow_mut().push(self.id));
        }
    }

    const PAIR: u64 = 102;
    const PAIR2: u64 = 103;

    unsafe extern "C" fn release_pair(cell: *mut u8) {
        drop(unsafe { take_word::<Rc<Pair>>(cell as u64) });
    }

    thread_local! {
        static SEEN: RefCell<std::vec::Vec<(u32, bool, usize)>> = RefCell::new(std::vec::Vec::new());
    }

    fn take_seen() -> std::vec::Vec<(u32, bool, usize)> {
        SEEN.with(|l| std::mem::take(&mut *l.borrow_mut()))
    }

    /// A program payload (number 104, or the leaf number `LEAF_BIT | 21`
    /// when it holds no box) that logs, when its release starts, its id,
    /// whether a free runs and the depth of the stack of pending work.
    struct Probe {
        id: u32,
        #[allow(dead_code)]
        next: LAny,
    }

    impl Drop for Probe {
        fn drop(&mut self) {
            SEEN.with(|l| l.borrow_mut().push((self.id, crate::drop::active(), reussir_rt::drop::depth())));
        }
    }

    const PROBE: u64 = 104;
    const LEAF_PROBE: u64 = LEAF_BIT | 21;

    unsafe extern "C" fn release_probe(cell: *mut u8) {
        drop(unsafe { take_word::<Rc<Probe>>(cell as u64) });
    }

    fn probe(id: u32, next: LAny) -> LAny {
        of(crate::alloc::rc_new(Probe { id, next }), PROBE)
    }

    fn leaf_probe(id: u32) -> LAny {
        of(crate::alloc::rc_new(Probe { id, next: LAny::unit() }), LEAF_PROBE)
    }

    /// A step of pending work that logs its argument.
    unsafe fn step_mark(p: usize) -> bool {
        LOG.with(|l| l.borrow_mut().push(p as u32));
        true
    }

    fn install() {
        super::install(&[
            Rel(NODE as u16, release_node),
            Rel(NODE2 as u16, release_node),
            Rel(LEAF as u16, release_leaf),
            Rel(PAIR as u16, release_pair),
            Rel(PAIR2 as u16, release_pair),
            Rel(PROBE as u16, release_probe),
            Rel(LEAF_PROBE as u16, release_probe),
            Rel(WIDE_NODE as u16, release_node),
            Rel(WIDE_PROBE as u16, release_probe),
            Rel(MANY as u16, release_many),
        ]);
    }

    fn pair(id: u32, a: LAny, b: LAny, num: u64) -> LAny {
        of(crate::alloc::rc_new(Pair { id, a, b }), num)
    }

    fn node(id: u32, next: LAny) -> LAny {
        of(crate::alloc::rc_new(Node { id, next }), NODE)
    }

    fn count(a: &LAny) -> u32 {
        unsafe { *a.count_ptr() }
    }

    #[test]
    fn immediates() {
        let u = LAny::unit();
        assert_eq!(u.word(), 1);
        assert!(u.is_imm() && u.is_exclusive());
        assert_eq!(u.num(), 0);
        let m = LAny::imm((1 << 63) - 1);
        assert_eq!(m.imm_value(), (1 << 63) - 1);
        let c = m.clone();
        assert_eq!(c.word(), m.word());
        assert_eq!(as_u64(of_u64(42)), 42);
        assert_eq!(of_u64(7).word(), 15);
        assert_eq!(as_u64(of_u64(u64::MAX)), u64::MAX);
        assert_eq!(as_u64(of_u64(1 << 63)), 1 << 63);
        assert_eq!(as_f64(of_f64(-2.5)), -2.5);
        assert!(as_f64(of_f64(f64::NAN)).is_nan());
    }

    #[test]
    fn small_and_big_numbers() {
        // A small Nat is its own word.
        let n = of_nat(LNat::small(5));
        assert_eq!(n.word(), 11);
        assert_eq!(as_::<LNat>(n, 0).low_u64(), 5);
        // A big Nat: a pointer of kind NUM_NAT, shared by copies.
        let b = of_nat(LNat::of_u64(u64::MAX));
        assert_eq!(b.num(), NUM_NAT);
        let b2 = b.clone();
        assert_eq!(count(&b), 2);
        assert_eq!(as_::<LNat>(b2, 0).low_u64(), u64::MAX);
        assert_eq!(count(&b), 1);
        drop(b);
        // A big Int.
        let i = of_int(LInt::of_i64(i64::MIN));
        assert_eq!(i.num(), NUM_INT);
        drop(i);
        let s = of_int(LInt::of_i64(-3));
        assert!(s.is_imm());
        drop(as_::<LInt>(s, 0));
    }

    #[test]
    fn strings_and_arrays() {
        let s = of(crate::string::from_bytes(b"hello"), NUM_STR);
        assert_eq!(s.num(), NUM_STR);
        assert!(s.is_exclusive());
        let t = s.clone();
        assert!(!s.is_exclusive());
        let back: LStr = as_(t, NUM_STR);
        assert_eq!(crate::string::bytes(&back), b"hello");
        drop(back);
        assert!(s.is_exclusive());
        drop(s);
        // An array of boxes, boxed itself: a copy of the array shares it;
        // dropping releases every element once.
        install();
        let mut v = crate::array::with_capacity::<LAny>(4);
        for i in 0..4 {
            v = crate::array::push(v, node(i, LAny::unit()));
        }
        let a = of(v, NUM_ARRAY);
        let a2 = a.clone();
        drop(a);
        assert!(take_log().is_empty());
        drop(a2);
        let mut log = take_log();
        log.sort();
        assert_eq!(log, vec![0, 1, 2, 3]);
    }

    #[test]
    fn program_payloads_and_sharing() {
        install();
        let a = node(1, LAny::imm(3));
        assert_eq!(a.num(), NODE);
        let copies: std::vec::Vec<LAny> = (0..10).map(|_| a.clone()).collect();
        assert_eq!(count(&a), 11);
        drop(copies);
        assert_eq!(count(&a), 1);
        assert!(take_log().is_empty());
        // Unboxed at its type: the same block, unique.
        let r: Rc<Node> = as_(a, NODE);
        assert!(r.is_unique());
        assert_eq!(r.data_ref().id, 1);
        let a = of(r, NODE);
        drop(a);
        assert_eq!(take_log(), vec![1]);
    }

    #[test]
    fn deep_chain_frees_without_recursion() {
        install();
        // Run on a small stack: a recursive free of 10^6 nodes would need
        // far more.
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                install();
                let mut a = LAny::unit();
                for i in 0..1_000_000 {
                    a = node(i, a);
                }
                drop(a);
                let log = take_log();
                assert_eq!(log.len(), 1_000_000);
                // The outermost node first, then inward.
                assert_eq!(log[0], 999_999);
                assert_eq!(log[999_999], 0);
            })
            .unwrap()
            .join()
            .unwrap();
    }

    /// A chain of three payload numbers in turn (two release functions, so
    /// that Reussir's runs mix them; one number with `WIDE_BIT`), on the
    /// same small stack: the same order.
    #[test]
    fn deep_chain_of_two_numbers() {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                install();
                let mut a = LAny::unit();
                for i in 0..1_000_000 {
                    a = of(crate::alloc::rc_new(Node { id: i, next: a }), [NODE2, NODE, WIDE_NODE][i as usize % 3]);
                }
                drop(a);
                let log = take_log();
                assert_eq!(log.len(), 1_000_000);
                assert!(log.iter().enumerate().all(|(k, &id)| id == 999_999 - k as u32));
                assert!(!crate::drop::active());
                assert_eq!(reussir_rt::drop::depth(), 0);
            })
            .unwrap()
            .join()
            .unwrap();
    }

    /// A payload's boxes are released in native Lean's order, the last
    /// field first and each completely before the one before it, outside a
    /// free and inside one (an array's free, which releases its elements
    /// from the last), whatever release functions their numbers have.
    #[test]
    fn fields_in_lean_order() {
        install();
        for (p, n) in [(PAIR, NODE), (PAIR, NODE2), (PAIR2, NODE), (PAIR2, NODE2), (PAIR, WIDE_NODE), (PAIR2, WIDE_NODE)] {
            let leaf = |id| of(crate::alloc::rc_new(Node { id, next: LAny::unit() }), n);
            let x = pair(1, leaf(2), of(crate::alloc::rc_new(Node { id: 3, next: leaf(4) }), n), p);
            drop(x);
            assert_eq!(take_log(), vec![1, 3, 4, 2], "pair {p}, node {n}");
            // Two pairs in an array: the last element first.
            let x = pair(10, leaf(11), leaf(12), p);
            let y = pair(20, leaf(21), pair(22, leaf(23), leaf(24), p), p);
            let v = crate::array::push(crate::array::push(crate::array::with_capacity::<LAny>(2), x), y);
            drop(of(v, NUM_ARRAY));
            assert_eq!(take_log(), vec![20, 22, 24, 23, 21, 10, 12, 11], "pair {p}, node {n}");
            assert_eq!(reussir_rt::drop::depth(), 0);
        }
    }

    /// An array of boxes freed from its last element: immediates skipped,
    /// a shared payload decremented, the unique payloads released last
    /// first, each completely (here a node holding a nested array) before
    /// the elements before it; outside a free and inside one. An array of
    /// immediates and shared payloads alone is freed without the stack.
    #[test]
    fn box_array_free() {
        install();
        let shared = node(50, LAny::unit());
        let mk = |shared: &LAny| {
            let inner = crate::array::push(crate::array::push(crate::array::empty::<LAny>(), node(31, LAny::imm(1))), node(32, LAny::unit()));
            let elems = [node(1, LAny::unit()), LAny::imm(7), shared.clone(), node(2, of(inner, NUM_ARRAY)), LAny::unit(), node(3, LAny::unit()), LAny::imm(9)];
            elems.into_iter().fold(crate::array::empty::<LAny>(), crate::array::push)
        };
        drop(of(mk(&shared), NUM_ARRAY));
        assert_eq!(take_log(), vec![3, 2, 32, 31, 1]);
        assert_eq!(count(&shared), 1);
        // Inside a free: the array is a node's field.
        drop(node(100, of(mk(&shared), NUM_ARRAY)));
        assert_eq!(take_log(), vec![100, 3, 2, 32, 31, 1]);
        assert_eq!(count(&shared), 1);
        // Immediates and shared payloads only.
        let v = [LAny::imm(1), shared.clone(), LAny::unit(), shared.clone()].into_iter().fold(crate::array::empty::<LAny>(), crate::array::push);
        assert_eq!(count(&shared), 3);
        drop(v);
        assert_eq!(count(&shared), 1);
        assert!(take_log().is_empty());
        assert_eq!(reussir_rt::drop::depth(), 0);
        drop(shared);
        assert_eq!(take_log(), vec![50]);
    }

    /// An array whose elements are shared inside it is freed in native
    /// Lean's two passes (`lean_del_core`): every element decremented in
    /// index order, then the ones whose count reached zero released last
    /// first. So a payload the array holds twice is released at its last
    /// index, and one that a later element also holds inside that
    /// element's release; outside a free and inside one. (From the last
    /// element while decrementing, the orders were 4 3 2 1 and 7 6 5.)
    #[test]
    fn box_array_free_shared_inside() {
        install();
        // [1, x, an immediate, 3, x, 4], x = node 2 held only by the array.
        let dup = || {
            let x = node(2, LAny::unit());
            [node(1, LAny::unit()), x.clone(), LAny::imm(5), node(3, LAny::unit()), x, node(4, LAny::unit())]
                .into_iter()
                .fold(crate::array::empty::<LAny>(), crate::array::push)
        };
        drop(of(dup(), NUM_ARRAY));
        assert_eq!(take_log(), vec![4, 2, 3, 1]);
        drop(node(100, of(dup(), NUM_ARRAY)));
        assert_eq!(take_log(), vec![100, 4, 2, 3, 1]);
        // [x, 6, node 7 holding x], x = node 5.
        let holder = || {
            let x = node(5, LAny::unit());
            [x.clone(), node(6, LAny::unit()), node(7, x)].into_iter().fold(crate::array::empty::<LAny>(), crate::array::push)
        };
        drop(of(holder(), NUM_ARRAY));
        assert_eq!(take_log(), vec![7, 5, 6]);
        drop(node(101, of(holder(), NUM_ARRAY)));
        assert_eq!(take_log(), vec![101, 7, 5, 6]);
        assert!(!crate::drop::active());
        assert_eq!(reussir_rt::drop::depth(), 0);
    }

    /// The second pass of an array free calls a kept payload's release in
    /// its step (`release_last_in_step`) instead of deferring it, but for
    /// the last kept element: the same releases in the same order, each
    /// with the stack the deferral's pop had (the array's step on top:
    /// depth 1 for an array freed outside a free; the last kept element is
    /// released after the step's entry is gone: depth 0), whether the
    /// payload is a leaf, pushes work or not; outside a free and inside
    /// one (the array a payload's field, also with other work pending
    /// below the array's step).
    #[test]
    fn box_array_free_releases_in_its_step() {
        install();
        let shared = probe(50, LAny::unit());
        let mk = |shared: &LAny| {
            [
                probe(1, LAny::unit()),
                probe(2, probe(3, LAny::imm(1))),
                of(crate::string::from_bytes(b"s"), NUM_STR),
                shared.clone(),
                probe(4, LAny::unit()),
                leaf_probe(5),
                LAny::imm(9),
                probe(6, LAny::unit()),
            ]
            .into_iter()
            .fold(crate::array::empty::<LAny>(), crate::array::push)
        };
        let want = vec![(6, true, 1), (5, true, 1), (4, true, 1), (2, true, 1), (3, true, 1), (1, true, 0)];
        drop(of(mk(&shared), NUM_ARRAY));
        assert_eq!(take_seen(), want);
        drop(probe(100, of(mk(&shared), NUM_ARRAY)));
        assert_eq!(take_seen(), [vec![(100, true, 0)], want.clone()].concat());
        // The array the second field of a pair whose first field, a
        // payload, is pushed before it: the step runs with that payload
        // below it (one entry more under each release), which comes out
        // last.
        drop(pair(200, probe(300, LAny::unit()), of(mk(&shared), NUM_ARRAY), PAIR));
        let below: std::vec::Vec<_> = want.iter().map(|&(id, a, d)| (id, a, d + 1)).collect();
        assert_eq!(take_seen(), [below, vec![(300, true, 0)]].concat());
        assert_eq!(take_log(), vec![200]);
        assert_eq!(count(&shared), 1);
        assert!(!crate::drop::active());
        assert_eq!(reussir_rt::drop::depth(), 0);
        drop(shared);
        assert_eq!(take_seen(), vec![(50, true, 0)]);
    }

    /// An array freed outside a free whose first pass keeps exactly one
    /// element, a program payload or one of leanrt's leaves, is freed
    /// without a step (`drop::ReleaseElems::free_single`): a payload's
    /// release runs in a drain of its own with nothing else on the stack,
    /// as the step's pop had it, and what it pushes after it; a leaf
    /// payload is released directly (outside a drain: the one difference a
    /// release can see). With work pending outside a drain, the step: its
    /// drain releases that work too before the free returns.
    #[test]
    fn one_kept_element_without_a_step() {
        install();
        let shared = probe(50, LAny::unit());
        let arr = |e: LAny, shared: &LAny| {
            [shared.clone(), LAny::imm(3), e, LAny::unit(), shared.clone()].into_iter().fold(crate::array::empty::<LAny>(), crate::array::push)
        };
        drop(arr(probe(1, probe(2, LAny::unit())), &shared));
        assert_eq!(take_seen(), vec![(1, true, 0), (2, true, 0)]);
        drop(arr(leaf_probe(3), &shared));
        assert_eq!(take_seen(), vec![(3, false, 0)]);
        for e in [
            of(crate::string::from_bytes(b"t"), NUM_STR),
            of_nat(LNat::of_u64(u64::MAX)),
            of_int(LInt::of_i64(i64::MIN)),
            of_f64(0.5),
            of_u64(u64::MAX),
        ] {
            assert!(!e.is_imm() && e.is_exclusive());
            drop(arr(e, &shared));
        }
        assert!(take_seen().is_empty());
        assert_eq!(count(&shared), 1);
        assert_eq!(reussir_rt::drop::depth(), 0);
        // Work pending outside a drain (as a record's `drop_in_place`
        // leaves it between the members it defers and its drain). The leaf,
        // the array's last kept element, is released directly in the
        // array's step, above the pending work (depth 2).
        crate::drop::defer(77, step_mark);
        drop(arr(leaf_probe(4), &shared));
        let (seen, log) = (take_seen(), take_log());
        if reussir_rt::drop::depth() != 0 {
            unsafe { reussir_rt::drop::__reussir_drop_drain() };
        }
        assert_eq!((seen, log), (vec![(4, true, 2)], vec![77]));
        assert_eq!(count(&shared), 1);
        assert!(!crate::drop::active());
        assert_eq!(reussir_rt::drop::depth(), 0);
    }

    /// A deep nesting of one-element arrays freed outside a free: the one
    /// element an array keeps is an array, which keeps the step (released
    /// directly, it would be freed by `free_vec` again, by recursion), so
    /// a small stack suffices.
    #[test]
    fn deep_nesting_of_one_element_arrays() {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                install();
                let mut a = probe(1, LAny::unit());
                for _ in 0..1_000_000 {
                    a = of(crate::array::push(crate::array::with_capacity::<LAny>(1), a), NUM_ARRAY);
                }
                drop(a);
                assert_eq!(take_seen(), vec![(1, true, 0)]);
                assert!(!crate::drop::active());
                assert_eq!(reussir_rt::drop::depth(), 0);
            })
            .unwrap()
            .join()
            .unwrap();
    }

    /// A shared array of boxes copied for an update: every pointer's
    /// payload count goes up once, the words are the same.
    #[test]
    fn box_array_copy() {
        install();
        let a = node(1, LAny::unit());
        let s = of(crate::string::from_bytes(b"s"), NUM_STR);
        let v = [LAny::imm(4), a.clone(), LAny::unit(), s.clone(), a.clone()].into_iter().fold(crate::array::empty::<LAny>(), crate::array::push);
        assert_eq!((count(&a), count(&s)), (3, 2));
        let w = crate::array::set(v.clone(), 0, LAny::imm(5));
        assert_eq!((count(&a), count(&s)), (5, 3));
        assert_eq!(w.as_slice().iter().map(|x| x.word()).skip(1).collect::<std::vec::Vec<_>>(), v.as_slice().iter().map(|x| x.word()).skip(1).collect::<std::vec::Vec<_>>());
        assert_eq!(w.as_slice()[0].word(), 11);
        drop((v, w));
        assert_eq!((count(&a), count(&s)), (1, 1));
        assert!(take_log().is_empty());
    }

    #[test]
    fn deep_chain_through_arrays() {
        install();
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                install();
                let mut a = LAny::unit();
                for i in 0..200_000 {
                    let v = crate::array::push(crate::array::with_capacity::<LAny>(1), a);
                    a = node(i, of(v, NUM_ARRAY));
                }
                drop(a);
                assert_eq!(take_log().len(), 200_000);
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn word_scalars_box_as_numbers() {
        // The generic textures at an 8-byte scalar: never a pointer box.
        assert_eq!(of(4096u64, 16).word(), (4096 << 1) | 1);
        assert_eq!(as_::<u64>(of(4096u64, 16), 16), 4096);
        assert_eq!(as_::<u64>(of(u64::MAX, 16), 16), u64::MAX);
        assert_eq!(of(u64::MAX, 16).num(), NUM_U64);
        assert_eq!(as_::<i64>(of(-5i64, 16), 16), -5);
        assert_eq!(as_::<usize>(of(7usize, 16), 16), 7);
        assert_eq!(as_::<isize>(of(isize::MIN, 16), 16), isize::MIN);
        let f = of(1.25f64, 16);
        assert_eq!(f.num(), NUM_F64);
        assert_eq!(as_::<f64>(f, 16), 1.25);
    }

    #[test]
    fn leanrt_kinds_ignore_the_number() {
        // A string boxed under a program number is still a string box.
        let s = of(crate::string::from_bytes(b"k"), 16);
        assert_eq!(s.num(), NUM_STR);
        drop(s);
        let v = of(crate::array::with_capacity::<LAny>(2), 40);
        assert_eq!(v.num(), NUM_ARRAY);
        let v: crate::drop::Vec<LAny> = as_(v, 40);
        drop(v);
        assert_eq!(of(crate::array::with_capacity::<u8>(2), 17).num(), NUM_BYTES);
        assert_eq!(of(crate::array::with_capacity::<f64>(2), 18).num(), NUM_FLOATS);
        assert_eq!(of(crate::array::with_capacity::<u16>(2), 19).num(), NUM_U16S);
        assert_eq!(of(crate::array::with_capacity::<u32>(2), 20).num(), NUM_U32S);
        assert_eq!(of(crate::array::with_capacity::<u64>(2), 21).num(), NUM_U64S);
        assert_eq!(of(crate::array::with_capacity::<f32>(2), 22).num(), NUM_F32S);
    }

    #[test]
    fn unit_is_the_zero_of_leanrt_kinds() {
        // Lean's box(0) read at each kind leanrt knows: its zero.
        assert_eq!(crate::string::bytes(&as_::<LStr>(LAny::unit(), NUM_STR)), b"");
        assert_eq!(as_::<crate::drop::Vec<LAny>>(LAny::unit(), NUM_ARRAY).len(), 0);
        assert_eq!(as_::<crate::drop::Vec<u8>>(LAny::unit(), NUM_BYTES).len(), 0);
        assert_eq!(as_::<crate::drop::Vec<f64>>(LAny::unit(), NUM_FLOATS).len(), 0);
        assert_eq!(as_::<crate::drop::Vec<u16>>(LAny::unit(), NUM_U16S).len(), 0);
        assert_eq!(as_::<crate::drop::Vec<u32>>(LAny::unit(), NUM_U32S).len(), 0);
        assert_eq!(as_::<crate::drop::Vec<u64>>(LAny::unit(), NUM_U64S).len(), 0);
        assert_eq!(as_::<crate::drop::Vec<f32>>(LAny::unit(), NUM_F32S).len(), 0);
        assert_eq!(as_f64(LAny::unit()), 0.0);
        assert_eq!(as_u64(LAny::unit()), 0);
        assert_eq!(as_::<LNat>(LAny::unit(), 0).low_u64(), 0);
        assert_eq!(crate::nat::int_of_small_word(as_::<LInt>(LAny::unit(), 0).into_raw()), 0);
    }

    /// A compact array of scalars boxed at its kind (whatever number is
    /// passed): the same block, unboxed back unique; a copy of the box
    /// shares the block (`is_shared`), and an update through an unboxed
    /// copy copies it; the persistent mark marks a block through its box; the last
    /// reference releases it (`release_last`, then `release_kind`), also
    /// inside a free (a payload's field) and as an element of an array of
    /// boxes (the array free's two passes, `release_last_in_step`).
    fn scalar_kind<T: Clone + Copy + PartialEq + std::fmt::Debug>(x: [T; 3], num: u64)
    where
        crate::drop::Vec<T>: Payload,
    {
        type V<T> = crate::drop::Vec<T>;
        install();
        let v = crate::array::from_slice(&x);
        let h = v.hdr();
        let a = of(v, 99);
        assert_eq!((a.num(), a.addr(), a.is_exclusive()), (num, h as u64, true));
        let v: V<T> = as_(a, 99);
        assert_eq!((v.hdr(), v.is_unique(), v.as_slice()), (h, true, &x[..]));
        // The persistent mark of another block of the kind, through its
        // box (`persist::mark_box`).
        let m = of(crate::array::from_slice(&x), num);
        assert!(!crate::persist::box_is_persistent(&m));
        crate::persist::mark_box(m.clone());
        assert!(crate::persist::box_is_persistent(&m) && !m.is_exclusive());
        // Shared: an update through a copy copies the block.
        let a = of(v, num);
        let b = a.clone();
        assert!(crate::is_shared(&a) && crate::is_shared(&b));
        let w: V<T> = as_(b, num);
        assert!(w.hdr() == h && crate::is_shared(&w));
        let w = crate::array::set(w, 0, x[2]);
        assert!(w.hdr() != h && w.is_unique());
        assert_eq!(w.as_slice(), &[x[2], x[1], x[2]]);
        assert!(a.is_exclusive());
        let v: V<T> = as_(a.clone(), num);
        assert_eq!(v.as_slice(), &x[..]);
        drop(v);
        drop(a);
        // A payload's field, released inside its free.
        drop(node(7, of(crate::array::from_slice(&x), num)));
        assert_eq!(take_log(), vec![7]);
        // Elements of an array of boxes, one of them shared.
        let keep = of(w, num);
        let arr = [of(crate::array::from_slice(&x), num), keep.clone(), LAny::imm(3), of(crate::array::empty::<T>(), num), node(8, LAny::unit())]
            .into_iter()
            .fold(crate::array::empty::<LAny>(), crate::array::push);
        assert_eq!(count(&keep), 2);
        drop(arr);
        assert_eq!((take_log(), count(&keep)), (vec![8], 1));
        let w: V<T> = as_(keep, num);
        assert_eq!(w.as_slice(), &[x[2], x[1], x[2]]);
        assert!(!crate::drop::active());
        assert_eq!(reussir_rt::drop::depth(), 0);
    }

    #[test]
    fn scalar_array_kinds() {
        scalar_kind([1u8, 0, 255], NUM_BYTES);
        scalar_kind([1.5f64, -0.0, f64::INFINITY], NUM_FLOATS);
        scalar_kind([1u16, 0, 0xffff], NUM_U16S);
        scalar_kind([0x41u32, 0x10ffff, u32::MAX], NUM_U32S);
        scalar_kind([1u64, 1 << 63, u64::MAX], NUM_U64S);
        scalar_kind([1.5f32, -0.0, f32::MAX], NUM_F32S);
    }

    /// The safety net: an array of scalars unboxed at `RVec<LAny>` is
    /// converted to boxes, each scalar boxed as lean2rr boxes it (an
    /// immediate; a `UInt64` from 2^63 and a `Float` a cell; a `Float32`
    /// its bits), the source released (a shared one decremented and kept as
    /// it is). `box(0)` is still the empty array, and an array of boxes the
    /// same block.
    #[test]
    fn compact_arrays_convert_at_an_array_of_boxes() {
        type V<T> = crate::drop::Vec<T>;
        let words = |v: &V<LAny>| v.as_slice().iter().map(|a| a.word()).collect::<std::vec::Vec<_>>();
        let imm = |x: u64| (x << 1) | 1;
        let conv = |a: LAny| -> V<LAny> { as_(a, NUM_ARRAY) };
        let v = conv(of(crate::array::from_slice(&[0u8, 1, 255]), 0));
        assert_eq!(words(&v), vec![1, imm(1), imm(255)]);
        let v = conv(of(crate::array::from_slice(&[0u16, 0x8000, 0xffff]), 0));
        assert_eq!(words(&v), vec![1, imm(0x8000), imm(0xffff)]);
        let v = conv(of(crate::array::from_slice(&[0x41u32, 0x10ffff, u32::MAX]), 0));
        assert_eq!(words(&v), vec![imm(0x41), imm(0x10ffff), imm(u32::MAX as u64)]);
        let v = conv(of(crate::array::from_slice(&[1.5f32, -0.0, f32::from_bits(0xffc0_0002)]), 0));
        assert_eq!(words(&v), vec![imm(1.5f32.to_bits() as u64), imm(0x8000_0000), imm(0xffc0_0002)]);
        let v = conv(of(crate::array::from_slice(&[5u64, (1 << 63) - 1, 1 << 63, u64::MAX]), 0));
        assert_eq!(&words(&v)[..2], &[imm(5), imm((1 << 63) - 1)]);
        assert_eq!(v.as_slice().iter().map(|a| a.num()).collect::<std::vec::Vec<_>>(), vec![0, 0, NUM_U64, NUM_U64]);
        assert_eq!(v.as_slice().iter().map(|a| as_u64(a.clone())).collect::<std::vec::Vec<_>>(), vec![5, (1 << 63) - 1, 1 << 63, u64::MAX]);
        let v = conv(of(crate::array::from_slice(&[2.5f64, -0.0, f64::NAN]), 0));
        assert!(v.as_slice().iter().all(|a| a.num() == NUM_F64 && a.is_exclusive()));
        let bits: std::vec::Vec<u64> = v.as_slice().iter().map(|a| as_f64(a.clone()).to_bits()).collect();
        assert_eq!(bits, vec![2.5f64.to_bits(), (-0.0f64).to_bits(), f64::NAN.to_bits()]);
        assert_eq!(conv(of(crate::array::empty::<u64>(), 0)).len(), 0);
        // A shared source: decremented, unchanged.
        let src = crate::array::from_slice(&[1u32, 2]);
        let v = conv(of(src.clone(), 0));
        assert_eq!((words(&v), src.is_unique(), src.as_slice()), (vec![imm(1), imm(2)], true, &[1u32, 2][..]));
        // The unboxing by word (`raw_as`) takes the same path.
        let v: V<LAny> = unsafe { raw_as(of(crate::array::from_slice(&[9u16]), 0).into_raw(), NUM_ARRAY) };
        assert_eq!(words(&v), vec![imm(9)]);
        // `box(0)`, an array of boxes.
        assert_eq!(conv(LAny::unit()).len(), 0);
        let b = crate::array::from_slice(&[LAny::imm(4)]);
        let h = b.hdr();
        assert_eq!(conv(of(b, 0)).hdr(), h);
    }

    /// The line `L2R_DEBUG_ARRAY_CONVERT` asks for (one per conversion, the
    /// kind and the size), and the reverse unboxing, an array of boxes at a
    /// compact kind, which stays a mismatch (here with `L2R_ANY_DEBUG`'s
    /// line): each in a child process (this test binary, this test only).
    #[test]
    fn conversion_line_and_reverse_mismatch() {
        type V<T> = crate::drop::Vec<T>;
        match std::env::var("LEANRT_TEST_CHILD").as_deref() {
            Ok("convert") => {
                let v: V<LAny> = as_(of(crate::array::from_slice(&[1u16, 2, 3]), 0), NUM_ARRAY);
                let e: V<LAny> = as_(of(crate::array::empty::<u64>(), 0), NUM_ARRAY);
                assert_eq!((v.len(), e.len()), (3, 0));
                return;
            }
            Ok("reverse") => {
                let _: V<u16> = as_(of(crate::array::empty::<LAny>(), 0), NUM_U16S);
                return;
            }
            _ => {}
        }
        let run = |mode: &str, var: &str| {
            std::process::Command::new(std::env::current_exe().unwrap())
                .args(["--exact", "any::tests::conversion_line_and_reverse_mismatch", "--test-threads=1"])
                .env("LEANRT_TEST_CHILD", mode)
                .env(var, "1")
                .output()
                .unwrap()
        };
        let out = run("convert", "L2R_DEBUG_ARRAY_CONVERT");
        let err = String::from_utf8_lossy(&out.stderr);
        assert!(out.status.success(), "{err}");
        let lines: std::vec::Vec<&str> = err.lines().filter(|l| l.starts_with("leanrt:")).collect();
        assert_eq!(
            lines,
            vec!["leanrt: compact array of kind 9 converted to boxes (3 elements)", "leanrt: compact array of kind 11 converted to boxes (0 elements)"]
        );
        let out = run("reverse", "L2R_ANY_DEBUG");
        let err = String::from_utf8_lossy(&out.stderr);
        assert!(!out.status.success() && err.contains("at payload 9"), "{err}");
    }

    #[test]
    fn function_values_keep_their_type_in_an_immediate() {
        // Not a Reussir record here: `of_typed` of an immediate box.
        let a = of_typed(LAny::imm(2), 40);
        assert_eq!(a.imm_value(), (40 << 32) | 2);
        let s = of_typed(crate::string::from_bytes(b"f"), 40);
        assert_eq!(s.num(), NUM_STR);
    }

    #[test]
    fn u64_and_f64_read_each_others_bits() {
        assert_eq!(as_f64(of_u64(1.5f64.to_bits())), 1.5);
        assert_eq!(as_f64(of_u64((-2.0f64).to_bits())), -2.0);
        assert_eq!(as_u64(of_f64(0.25)), 0.25f64.to_bits());
    }

    /// A float's or a large `UInt64`'s cell read while shared: the count
    /// goes down; read by its last reference: the cell is freed (once).
    #[test]
    fn scalar_cells_read_shared_and_last() {
        for (a, bits) in [(of_f64(2.75), 2.75f64.to_bits()), (of_u64(u64::MAX - 2), u64::MAX - 2)] {
            let b = a.clone();
            assert_eq!(count(&a), 2);
            assert_eq!(as_u64(b), bits);
            assert_eq!(count(&a), 1);
            let c = a.clone();
            assert_eq!(as_f64(c).to_bits(), bits);
            assert_eq!(count(&a), 1);
            assert_eq!(as_f64(a).to_bits(), bits);
        }
        // Released without a read.
        drop(of_f64(1.0));
        drop(of_u64(1 << 63));
    }

    #[test]
    fn a_leaf_payload_is_released_directly() {
        install();
        // A leaf number outside a free: the program's release is called
        // directly (it logs as the worklist would).
        drop(of(crate::alloc::rc_new(Node { id: 5, next: LAny::unit() }), LEAF));
        assert_eq!(take_log(), vec![5]);
        // Inside a free too: a pair's first field, a leaf, is released when
        // the pair's release drops it, with nothing pushed yet; the second
        // field, deferred, comes after it (a deferred leaf would come after
        // the second field, with the second field's entry above it).
        drop(pair(1, leaf_probe(2), probe(3, LAny::unit()), PAIR));
        assert_eq!(take_seen(), vec![(2, true, 0), (3, true, 0)]);
        assert_eq!(take_log(), vec![1]);
        assert_eq!(reussir_rt::drop::depth(), 0);
    }

    /// Payload numbers with `WIDE_BIT`: their cells, deferred one after
    /// the other inside a free (the items of a `Many`, as the heads of a
    /// list that Reussir's glue frees whole), link into one run of
    /// Reussir's stack: one entry, so the depth a release sees stays 1,
    /// where cells without the bit take an entry each (24 bytes in the
    /// stack's vector). The same releases in the same order, each cell's
    /// count set back to 1 before its release (`Rc`'s drop frees the cell),
    /// also with two release functions in turn (the run's table).
    #[test]
    fn wide_cells_link_into_one_run() {
        install();
        let items = |nums: [u64; 4]| -> std::vec::Vec<LAny> {
            (0..4)
                .map(|k| match nums[k] {
                    WIDE_NODE => of(crate::alloc::rc_new(Node { id: 10 + k as u32, next: LAny::unit() }), WIDE_NODE),
                    num => of(crate::alloc::rc_new(Probe { id: k as u32 + 1, next: LAny::unit() }), num),
                })
                .collect()
        };
        drop(of(crate::alloc::rc_new(Many { id: 9, items: items([WIDE_PROBE; 4]) }), MANY));
        assert_eq!(take_seen(), vec![(4, true, 1), (3, true, 1), (2, true, 1), (1, true, 0)]);
        drop(of(crate::alloc::rc_new(Many { id: 9, items: items([PROBE; 4]) }), MANY));
        assert_eq!(take_seen(), vec![(4, true, 3), (3, true, 2), (2, true, 1), (1, true, 0)]);
        drop(of(crate::alloc::rc_new(Many { id: 9, items: items([WIDE_PROBE, WIDE_NODE, WIDE_PROBE, WIDE_NODE]) }), MANY));
        assert_eq!(take_seen(), vec![(3, true, 1), (1, true, 0)]);
        assert_eq!(take_log(), vec![9, 9, 9, 13, 11]);
        // With work pending below: the wide cells link onto the run on top,
        // the pair's first field (deferred first, without the bit: a link
        // writes only the cell that links), which comes out last.
        let many = of(crate::alloc::rc_new(Many { id: 8, items: items([WIDE_PROBE; 4]) }), MANY);
        drop(pair(1, probe(5, LAny::unit()), many, PAIR));
        assert_eq!(take_seen(), vec![(4, true, 1), (3, true, 1), (2, true, 1), (1, true, 1), (5, true, 0)]);
        assert_eq!(take_log(), vec![1, 8]);
        assert!(!crate::drop::active());
        assert_eq!(reussir_rt::drop::depth(), 0);
    }

    #[test]
    fn boxing_a_box_is_the_identity() {
        let s = of(crate::string::from_bytes(b"y"), NUM_STR);
        let w = s.word();
        let t = of(s, 99);
        assert_eq!(t.word(), w);
        let u: LAny = as_(t, 7);
        assert_eq!(u.word(), w);
        assert_eq!(of(LAny::imm(5), 3).word(), 11);
    }

    #[test]
    fn addresses() {
        let s = of(crate::string::from_bytes(b"x"), NUM_STR);
        assert_eq!(s.addr() >> ADDR_BITS, 0);
        assert_eq!(s.addr() & 7, 0);
        assert_eq!(LAny::imm(4).addr(), 9);
    }
}
