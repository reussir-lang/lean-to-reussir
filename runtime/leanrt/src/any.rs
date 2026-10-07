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
//! (`NUM_*`), released here; 16 and up are the program's (lean2rr numbers
//! the payload types of a program). The last reference to a program
//! payload goes to the program's release function of its type (a table by
//! payload number, `RELEASES`: lean2rr's `l2r_any_rel_<num>_c(cell)`, an
//! `extern "C" trampoline` of a generated Reussir function that drops the
//! payload at its type), through the drop worklist: the payload's cell is
//! deferred as one pending cell, so a chain of a million nested boxes is
//! freed without deep recursion and what the payload holds is released in
//! native Lean's order. A leaf payload (a number with `LEAF_BIT`: lean2rr
//! gives it to records and enums whose fields are all scalars) is released
//! by a direct call when no free is running: it holds nothing to order.
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
/// A `ByteArray` (`RVec<u8>`).
pub const NUM_BYTES: u64 = 7;
/// A `FloatArray` (`RVec<f64>`).
pub const NUM_FLOATS: u64 = 8;
pub const FIRST_PROGRAM_NUM: u64 = 16;
/// The bit of a program payload number that marks a leaf type: a record or
/// enum without counted or observable members (its fields are scalars), so
/// that freeing it frees nothing else. lean2rr numbers leaf types with it
/// (`release_last`).
pub const LEAF_BIT: u64 = 0x8000;
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
/// (`init_releases`, from `rt::run_main2`) and never changed afterwards. In
/// `.bss`: only the pages of the numbers in use are touched.
static RELEASES: [AtomicPtr<()>; 1 << 16] = [const { AtomicPtr::new(std::ptr::null_mut()) }; 1 << 16];

/// Install a program's releases (lean2rr's generated `l2r_any_releases`, a
/// texture that the trampoline `l2r_any_init_c` calls; a test's own). An
/// entry installed again gets the same value. 0.
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
/// `drop::free_unique` for records (`__reussir_drop_defer`, which neither
/// reads nor writes the cell). Inside a free it is only pushed; outside one
/// Reussir's drain releases it and then what it pushed (`drain_one`). So
/// nested boxes are released one after the other, not by recursion, and
/// what a payload holds in native Lean's order. A leaf payload outside a
/// free is released directly. leanrt's own kinds are dropped as their
/// types (`release_kind`). `extern "C"`: no unwinding, so the textures that
/// drop an `LAny` need no landing pad. `#[cold]`, though the last
/// reference of a boxed record is common: the drops in a loop then keep
/// their decrement in line and the call out of the way (without it, sieve
/// +0.5 % instructions from the loop's layout; monadic-interp, which frees
/// a boxed record per step, -0.1 %).
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
            return release_leaf(cell, f);
        }
        return unsafe { defer_and_drain(cell, f) };
    }
    release_kind(w, num)
}

/// Defer `release(cell)` as one pending cell, then drain: Reussir's drain
/// runs it now when no free runs (`drain_one`), else the free on top pops
/// it after what is pushed later. Not `__reussir_drop_defer_wide`, which
/// could link the cell to the run on top through its header (when the
/// type's first 8 bytes are header): in the classic programs the stack was
/// empty at every such deferral, so no link ever formed, and the wide
/// deferral cost 3 instructions more each (monadic-interp +0.6 %).
#[inline(always)]
unsafe fn defer_and_drain(cell: *mut u8, release: unsafe extern "C" fn(*mut u8)) {
    unsafe {
        reussir_rt::drop::__reussir_drop_defer(cell, release);
        reussir_rt::drop::__reussir_drop_drain();
    }
}

/// `release_last` of a leaf payload: outside a free its release frees only
/// its own cell (no member to order, no recursion), so it is called
/// directly; inside one it is deferred as any payload. Apart from
/// `release_last`, whose path then reads no thread-local state.
#[inline(never)]
extern "C" fn release_leaf(cell: *mut u8, release: unsafe extern "C" fn(*mut u8)) {
    unsafe {
        if !crate::drop::active() {
            return release(cell);
        }
        defer_and_drain(cell, release)
    }
}

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
            NUM_BYTES => drop(std::mem::transmute::<*mut u8, crate::drop::Vec<u8>>(p)),
            NUM_FLOATS => drop(std::mem::transmute::<*mut u8, crate::drop::Vec<f64>>(p)),
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
        if c >= 0x8000_0000 {
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
// `RVec<LAny>`; also the prelude's `LRef<LAny>`, the same Rust type (number
// 6; `box(0)` unboxes to an empty one; generated code does not use `LRef`).
leanrt_kind!(crate::drop::Vec<LAny>, NUM_ARRAY, Some(crate::array::empty::<LAny>));
leanrt_kind!(crate::drop::Vec<u8>, NUM_BYTES, Some(crate::array::empty::<u8>));
leanrt_kind!(crate::drop::Vec<f64>, NUM_FLOATS, Some(crate::array::empty::<f64>));

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

    /// The release of the leaf number: called directly outside a free.
    unsafe extern "C" fn release_leaf(cell: *mut u8) {
        assert!(!crate::drop::active());
        drop(unsafe { take_word::<Rc<Node>>(cell as u64) });
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

    fn install() {
        super::install(&[
            Rel(NODE as u16, release_node),
            Rel(NODE2 as u16, release_node),
            Rel(LEAF as u16, release_leaf),
            Rel(PAIR as u16, release_pair),
            Rel(PAIR2 as u16, release_pair),
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

    /// A chain of two payload numbers in turn (two release functions, so
    /// that Reussir's runs mix them), on the same small stack: the same
    /// order.
    #[test]
    fn deep_chain_of_two_numbers() {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                install();
                let mut a = LAny::unit();
                for i in 0..1_000_000 {
                    a = of(crate::alloc::rc_new(Node { id: i, next: a }), if i % 3 == 0 { NODE2 } else { NODE });
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
        for (p, n) in [(PAIR, NODE), (PAIR, NODE2), (PAIR2, NODE), (PAIR2, NODE2)] {
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
    }

    #[test]
    fn unit_is_the_zero_of_leanrt_kinds() {
        // Lean's box(0) read at each kind leanrt knows: its zero.
        assert_eq!(crate::string::bytes(&as_::<LStr>(LAny::unit(), NUM_STR)), b"");
        assert_eq!(as_::<crate::drop::Vec<LAny>>(LAny::unit(), NUM_ARRAY).len(), 0);
        assert_eq!(as_::<crate::drop::Vec<u8>>(LAny::unit(), NUM_BYTES).len(), 0);
        assert_eq!(as_::<crate::drop::Vec<f64>>(LAny::unit(), NUM_FLOATS).len(), 0);
        assert_eq!(as_f64(LAny::unit()), 0.0);
        assert_eq!(as_u64(LAny::unit()), 0);
        assert_eq!(as_::<LNat>(LAny::unit(), 0).low_u64(), 0);
        assert_eq!(crate::nat::int_of_small_word(as_::<LInt>(LAny::unit(), 0).into_raw()), 0);
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
