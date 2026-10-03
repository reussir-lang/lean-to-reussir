//! Big natural numbers and integers: the slow paths of `Nat` and `Int`.
//!
//! A big number is one mimalloc block, a 16-byte header followed by the
//! limbs:
//!
//! ```text
//!    0: count: u32          the reference count (Reussir's `rc.inc` bumps it in line)
//!    4: flags: u32          reserved, 0
//!    8: size: i32           limbs in use, negated for a negative value (as GMP's `_mp_size`)
//!   12: cap: u32            room for limbs (at least 1)
//!   16: limbs: [u64; cap]   the magnitude, least significant limb first
//! ```
//!
//! The limbs in use have no zero top limb (zero has size 0), as GMP keeps
//! them. Native Lean's `lean_mpz_object` is a header and an `mpz_t` whose
//! limbs GMP allocates separately; one block saves that allocation, its
//! free and a dependent load on every access (plan §5.1; a `Nat` or `Int`
//! passed to C code is converted at that boundary). A `Nat`/`Int` word that
//! points to a big number owns one reference (see `crate::nat`), and the
//! values are normalized like Lean's: `crate::nat` keeps a `Nat` below 2^63
//! and an `Int` in the `int32` range in the word itself, so a big number in
//! a word is always outside those ranges. Functions whose result may fall
//! back into them return an `LBig` anyway; `LNat::of_big`/`LInt::of_big`
//! normalize.
//!
//! The arithmetic is GMP's: the frequent operations call its `mpn_*`
//! functions on the limbs directly, writing the result into an operand
//! that is uniquely referenced (grown with `mi_realloc` when it lacks room)
//! or else into a fresh block; the rare ones (`pow`, `gcd`, parsing,
//! printing) give GMP's `mpz_*` functions read-only `mpz_t` views of the
//! operands (`MPZ_ROINIT_N`) and copy a result out of a temporary `mpz_t`.
//! Semantics are Lean's (`src/runtime/mpz.cpp`, `object.cpp`): truncating
//! subtraction, `x / 0 = 0`, `x % 0 = x` (both handled by `crate::nat`),
//! `Int.div`/`Int.mod` truncate, `Int.ediv`/`Int.emod` are Euclidean.
//!
//! Every function consumes its `LBig` arguments.
//!
//! The `mpn` aliasing rules used here (GMP manual, "Low-level Functions",
//! and GMP's own `mpz` code, which relies on the same): `mpn_add`,
//! `mpn_sub`, `mpn_add_1`, `mpn_sub_1`, `mpn_mul_1` and `mpn_divrem_1` may
//! write over one of their sources exactly (the result pointer equal to a
//! source pointer); `mpn_lshift` may write over its source at a higher or
//! equal address, `mpn_rshift` at a lower or equal one; `mpn_mul`,
//! `mpn_sqr` and `mpn_tdiv_qr` write to separate memory.

use crate::gmp::*;
use std::ffi::c_void;
use std::ptr;

extern "C" {
    fn mi_malloc(size: usize) -> *mut c_void;
    fn mi_realloc(p: *mut c_void, size: usize) -> *mut c_void;
    fn mi_free(p: *mut c_void);
    fn mi_good_size(size: usize) -> usize;
}

/// The header of a big number's block (see the module comment).
#[repr(C)]
struct Obj {
    count: u32,
    flags: u32,
    size: i32,
    cap: u32,
}

const HDR: usize = std::mem::size_of::<Obj>();
const _: () = assert!(HDR == 16);

/// The most limbs a number may have (`size` is an `i32`, as GMP's).
pub const MAX_LIMBS: usize = i32::MAX as usize;

/// A big number: a `#[repr(transparent)]` pointer to its block, owning one
/// reference. Reussir sees it only inside a `Nat`/`Int` word, whose
/// increment touches the `u32` count at the block's address and whose
/// release calls `Drop` here.
///
/// Safety argument for the raw block: every `LBig` points at a live block
/// from `alloc` or `grow` (`mi_malloc`/`mi_realloc`, 8-aligned) of
/// `HDR + 8 * cap` bytes or more with `cap >= 1`, whose first `|size|`
/// limbs are initialized; the block is freed only by the reference that
/// finds the count at 1, and written or moved (`grow`) only through a
/// unique handle (count 1), which the result of the operation then is.
#[repr(transparent)]
pub struct LBig(*mut Obj);

impl LBig {
    #[inline(always)]
    pub fn is_unique(&self) -> bool {
        unsafe { (*self.0).count == 1 }
    }

    /// The reference count (for tests).
    #[inline(always)]
    pub fn count(&self) -> u32 {
        unsafe { (*self.0).count }
    }

    #[inline(always)]
    fn size(&self) -> i32 {
        unsafe { (*self.0).size }
    }

    /// The number of limbs in use.
    #[inline(always)]
    fn len(&self) -> usize {
        self.size().unsigned_abs() as usize
    }

    #[inline(always)]
    fn neg(&self) -> bool {
        self.size() < 0
    }

    #[inline(always)]
    fn cap(&self) -> usize {
        unsafe { (*self.0).cap as usize }
    }

    #[inline(always)]
    fn ptr(&self) -> *mut u64 {
        unsafe { (self.0 as *mut u8).add(HDR) as *mut u64 }
    }

    #[inline(always)]
    fn same(&self, o: &LBig) -> bool {
        self.0 == o.0
    }

    /// The value is the first `n <= cap` limbs (fewer when the top ones are
    /// zero), negated when `neg` (zero is never negative).
    #[inline]
    fn set(&mut self, n: usize, neg: bool) {
        debug_assert!(n <= self.cap());
        let p = self.ptr();
        let mut n = n;
        while n > 0 && unsafe { *p.add(n - 1) } == 0 {
            n -= 1;
        }
        unsafe { (*self.0).size = if neg { -(n as i32) } else { n as i32 } };
    }
}

impl Clone for LBig {
    #[inline(always)]
    fn clone(&self) -> Self {
        unsafe { (*self.0).count += 1 };
        LBig(self.0)
    }
}

impl Drop for LBig {
    /// A shared handle is a decrement; the last reference is freed out of
    /// line.
    #[inline(always)]
    fn drop(&mut self) {
        let o = self.0;
        unsafe {
            let c = (*o).count;
            if c == 1 {
                free(o)
            } else {
                (*o).count = c - 1;
            }
        }
    }
}

impl crate::Release for LBig {
    #[inline(always)]
    fn release(self) {
        std::mem::drop(self)
    }
}

#[cold]
#[inline(never)]
extern "C" fn free(o: *mut Obj) {
    #[cfg(leanrt_count_bigs)]
    count::freed();
    unsafe { mi_free(o as *mut c_void) }
}

/// Counts of the big numbers made, freed and grown in place, for tests:
/// built with `--cfg leanrt_count_bigs` (`L2R_LEANRT_RUSTFLAGS`, see
/// `tests/runtime/nat-alloc-check.sh`), a program prints them to stderr at
/// exit. Not compiled otherwise.
#[cfg(leanrt_count_bigs)]
mod count {
    use std::sync::atomic::{AtomicU64, Ordering::Relaxed};

    static MADE: AtomicU64 = AtomicU64::new(0);
    static FREED: AtomicU64 = AtomicU64::new(0);
    static GROWN: AtomicU64 = AtomicU64::new(0);
    static REPORT: std::sync::Once = std::sync::Once::new();

    extern "C" {
        fn atexit(f: extern "C" fn()) -> i32;
    }

    extern "C" fn report() {
        let (m, f, g) = (MADE.load(Relaxed), FREED.load(Relaxed), GROWN.load(Relaxed));
        eprintln!("leanrt: big numbers made {} freed {} live {} grown {}", m, f, m as i64 - f as i64, g);
    }

    pub fn made() {
        REPORT.call_once(|| unsafe {
            atexit(report);
        });
        MADE.fetch_add(1, Relaxed);
    }

    pub fn freed() {
        FREED.fetch_add(1, Relaxed);
    }

    pub fn grown() {
        GROWN.fetch_add(1, Relaxed);
    }
}

#[cold]
#[inline(never)]
fn oom() -> ! {
    crate::internal_panic("out of memory")
}

/// The block size for `n` limbs, rounded up to mimalloc's size class (the
/// rounding becomes capacity).
#[inline]
fn block_bytes(n: usize) -> usize {
    if n > MAX_LIMBS {
        oom()
    }
    unsafe { mi_good_size(HDR + 8 * n) }
}

#[inline]
fn cap_of(bytes: usize) -> u32 {
    ((bytes - HDR) / 8).min(MAX_LIMBS) as u32
}

/// A new number (count 1) with room for `n` limbs (at least one), zero.
#[inline]
fn alloc(n: usize) -> LBig {
    let bytes = block_bytes(n.max(1));
    unsafe {
        let o = mi_malloc(bytes) as *mut Obj;
        if o.is_null() {
            oom();
        }
        ptr::write(o, Obj { count: 1, flags: 0, size: 0, cap: cap_of(bytes) });
        #[cfg(leanrt_count_bigs)]
        count::made();
        LBig(o)
    }
}

/// Room for `n` limbs in a unique number, its value kept.
#[inline]
fn reserve(b: &mut LBig, n: usize) {
    debug_assert!(b.is_unique());
    if b.cap() < n {
        grow(b, n)
    }
}

#[inline(never)]
fn grow(b: &mut LBig, n: usize) {
    let bytes = block_bytes(n);
    unsafe {
        let o = mi_realloc(b.0 as *mut c_void, bytes) as *mut Obj;
        if o.is_null() {
            oom();
        }
        (*o).cap = cap_of(bytes);
        b.0 = o;
    }
    #[cfg(leanrt_count_bigs)]
    count::grown();
}

/// `b` itself when it is unique, else a copy (and `b` released); with room
/// for `n` limbs.
#[inline]
fn unique(b: LBig, n: usize) -> LBig {
    if b.is_unique() {
        let mut b = b;
        reserve(&mut b, n);
        b
    } else {
        let r = alloc(n.max(b.len()));
        unsafe {
            ptr::copy_nonoverlapping(b.ptr(), r.ptr(), b.len());
            (*r.0).size = b.size();
        }
        drop(b);
        r
    }
}

/// Where a result of `n` limbs computed beside the operands goes: a unique
/// operand with room for it (`a` before `b`), else a fresh block (growing
/// an operand would copy limbs about to be overwritten: its capacity is
/// its block's usable size, so `mi_realloc` would move it). The other
/// operands are released.
#[inline]
fn either(a: LBig, b: LBig, n: usize) -> LBig {
    if a.is_unique() && a.cap() >= n {
        drop(b);
        a
    } else if b.is_unique() && b.cap() >= n {
        drop(a);
        b
    } else {
        drop(a);
        drop(b);
        alloc(n)
    }
}

/// Zero, in an operand's block when one is unique.
fn zero(a: LBig, b: LBig) -> LBig {
    let mut r = either(a, b, 1);
    r.set(0, false);
    r
}

/// Zero, in `a`'s block when it is unique.
fn zero_of(a: LBig) -> LBig {
    let mut r = if a.is_unique() {
        a
    } else {
        drop(a);
        alloc(1)
    };
    r.set(0, false);
    r
}

/// A new number with the limbs `src[..n]`, negated when `neg`.
fn of_limbs(src: *const u64, n: usize, neg: bool) -> LBig {
    let mut r = alloc(n);
    unsafe { ptr::copy_nonoverlapping(src, r.ptr(), n) };
    r.set(n, neg);
    r
}

/// A read-only `mpz_t` view of `b` (`MPZ_ROINIT_N`), for GMP's `mpz_*`
/// functions; valid while `b` is.
#[inline]
fn view(b: &LBig) -> Mpz {
    Mpz { alloc: 0, size: b.size(), d: b.ptr() }
}

/// A new number with the value of a temporary `mpz_t`.
fn of_mpz(z: &Mpz) -> LBig {
    of_limbs(z.d, z.size.unsigned_abs() as usize, z.size < 0)
}

/// Scratch limbs: on the stack up to `SMALL`, else on the heap.
const SMALL: usize = 32;

#[inline]
fn scratch(stack: &mut [u64; SMALL], heap: &mut Vec<u64>, n: usize) -> *mut u64 {
    if n <= SMALL {
        stack.as_mut_ptr()
    } else {
        *heap = vec![0; n];
        heap.as_mut_ptr()
    }
}

// ---------------------------------------------------------------------------
// Construction and inspection

#[inline(never)]
pub fn of_u64(x: u64) -> LBig {
    let mut r = alloc(1);
    unsafe { *r.ptr() = x };
    r.set(1, false);
    r
}

/// `hi * 2^64 + lo`.
#[inline(never)]
pub fn of_limbs2(lo: u64, hi: u64) -> LBig {
    let mut r = alloc(2);
    unsafe {
        *r.ptr() = lo;
        *r.ptr().add(1) = hi;
    }
    r.set(2, false);
    r
}

#[inline(never)]
pub fn of_i64(x: i64) -> LBig {
    let mut r = alloc(1);
    unsafe { *r.ptr() = x.unsigned_abs() };
    r.set(1, x < 0);
    r
}

/// `2^k`.
#[inline(never)]
pub fn pow2(k: u64) -> LBig {
    let n = (k / 64) as usize + 1;
    let mut r = alloc(n);
    unsafe {
        ptr::write_bytes(r.ptr(), 0, n - 1);
        *r.ptr().add(n - 1) = 1 << (k % 64);
    }
    r.set(n, false);
    r
}

/// The magnitude's limbs, little-endian, without high zero limbs (empty
/// for zero).
#[inline]
pub fn limbs(b: &LBig) -> &[u64] {
    unsafe { std::slice::from_raw_parts(b.ptr(), b.len()) }
}

#[inline]
pub fn is_neg(b: &LBig) -> bool {
    b.neg()
}

/// Whether a non-negative value fits in a `u64`.
#[inline]
pub fn is_u64(b: &LBig) -> bool {
    !b.neg() && b.len() <= 1
}

/// The lowest limb of the magnitude (`0` for zero).
#[inline]
pub fn low_limb(b: &LBig) -> u64 {
    if b.len() == 0 { 0 } else { unsafe { *b.ptr() } }
}

/// Whether the value is in the `i64` range.
#[inline]
pub fn fits_i64(b: &LBig) -> bool {
    match b.len() {
        0 => true,
        1 => {
            let m = low_limb(b);
            if b.neg() { m <= 1 << 63 } else { m < 1 << 63 }
        }
        _ => false,
    }
}

/// The value modulo 2^64 in two's complement (for `Int64.ofInt`,
/// `Int8.ofInt`, ... which take the low bits, like `mpz::smod64`).
#[inline]
pub fn low_u64_twos(b: &LBig) -> u64 {
    let m = low_limb(b);
    if is_neg(b) { m.wrapping_neg() } else { m }
}

/// The value as an `i64` (requires `fits_i64`).
#[inline]
pub fn to_i64(b: &LBig) -> i64 {
    low_u64_twos(b) as i64
}

/// Parse a decimal digit string (as produced by lean2rr for big literals).
#[inline(never)]
pub fn of_decimal(s: &str) -> LBig {
    let mut digits: Vec<u8> = s.bytes().filter(|c| c.is_ascii_digit()).collect();
    if digits.is_empty() {
        digits.push(b'0');
    }
    digits.push(0);
    let mut t = OwnedMpz(Mpz { alloc: 0, size: 0, d: ptr::null_mut() });
    unsafe { __gmpz_init_set_str(&mut t.0, digits.as_ptr(), 10) };
    of_mpz(&t.0)
}

/// The decimal representation (with a leading `-` for negative values).
#[inline(never)]
pub fn to_decimal(b: &LBig) -> Vec<u8> {
    let z = view(b);
    // `mpz_sizeinbase` may overestimate by one; one more for the sign and
    // one for the terminating NUL.
    let cap = unsafe { __gmpz_sizeinbase(&z, 10) } + 2;
    let mut out = vec![0u8; cap];
    unsafe { __gmpz_get_str(out.as_mut_ptr(), 10, &z) };
    let n = out.iter().position(|&c| c == 0).unwrap_or(out.len());
    out.truncate(n);
    out
}

// ---------------------------------------------------------------------------
// Building blocks on magnitudes and signs

/// Compare the magnitudes: -1, 0, 1.
fn cmp_mag(a: &LBig, b: &LBig) -> i32 {
    let (na, nb) = (a.len(), b.len());
    if na != nb {
        return if na > nb { 1 } else { -1 };
    }
    let (x, y) = (limbs(a), limbs(b));
    for i in (0..na).rev() {
        if x[i] != y[i] {
            return if x[i] > y[i] { 1 } else { -1 };
        }
    }
    0
}

/// Compare the values: -1, 0, 1 (as `mpz_cmp`; the sizes are normalized).
fn cmp(a: &LBig, b: &LBig) -> i32 {
    let (sa, sb) = (a.size(), b.size());
    if sa != sb {
        return if sa > sb { 1 } else { -1 };
    }
    let c = cmp_mag(a, b);
    if sa < 0 { -c } else { c }
}

/// `|x| + |y|` (with `x.len() >= y.len()`), negated when `neg`.
fn add_mag(x: LBig, y: LBig, neg: bool) -> LBig {
    let (nx, ny) = (x.len(), y.len());
    debug_assert!(nx >= ny);
    unsafe {
        if x.is_unique() {
            let mut r = x;
            let c = __gmpn_add(r.ptr(), r.ptr(), nx as i64, y.ptr(), ny as i64);
            drop(y);
            if c != 0 {
                reserve(&mut r, nx + 1);
                *r.ptr().add(nx) = c;
            }
            r.set(nx + c as usize, neg);
            r
        } else if y.is_unique() && y.cap() >= nx {
            // Over the second source (allowed, as `mpz_add` does).
            let mut r = y;
            let c = __gmpn_add(r.ptr(), x.ptr(), nx as i64, r.ptr(), ny as i64);
            drop(x);
            if c != 0 {
                reserve(&mut r, nx + 1);
                *r.ptr().add(nx) = c;
            }
            r.set(nx + c as usize, neg);
            r
        } else {
            let mut r = alloc(nx + 1);
            *r.ptr().add(nx) = __gmpn_add(r.ptr(), x.ptr(), nx as i64, y.ptr(), ny as i64);
            drop(x);
            drop(y);
            r.set(nx + 1, neg);
            r
        }
    }
}

/// `|x| - |y|` (with `|x| >= |y|`), negated when `neg`.
fn sub_mag(x: LBig, y: LBig, neg: bool) -> LBig {
    let (nx, ny) = (x.len(), y.len());
    debug_assert!(cmp_mag(&x, &y) >= 0);
    unsafe {
        if x.is_unique() {
            let mut r = x;
            __gmpn_sub(r.ptr(), r.ptr(), nx as i64, y.ptr(), ny as i64);
            drop(y);
            r.set(nx, neg);
            r
        } else if y.is_unique() && y.cap() >= nx {
            let mut r = y;
            __gmpn_sub(r.ptr(), x.ptr(), nx as i64, r.ptr(), ny as i64);
            drop(x);
            r.set(nx, neg);
            r
        } else {
            let mut r = alloc(nx);
            __gmpn_sub(r.ptr(), x.ptr(), nx as i64, y.ptr(), ny as i64);
            drop(x);
            drop(y);
            r.set(nx, neg);
            r
        }
    }
}

/// `a + b`, or `a - b` when `sub`, with signs.
fn add_signed(a: LBig, b: LBig, sub: bool) -> LBig {
    let sa = a.neg();
    let sb = b.neg() != sub;
    if sa == sb {
        if a.len() >= b.len() { add_mag(a, b, sa) } else { add_mag(b, a, sa) }
    } else {
        match cmp_mag(&a, &b) {
            0 => zero(a, b),
            c if c > 0 => sub_mag(a, b, sa),
            _ => sub_mag(b, a, sb),
        }
    }
}

/// `|a| * y`, negated when `neg`.
fn mul_limb(a: LBig, y: u64, neg: bool) -> LBig {
    let n = a.len();
    if n == 0 {
        return a;
    }
    unsafe {
        if a.is_unique() {
            let mut r = a;
            let c = __gmpn_mul_1(r.ptr(), r.ptr(), n as i64, y);
            if c != 0 {
                reserve(&mut r, n + 1);
                *r.ptr().add(n) = c;
            }
            r.set(n + (c != 0) as usize, neg);
            r
        } else {
            let mut r = alloc(n + 1);
            *r.ptr().add(n) = __gmpn_mul_1(r.ptr(), a.ptr(), n as i64, y);
            drop(a);
            r.set(n + 1, neg);
            r
        }
    }
}

/// `a * b` with signs. A product with a one-limb factor goes into a unique
/// operand's block (`mpn_mul_1`); a small product of two longer factors is
/// computed into scratch limbs and copied into a unique operand's block
/// (`mpn_mul` cannot write over its sources); anything else into a fresh
/// block.
fn mul(a: LBig, b: LBig) -> LBig {
    let (na, nb) = (a.len(), b.len());
    let neg = a.neg() != b.neg();
    if na == 0 || nb == 0 {
        return zero(a, b);
    }
    if na == 1 || nb == 1 {
        // `x * y` with `y` of one limb.
        let (x, y) = if nb == 1 { (a, b) } else { (b, a) };
        let y0 = low_limb(&y);
        if !x.is_unique() && y.is_unique() && y.cap() > x.len() {
            // Into `y`'s block, which has room for the `nx + 1` limbs.
            let nx = x.len();
            let mut r = y;
            unsafe { *r.ptr().add(nx) = __gmpn_mul_1(r.ptr(), x.ptr(), nx as i64, y0) };
            drop(x);
            r.set(nx + 1, neg);
            return r;
        }
        drop(y);
        return mul_limb(x, y0, neg);
    }
    let n = na + nb;
    let (x, y) = if na >= nb { (&a, &b) } else { (&b, &a) };
    if n <= SMALL && (a.is_unique() || b.is_unique()) {
        let mut s = [0u64; SMALL];
        unsafe { __gmpn_mul(s.as_mut_ptr(), x.ptr(), x.len() as i64, y.ptr(), y.len() as i64) };
        let mut r = either(a, b, n);
        unsafe { ptr::copy_nonoverlapping(s.as_ptr(), r.ptr(), n) };
        r.set(n, neg);
        return r;
    }
    let mut r = alloc(n);
    unsafe {
        if a.same(&b) {
            __gmpn_sqr(r.ptr(), a.ptr(), na as i64);
        } else {
            __gmpn_mul(r.ptr(), x.ptr(), x.len() as i64, y.ptr(), y.len() as i64);
        }
    }
    drop(a);
    drop(b);
    r.set(n, neg);
    r
}

/// What `div` computes.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Div {
    /// The truncated quotient (`Nat./`, `Int.tdiv`).
    TQ,
    /// The truncated remainder, with the dividend's sign (`Nat.%`, `Int.tmod`).
    TR,
    /// The Euclidean quotient (`Int.ediv`).
    EQ,
    /// The Euclidean remainder, never negative (`Int.emod`).
    ER,
}

/// Division with signs; `b` nonzero. The quotient and the remainder are
/// computed into scratch limbs and the requested one copied into an
/// operand's block when one is unique, else into a fresh block.
fn div(a: LBig, b: LBig, k: Div) -> LBig {
    let (na, nb) = (a.len(), b.len());
    debug_assert!(nb > 0);
    let (sa, sb) = (a.neg(), b.neg());
    let qn = if na >= nb { na - nb + 1 } else { 0 };
    let (mut qs, mut qh) = ([0u64; SMALL], Vec::new());
    let (mut rs, mut rh) = ([0u64; SMALL], Vec::new());
    // One more quotient limb for `EQ`'s increment.
    let q = scratch(&mut qs, &mut qh, qn + 1);
    let r = scratch(&mut rs, &mut rh, nb);
    let mut rn = unsafe {
        if na < nb {
            ptr::copy_nonoverlapping(a.ptr(), r, na);
            na
        } else if nb == 1 {
            *r = __gmpn_divrem_1(q, 0, a.ptr(), na as i64, *b.ptr());
            1
        } else {
            __gmpn_tdiv_qr(q, r, 0, a.ptr(), na as i64, b.ptr(), nb as i64);
            nb
        }
    };
    while rn > 0 && unsafe { *r.add(rn - 1) } == 0 {
        rn -= 1;
    }
    let (src, n, neg) = unsafe {
        match k {
            Div::TQ => (q as *const u64, qn, sa != sb),
            Div::TR => (r as *const u64, rn, sa),
            Div::EQ => {
                // A negative dividend with a remainder: one further from
                // zero (floor for `b > 0`, ceiling for `b < 0`).
                let mut n = qn;
                if rn != 0 && sa {
                    let c = if n == 0 { 1 } else { __gmpn_add_1(q, q, n as i64, 1) };
                    *q.add(n) = c;
                    n += 1;
                }
                (q as *const u64, n, sa != sb)
            }
            Div::ER => {
                // A negative dividend with a remainder: `|b| - |r|`.
                if rn != 0 && sa {
                    __gmpn_sub(r, b.ptr(), nb as i64, r, rn as i64);
                    rn = nb;
                }
                (r as *const u64, rn, false)
            }
        }
    };
    let mut out = either(a, b, n);
    unsafe { ptr::copy_nonoverlapping(src, out.ptr(), n) };
    out.set(n, neg);
    out
}

/// The bitwise operations on magnitudes (`Nat`s).
#[derive(Clone, Copy, PartialEq, Eq)]
enum Bit {
    And,
    Or,
    Xor,
}

fn bitwise(a: LBig, b: LBig, op: Bit) -> LBig {
    let (x, y) = if a.len() >= b.len() { (a, b) } else { (b, a) };
    let (nx, ny) = (x.len(), y.len());
    let n = if op == Bit::And { ny } else { nx };
    // `rp` may be `xp` or `yp` exactly: each limb is read before it is
    // written.
    let run = |rp: *mut u64, xp: *const u64, yp: *const u64| unsafe {
        for i in 0..ny {
            let (u, v) = (*xp.add(i), *yp.add(i));
            *rp.add(i) = match op {
                Bit::And => u & v,
                Bit::Or => u | v,
                Bit::Xor => u ^ v,
            };
        }
        if op != Bit::And && rp as *const u64 != xp {
            ptr::copy_nonoverlapping(xp.add(ny), rp.add(ny), nx - ny);
        }
    };
    if x.is_unique() {
        let mut r = x;
        run(r.ptr(), r.ptr(), y.ptr());
        drop(y);
        r.set(n, false);
        r
    } else if y.is_unique() && y.cap() >= n {
        let mut r = y;
        run(r.ptr(), x.ptr(), r.ptr());
        drop(x);
        r.set(n, false);
        r
    } else {
        let mut r = alloc(n);
        run(r.ptr(), x.ptr(), y.ptr());
        drop(x);
        drop(y);
        r.set(n, false);
        r
    }
}

// ---------------------------------------------------------------------------
// Nat (non-negative) operations. Arguments are big `Nat`s (>= 2^63)
// unless stated otherwise.

/// `a + b`.
#[inline(never)]
pub fn nat_add(a: LBig, b: LBig) -> LBig {
    add_signed(a, b, false)
}

/// `a + y` for a big `a` and any `y`.
#[inline(never)]
pub fn nat_add_u64(a: LBig, y: u64) -> LBig {
    let n = a.len();
    if n == 0 {
        drop(a);
        return of_u64(y);
    }
    unsafe {
        if a.is_unique() {
            let mut r = a;
            let c = __gmpn_add_1(r.ptr(), r.ptr(), n as i64, y);
            if c != 0 {
                reserve(&mut r, n + 1);
                *r.ptr().add(n) = c;
            }
            r.set(n + c as usize, false);
            r
        } else {
            let mut r = alloc(n + 1);
            *r.ptr().add(n) = __gmpn_add_1(r.ptr(), a.ptr(), n as i64, y);
            drop(a);
            r.set(n + 1, false);
            r
        }
    }
}

/// Truncated subtraction `a - b` (0 when `a < b`).
#[inline(never)]
pub fn nat_sub(a: LBig, b: LBig) -> LBig {
    if cmp_mag(&a, &b) <= 0 {
        return zero(a, b);
    }
    sub_mag(a, b, false)
}

/// `a - y` for a big `a` (never truncates: `y < 2^63 <= a`).
#[inline(never)]
pub fn nat_sub_u64(a: LBig, y: u64) -> LBig {
    let n = a.len();
    if n == 0 {
        return a;
    }
    unsafe {
        if a.is_unique() {
            let mut r = a;
            __gmpn_sub_1(r.ptr(), r.ptr(), n as i64, y);
            r.set(n, false);
            r
        } else {
            let mut r = alloc(n);
            __gmpn_sub_1(r.ptr(), a.ptr(), n as i64, y);
            drop(a);
            r.set(n, false);
            r
        }
    }
}

#[inline(never)]
pub fn nat_mul(a: LBig, b: LBig) -> LBig {
    mul(a, b)
}

/// `a * y`.
#[inline(never)]
pub fn nat_mul_u64(a: LBig, y: u64) -> LBig {
    mul_limb(a, y, false)
}

/// The full product of two words.
#[inline(never)]
pub fn u64_mul_wide(x: u64, y: u64) -> LBig {
    let p = (x as u128) * (y as u128);
    of_limbs2(p as u64, (p >> 64) as u64)
}

/// High word of the product of two words (0 when it does not overflow).
#[inline]
pub fn u64_mul_hi(x: u64, y: u64) -> u64 {
    (((x as u128) * (y as u128)) >> 64) as u64
}

/// `a / b` for a nonzero `b`.
#[inline(never)]
pub fn nat_div(a: LBig, b: LBig) -> LBig {
    div(a, b, Div::TQ)
}

/// `a / y` for `y != 0`.
#[inline(never)]
pub fn nat_div_u64(a: LBig, y: u64) -> LBig {
    let n = a.len();
    if n == 0 {
        return a;
    }
    unsafe {
        if a.is_unique() {
            let mut r = a;
            __gmpn_divrem_1(r.ptr(), 0, r.ptr(), n as i64, y);
            r.set(n, false);
            r
        } else {
            let mut r = alloc(n);
            __gmpn_divrem_1(r.ptr(), 0, a.ptr(), n as i64, y);
            drop(a);
            r.set(n, false);
            r
        }
    }
}

/// `a % b` for a nonzero `b`.
#[inline(never)]
pub fn nat_mod(a: LBig, b: LBig) -> LBig {
    div(a, b, Div::TR)
}

/// `a % y` for `y != 0`.
#[inline(never)]
pub fn nat_mod_u64(a: LBig, y: u64) -> u64 {
    let n = a.len();
    if n == 0 { 0 } else { unsafe { __gmpn_mod_1(a.ptr(), n as i64, y) } }
}

/// Three-way comparison: -1, 0, 1 (any signs).
#[inline(never)]
pub fn nat_cmp(a: LBig, b: LBig) -> i64 {
    cmp(&a, &b) as i64
}

#[inline(never)]
pub fn nat_eq(a: LBig, b: LBig) -> bool {
    a.size() == b.size() && limbs(&a) == limbs(&b)
}

#[inline(never)]
pub fn nat_land(a: LBig, b: LBig) -> LBig {
    bitwise(a, b, Bit::And)
}

#[inline(never)]
pub fn nat_land_u64(a: LBig, y: u64) -> u64 {
    low_limb(&a) & y
}

#[inline(never)]
pub fn nat_lor(a: LBig, b: LBig) -> LBig {
    bitwise(a, b, Bit::Or)
}

/// Apply `f` to the lowest limb of a positive `a` (into `a` when unique).
#[inline]
fn with_low_limb(a: LBig, f: impl FnOnce(u64) -> u64) -> LBig {
    let n = a.len();
    debug_assert!(n > 0);
    let mut r = unique(a, n);
    unsafe { *r.ptr() = f(*r.ptr()) };
    r.set(n, false);
    r
}

/// `a ||| y` for a big `a` (>= 2^63, at least one limb).
#[inline(never)]
pub fn nat_lor_u64(a: LBig, y: u64) -> LBig {
    with_low_limb(a, |l| l | y)
}

#[inline(never)]
pub fn nat_xor(a: LBig, b: LBig) -> LBig {
    bitwise(a, b, Bit::Xor)
}

/// `a ^^^ y` for a big `a` (>= 2^63, at least one limb).
#[inline(never)]
pub fn nat_xor_u64(a: LBig, y: u64) -> LBig {
    with_low_limb(a, |l| l ^ y)
}

/// `a <<< s`; `s <= 2^32 - 1` (checked by the caller).
#[inline(never)]
pub fn nat_shl(a: LBig, s: u64) -> LBig {
    let n = a.len();
    if n == 0 {
        return a;
    }
    let k = (s / 64) as usize;
    let bits = (s % 64) as u32;
    let need = n.checked_add(k).and_then(|m| m.checked_add(1)).unwrap_or_else(|| oom());
    unsafe {
        if a.is_unique() && a.cap() >= need {
            let mut r = a;
            let p = r.ptr();
            // Up by `k` limbs (from the top: GMP's `lshift` and `copy`
            // allow a destination at or above the source).
            if bits == 0 {
                ptr::copy(p, p.add(k), n);
                *p.add(n + k) = 0;
            } else {
                *p.add(n + k) = __gmpn_lshift(p.add(k), p, n as i64, bits);
            }
            ptr::write_bytes(p, 0, k);
            r.set(need, false);
            r
        } else {
            let mut r = alloc(need);
            let p = r.ptr();
            ptr::write_bytes(p, 0, k);
            if bits == 0 {
                ptr::copy_nonoverlapping(a.ptr(), p.add(k), n);
                *p.add(n + k) = 0;
            } else {
                *p.add(n + k) = __gmpn_lshift(p.add(k), a.ptr(), n as i64, bits);
            }
            drop(a);
            r.set(need, false);
            r
        }
    }
}

/// `a >>> s` (a non-negative).
#[inline(never)]
pub fn nat_shr(a: LBig, s: u64) -> LBig {
    let n = a.len();
    let k = s / 64;
    if k >= n as u64 {
        return zero_of(a);
    }
    let k = k as usize;
    let m = n - k;
    let bits = (s % 64) as u32;
    unsafe {
        if a.is_unique() {
            let mut r = a;
            let p = r.ptr();
            // Down by `k` limbs (from the bottom: a destination at or
            // below the source).
            if bits == 0 {
                ptr::copy(p.add(k), p, m);
            } else {
                __gmpn_rshift(p, p.add(k), m as i64, bits);
            }
            r.set(m, false);
            r
        } else {
            let mut r = alloc(m);
            if bits == 0 {
                ptr::copy_nonoverlapping(a.ptr().add(k), r.ptr(), m);
            } else {
                __gmpn_rshift(r.ptr(), a.ptr().add(k), m as i64, bits);
            }
            drop(a);
            r.set(m, false);
            r
        }
    }
}

/// Bit length minus one (`Nat.log2`) of a positive value.
#[inline(never)]
pub fn nat_log2(a: LBig) -> u64 {
    let n = a.len();
    if n == 0 {
        return 0;
    }
    let top = limbs(&a)[n - 1];
    64 * (n as u64 - 1) + 63 - top.leading_zeros() as u64
}

/// `a ^ e`.
#[inline(never)]
pub fn nat_pow(a: LBig, e: u64) -> LBig {
    let mut t = OwnedMpz::new();
    let z = view(&a);
    unsafe { __gmpz_pow_ui(t.ptr(), &z, e) };
    drop(a);
    of_mpz(&t.0)
}

/// `x ^ e` for a word `x`.
#[inline(never)]
pub fn u64_pow(x: u64, e: u64) -> LBig {
    let mut t = OwnedMpz::new();
    let z = Mpz { alloc: 0, size: (x != 0) as i32, d: &x as *const u64 as *mut u64 };
    unsafe { __gmpz_pow_ui(t.ptr(), &z, e) };
    of_mpz(&t.0)
}

#[inline(never)]
pub fn nat_gcd(a: LBig, b: LBig) -> LBig {
    let mut t = OwnedMpz::new();
    let (x, y) = (view(&a), view(&b));
    unsafe { __gmpz_gcd(t.ptr(), &x, &y) };
    drop(a);
    drop(b);
    of_mpz(&t.0)
}

// ---------------------------------------------------------------------------
// Int (signed) operations. Small operands are converted by the caller with
// `of_i64`.

/// The magnitude (for `Int.natAbs`/`Int.toNat`).
#[inline(never)]
pub fn int_abs(a: LBig) -> LBig {
    if !a.neg() {
        return a;
    }
    let n = a.len();
    let mut r = unique(a, n);
    r.set(n, false);
    r
}

#[inline(never)]
pub fn int_add(a: LBig, b: LBig) -> LBig {
    add_signed(a, b, false)
}

#[inline(never)]
pub fn int_sub(a: LBig, b: LBig) -> LBig {
    add_signed(a, b, true)
}

#[inline(never)]
pub fn int_mul(a: LBig, b: LBig) -> LBig {
    mul(a, b)
}

#[inline(never)]
pub fn int_neg(a: LBig) -> LBig {
    let n = a.len();
    if n == 0 {
        return a;
    }
    let neg = !a.neg();
    let mut r = unique(a, n);
    r.set(n, neg);
    r
}

/// Truncating quotient (`Int.tdiv`, C `/`); `b` must be nonzero.
#[inline(never)]
pub fn int_tdiv(a: LBig, b: LBig) -> LBig {
    div(a, b, Div::TQ)
}

/// Truncating remainder (`Int.tmod`, C `%`, sign of the dividend); `b` nonzero.
#[inline(never)]
pub fn int_tmod(a: LBig, b: LBig) -> LBig {
    div(a, b, Div::TR)
}

/// Euclidean quotient (`Int.ediv`); `b` nonzero: the floor of `a / b` for
/// `b > 0`, the ceiling for `b < 0` (so that `a - b * q` is in `[0, |b|)`).
#[inline(never)]
pub fn int_ediv(a: LBig, b: LBig) -> LBig {
    div(a, b, Div::EQ)
}

/// Euclidean remainder (`Int.emod`, always `>= 0`); `b` nonzero.
#[inline(never)]
pub fn int_emod(a: LBig, b: LBig) -> LBig {
    div(a, b, Div::ER)
}

#[inline(never)]
pub fn int_cmp(a: LBig, b: LBig) -> i64 {
    nat_cmp(a, b)
}

#[inline(never)]
pub fn int_eq(a: LBig, b: LBig) -> bool {
    nat_eq(a, b)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn dec(b: &LBig) -> String {
        String::from_utf8(to_decimal(b)).unwrap()
    }

    #[test]
    fn layout() {
        // The count at 0, the size at 8, the capacity at 12, the limbs at 16.
        let b = int_neg(of_decimal("123456789012345678901234567890"));
        let p = unsafe { std::mem::transmute_copy::<LBig, *const u8>(&b) };
        unsafe {
            assert_eq!(*(p as *const u32), 1);
            assert_eq!(*(p.add(4) as *const u32), 0);
            assert_eq!(*(p.add(8) as *const i32), -2); // two limbs, negative
            assert!(*(p.add(12) as *const u32) >= 2);
            assert_eq!(*(p.add(16) as *const u64), 123456789012345678901234567890u128 as u64);
            assert_eq!(*(p.add(24) as *const u64), (123456789012345678901234567890u128 >> 64) as u64);
        }
        let c = b.clone();
        unsafe { assert_eq!(*(p as *const u32), 2) };
        drop(c);
        assert_eq!(b.count(), 1);
    }

    #[test]
    fn decimal_roundtrip() {
        for s in ["0", "1", "18446744073709551616", "123456789012345678901234567890123456789"] {
            assert_eq!(dec(&of_decimal(s)), s);
        }
        assert_eq!(dec(&int_neg(of_decimal("18446744073709551616"))), "-18446744073709551616");
    }

    #[test]
    fn arith() {
        let a = of_decimal("18446744073709551616");
        let b = nat_mul(a.clone(), a.clone());
        assert_eq!(dec(&b), "340282366920938463463374607431768211456");
        assert_eq!(dec(&nat_sub(b.clone(), a.clone())), "340282366920938463444927863358058659840");
        assert_eq!(dec(&nat_div(b.clone(), of_u64(3))), "113427455640312821154458202477256070485");
        assert_eq!(dec(&nat_mod(b.clone(), of_u64(7))), "4");
        assert_eq!(dec(&int_ediv(int_neg(b.clone()), of_u64(7))), "-48611766702991209066196372490252601637");
        assert_eq!(dec(&int_emod(int_neg(b.clone()), of_u64(7))), "3");
        assert_eq!(dec(&int_tmod(int_neg(b.clone()), of_u64(7))), "-4");
        assert_eq!(dec(&int_ediv(of_u64(7), int_neg(of_u64(2)))), "-3");
        assert_eq!(dec(&int_ediv(int_neg(of_u64(7)), int_neg(of_u64(2)))), "4");
        assert_eq!(dec(&int_emod(int_neg(of_u64(7)), int_neg(of_u64(2)))), "1");
        assert_eq!(dec(&nat_lor_u64(a.clone(), 5)), "18446744073709551621");
        assert_eq!(dec(&nat_xor_u64(nat_lor_u64(a.clone(), 5), 4)), "18446744073709551617");
        assert_eq!(nat_log2(a.clone()), 64);
        assert_eq!(dec(&nat_shr(nat_shl(a.clone(), 100), 99)), "36893488147419103232");
        assert_eq!(dec(&pow2(64)), "18446744073709551616");
        assert_eq!(dec(&u64_pow(10, 20)), "100000000000000000000");
        // in place on a unique value, a copy for a shared one
        let s = a.clone();
        let t = nat_add_u64(s, 1);
        assert_eq!(dec(&a), "18446744073709551616");
        assert_eq!(dec(&t), "18446744073709551617");
    }

    /// The same operand twice (one block, count 2): never written in place.
    #[test]
    fn aliased_operands() {
        let a = of_decimal("340282366920938463463374607431768211457");
        assert_eq!(dec(&nat_add(a.clone(), a.clone())), "680564733841876926926749214863536422914");
        assert_eq!(dec(&nat_sub(a.clone(), a.clone())), "0");
        assert_eq!(dec(&int_sub(a.clone(), a.clone())), "0");
        assert_eq!(dec(&nat_mul(a.clone(), a.clone())), "115792089237316195423570985008687907853950549399482440966384333222776666062849");
        assert_eq!(dec(&nat_div(a.clone(), a.clone())), "1");
        assert_eq!(dec(&nat_mod(a.clone(), a.clone())), "0");
        assert_eq!(dec(&nat_land(a.clone(), a.clone())), dec(&a));
        assert_eq!(dec(&nat_xor(a.clone(), a.clone())), "0");
        assert_eq!(dec(&nat_gcd(a.clone(), a.clone())), dec(&a));
        assert_eq!(a.count(), 1);
    }

    /// GMP's `mpz` functions, as a reference.
    fn reference(f: unsafe extern "C" fn(*mut Mpz, *const Mpz, *const Mpz), a: &LBig, b: &LBig) -> String {
        let mut t = OwnedMpz::new();
        let (x, y) = (view(a), view(b));
        unsafe { f(t.ptr(), &x, &y) };
        dec(&of_mpz(&t.0))
    }

    /// A deterministic sequence of numbers of 0 to 5 limbs, both signs,
    /// with runs of all-zero and all-one limbs (carries and borrows).
    fn samples() -> Vec<LBig> {
        let mut s = 0x9E3779B97F4A7C15u64;
        let mut next = || {
            s ^= s << 13;
            s ^= s >> 7;
            s ^= s << 17;
            s
        };
        let mut out = Vec::new();
        for i in 0..60 {
            let n = i % 6;
            let mut l: Vec<u64> = (0..n).map(|_| match next() % 4 { 0 => 0, 1 => u64::MAX, _ => next() }).collect();
            if let Some(t) = l.last_mut() {
                if *t == 0 {
                    *t = 1;
                }
            }
            out.push(of_limbs(l.as_ptr(), n, i % 3 == 1));
        }
        out
    }

    /// Every operation on every pair, against `mpz`, with the operands
    /// unique (written in place) and shared (copied).
    #[test]
    fn against_mpz() {
        let xs = samples();
        let fresh = |b: &LBig| of_limbs(b.ptr(), b.len(), b.neg());
        for a in &xs {
            for b in &xs {
                for shared in [false, true] {
                    let pair = || if shared { (a.clone(), b.clone()) } else { (fresh(a), fresh(b)) };
                    let (x, y) = pair();
                    assert_eq!(dec(&int_add(x, y)), reference(__gmpz_add, a, b));
                    let (x, y) = pair();
                    assert_eq!(dec(&int_sub(x, y)), reference(__gmpz_sub, a, b));
                    let (x, y) = pair();
                    assert_eq!(dec(&int_mul(x, y)), reference(__gmpz_mul, a, b));
                    let (x, y) = pair();
                    assert_eq!(nat_cmp(x, y), unsafe { __gmpz_cmp(&view(a), &view(b)) }.signum() as i64);
                    if b.len() != 0 {
                        let (x, y) = pair();
                        assert_eq!(dec(&int_tdiv(x, y)), reference(__gmpz_tdiv_q, a, b));
                        let (x, y) = pair();
                        assert_eq!(dec(&int_tmod(x, y)), reference(__gmpz_tdiv_r, a, b));
                        let (x, y) = pair();
                        let e = if b.neg() { reference(__gmpz_cdiv_q, a, b) } else { reference(__gmpz_fdiv_q, a, b) };
                        assert_eq!(dec(&int_ediv(x, y)), e);
                        let (x, y) = pair();
                        assert_eq!(dec(&int_emod(x, y)), reference(__gmpz_mod, a, b));
                    }
                    if !a.neg() && !b.neg() {
                        let (x, y) = pair();
                        assert_eq!(dec(&nat_land(x, y)), reference(__gmpz_and, a, b));
                        let (x, y) = pair();
                        assert_eq!(dec(&nat_lor(x, y)), reference(__gmpz_ior, a, b));
                        let (x, y) = pair();
                        assert_eq!(dec(&nat_xor(x, y)), reference(__gmpz_xor, a, b));
                        let (x, y) = pair();
                        assert_eq!(dec(&nat_gcd(x, y)), reference(__gmpz_gcd, a, b));
                        let (x, y) = pair();
                        let t = if cmp(a, b) <= 0 { "0".to_string() } else { reference(__gmpz_sub, a, b) };
                        assert_eq!(dec(&nat_sub(x, y)), t);
                    }
                }
            }
            if !a.neg() && a.len() > 0 {
                for s in [0u64, 1, 63, 64, 65, 127, 128, 200] {
                    for shared in [false, true] {
                        let x = || if shared { a.clone() } else { fresh(a) };
                        let mut t = OwnedMpz::new();
                        unsafe { __gmpz_mul_2exp(t.ptr(), &view(a), s) };
                        assert_eq!(dec(&nat_shl(x(), s)), dec(&of_mpz(&t.0)));
                        unsafe { __gmpz_tdiv_q_2exp(t.ptr(), &view(a), s) };
                        assert_eq!(dec(&nat_shr(x(), s)), dec(&of_mpz(&t.0)));
                    }
                }
                for y in [0u64, 1, 2, 3, u64::MAX, 1 << 63] {
                    for shared in [false, true] {
                        let x = || if shared { a.clone() } else { fresh(a) };
                        let mut t = OwnedMpz::new();
                        unsafe { __gmpz_add_ui(t.ptr(), &view(a), y) };
                        assert_eq!(dec(&nat_add_u64(x(), y)), dec(&of_mpz(&t.0)));
                        unsafe { __gmpz_mul_ui(t.ptr(), &view(a), y) };
                        assert_eq!(dec(&nat_mul_u64(x(), y)), dec(&of_mpz(&t.0)));
                        if y != 0 {
                            unsafe { __gmpz_tdiv_q_ui(t.ptr(), &view(a), y) };
                            assert_eq!(dec(&nat_div_u64(x(), y)), dec(&of_mpz(&t.0)));
                            assert_eq!(nat_mod_u64(x(), y), unsafe { __gmpz_tdiv_ui(&view(a), y) });
                        }
                        if cmp_mag(a, &of_u64(y)) >= 0 {
                            unsafe { __gmpz_sub_ui(t.ptr(), &view(a), y) };
                            assert_eq!(dec(&nat_sub_u64(x(), y)), dec(&of_mpz(&t.0)));
                        }
                    }
                }
            }
        }
        // Every number is still referenced once only by `xs`.
        assert!(xs.iter().all(|x| x.count() == 1));
    }

    /// In-place results keep the block until it must grow.
    #[test]
    fn in_place() {
        let a = of_limbs2(u64::MAX, u64::MAX);
        let a = nat_mul_u64(a, 3);
        assert_eq!(dec(&a), "1020847100762815390390123822295304634365");
        let q = a.0;
        let a = nat_sub_u64(a, 5);
        let a = nat_div_u64(a, 3);
        let a = nat_add_u64(a, 1);
        let a = nat_mod(a, of_u64(1 << 40));
        assert_eq!(a.0, q);
        assert_eq!(dec(&a), (340282366920938463463374607431768211454u128 % (1u128 << 40)).to_string());
    }
}
