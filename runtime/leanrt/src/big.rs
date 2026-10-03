//! Big natural numbers and integers: the slow paths of `Nat` and `Int`.
//!
//! A big number is laid out exactly as Lean's `lean_mpz_object`: Lean's
//! object header (the 32-bit reference count, `m_cs_sz`, `m_other` and
//! `m_tag = LeanMPZ`) followed by GMP's `mpz_t` (`_mp_alloc`, `_mp_size`,
//! the limb pointer; the limbs allocated by GMP). Here it is a
//! `reussir_rt::rc::Rc<BigZ>`: Reussir's box is its 32-bit count, then the
//! payload at offset 8; the four header bytes in between, padding to
//! Reussir, are written at creation. So a `Nat`/`Int` word that points to a
//! big number is what native Lean's would be (see `crate::nat`), and the
//! values are normalized like Lean's: `crate::nat` keeps a `Nat` below 2^63
//! and an `Int` in the `int32` range in the word itself, so a big number is
//! always outside those ranges. Functions whose result may fall back into
//! them return an `LBig` anyway; `LNat::of_big`/`LInt::of_big` normalize.
//!
//! The operations are GMP's `mpz` functions, as Lean's runtime uses
//! (`src/runtime/mpz.cpp`, `object.cpp`), with Lean's semantics: truncating
//! subtraction, `x / 0 = 0`, `x % 0 = x`, `Int.div`/`Int.mod` truncate,
//! `Int.ediv`/`Int.emod` are Euclidean.
//!
//! All functions consume their `LBig` arguments. When the first argument
//! is uniquely referenced, the result is computed into it (GMP allows the
//! output to alias an input).

use crate::gmp::*;
use reussir_rt::rc::Rc;
use std::ffi::c_void;

/// Lean's object tag of a big number (`LeanMPZ` in `lean.h`).
pub const LEAN_MPZ_TAG: u8 = 250;

/// A big number's payload: GMP's `mpz_t`, cleared (limbs freed) on drop.
#[repr(transparent)]
pub struct BigZ(pub Mpz);

pub type LBig = Rc<BigZ>;

/// The whole object, as `lean_mpz_object`.
#[repr(C)]
struct BigObj {
    count: u32,
    cs_sz: u16,
    other: u8,
    tag: u8,
    z: Mpz,
}

const _: () = assert!(std::mem::size_of::<BigObj>() == 24);

extern "C" {
    fn mi_malloc(size: usize) -> *mut c_void;
}

impl Drop for BigZ {
    fn drop(&mut self) {
        #[cfg(leanrt_count_bigs)]
        count::freed();
        unsafe { __gmpz_clear(&mut self.0) }
    }
}

/// Counts of the big numbers made and freed, for tests: built with
/// `--cfg leanrt_count_bigs` (`L2R_LEANRT_RUSTFLAGS`, see
/// `tests/runtime/nat-alloc-check.sh`), a program prints them to stderr at
/// exit. Not compiled otherwise.
#[cfg(leanrt_count_bigs)]
mod count {
    use std::sync::atomic::{AtomicU64, Ordering::Relaxed};

    static MADE: AtomicU64 = AtomicU64::new(0);
    static FREED: AtomicU64 = AtomicU64::new(0);
    static REPORT: std::sync::Once = std::sync::Once::new();

    extern "C" {
        fn atexit(f: extern "C" fn()) -> i32;
    }

    extern "C" fn report() {
        let (m, f) = (MADE.load(Relaxed), FREED.load(Relaxed));
        eprintln!("leanrt: big numbers made {} freed {} live {}", m, f, m as i64 - f as i64);
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
}

#[cold]
#[inline(never)]
fn oom() -> ! {
    crate::internal_panic("out of memory")
}

/// A new object (count 1) owning the initialized `z`.
#[inline]
fn wrap(z: Mpz) -> LBig {
    #[cfg(leanrt_count_bigs)]
    count::made();
    unsafe {
        let p = mi_malloc(std::mem::size_of::<BigObj>()) as *mut BigObj;
        if p.is_null() {
            oom();
        }
        std::ptr::write(p, BigObj { count: 1, cs_sz: std::mem::size_of::<BigObj>() as u16, other: 0, tag: LEAN_MPZ_TAG, z });
        std::mem::transmute::<*mut BigObj, LBig>(p)
    }
}

#[inline]
fn empty() -> Mpz {
    Mpz { alloc: 0, size: 0, d: std::ptr::null_mut() }
}

/// A new big number computed by `f` into a fresh `mpz_t`.
#[inline]
fn make(f: impl FnOnce(*mut Mpz)) -> LBig {
    let mut z = empty();
    unsafe { __gmpz_init(&mut z) };
    f(&mut z);
    wrap(z)
}

#[inline]
fn z(b: &LBig) -> *const Mpz {
    &b.0
}

/// `r = f(a, b)`, into `a` when it is unique (and so not `b` itself).
#[inline]
fn binop(a: LBig, b: LBig, f: unsafe extern "C" fn(*mut Mpz, *const Mpz, *const Mpz)) -> LBig {
    let mut a = a;
    if a.is_unique() {
        let r = unsafe { &mut a.data_mut().0 } as *mut Mpz;
        unsafe { f(r, r, z(&b)) };
        return a;
    }
    make(|r| unsafe { f(r, z(&a), z(&b)) })
}

/// `r = f(a, y)` for a word `y`, into `a` when it is unique.
#[inline]
fn op_ui(a: LBig, y: u64, f: unsafe extern "C" fn(*mut Mpz, *const Mpz, u64)) -> LBig {
    let mut a = a;
    if a.is_unique() {
        let r = unsafe { &mut a.data_mut().0 } as *mut Mpz;
        unsafe { f(r, r, y) };
        return a;
    }
    make(|r| unsafe { f(r, z(&a), y) })
}

/// `r = f(a)`, into `a` when it is unique.
#[inline]
fn unop(a: LBig, f: unsafe extern "C" fn(*mut Mpz, *const Mpz)) -> LBig {
    let mut a = a;
    if a.is_unique() {
        let r = unsafe { &mut a.data_mut().0 } as *mut Mpz;
        unsafe { f(r, r) };
        return a;
    }
    make(|r| unsafe { f(r, z(&a)) })
}

// ---------------------------------------------------------------------------
// Construction and inspection

#[inline(never)]
pub fn of_u64(x: u64) -> LBig {
    let mut z = empty();
    unsafe { __gmpz_init_set_ui(&mut z, x) };
    wrap(z)
}

/// `hi * 2^64 + lo`.
#[inline(never)]
pub fn of_limbs2(lo: u64, hi: u64) -> LBig {
    make(|r| unsafe {
        let d = __gmpz_limbs_write(r, 2);
        *d = lo;
        *d.add(1) = hi;
        __gmpz_limbs_finish(r, 2);
    })
}

#[inline(never)]
pub fn of_i64(x: i64) -> LBig {
    let mut z = empty();
    unsafe { __gmpz_init_set_si(&mut z, x) };
    wrap(z)
}

/// The magnitude's limbs, little-endian, without high zero limbs (empty
/// for zero).
#[inline]
pub fn limbs(b: &LBig) -> &[u64] {
    let n = b.0.size.unsigned_abs() as usize;
    if n == 0 { &[] } else { unsafe { std::slice::from_raw_parts(b.0.d, n) } }
}

#[inline]
pub fn is_neg(b: &LBig) -> bool {
    b.0.size < 0
}

/// Whether a non-negative value fits in a `u64`.
#[inline]
pub fn is_u64(b: &LBig) -> bool {
    !is_neg(b) && limbs(b).len() <= 1
}

/// The lowest limb of the magnitude (`0` for zero).
#[inline]
pub fn low_limb(b: &LBig) -> u64 {
    limbs(b).first().copied().unwrap_or(0)
}

/// Whether the value is in the `i64` range.
#[inline]
pub fn fits_i64(b: &LBig) -> bool {
    unsafe { __gmpz_fits_slong_p(z(b)) != 0 }
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
    let mut z = empty();
    unsafe { __gmpz_init_set_str(&mut z, digits.as_ptr(), 10) };
    wrap(z)
}

/// The decimal representation (with a leading `-` for negative values).
#[inline(never)]
pub fn to_decimal(b: &LBig) -> Vec<u8> {
    // `mpz_sizeinbase` may overestimate by one; one more for the sign and
    // one for the terminating NUL.
    let cap = unsafe { __gmpz_sizeinbase(z(b), 10) } + 2;
    let mut out = vec![0u8; cap];
    unsafe { __gmpz_get_str(out.as_mut_ptr(), 10, z(b)) };
    let n = out.iter().position(|&c| c == 0).unwrap_or(out.len());
    out.truncate(n);
    out
}

// ---------------------------------------------------------------------------
// Nat (non-negative) operations. Arguments are big `Nat`s (>= 2^63)
// unless stated otherwise.

/// `a + b`.
#[inline(never)]
pub fn nat_add(a: LBig, b: LBig) -> LBig {
    binop(a, b, __gmpz_add)
}

/// `a + y` for a big `a` and any `y`.
#[inline(never)]
pub fn nat_add_u64(a: LBig, y: u64) -> LBig {
    op_ui(a, y, __gmpz_add_ui)
}

/// Truncated subtraction `a - b` (0 when `a < b`).
#[inline(never)]
pub fn nat_sub(a: LBig, b: LBig) -> LBig {
    if unsafe { __gmpz_cmp(z(&a), z(&b)) } <= 0 {
        return of_u64(0);
    }
    binop(a, b, __gmpz_sub)
}

/// `a - y` for a big `a` (never truncates: `y < 2^63 <= a`).
#[inline(never)]
pub fn nat_sub_u64(a: LBig, y: u64) -> LBig {
    op_ui(a, y, __gmpz_sub_ui)
}

#[inline(never)]
pub fn nat_mul(a: LBig, b: LBig) -> LBig {
    binop(a, b, __gmpz_mul)
}

/// `a * y`.
#[inline(never)]
pub fn nat_mul_u64(a: LBig, y: u64) -> LBig {
    op_ui(a, y, __gmpz_mul_ui)
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
    binop(a, b, __gmpz_tdiv_q)
}

unsafe extern "C" fn tdiv_q_ui(r: *mut Mpz, a: *const Mpz, y: u64) {
    __gmpz_tdiv_q_ui(r, a, y);
}

/// `a / y` for `y != 0`.
#[inline(never)]
pub fn nat_div_u64(a: LBig, y: u64) -> LBig {
    op_ui(a, y, tdiv_q_ui)
}

/// `a % b` for a nonzero `b`.
#[inline(never)]
pub fn nat_mod(a: LBig, b: LBig) -> LBig {
    binop(a, b, __gmpz_tdiv_r)
}

/// `a % y` for `y != 0`.
#[inline(never)]
pub fn nat_mod_u64(a: LBig, y: u64) -> u64 {
    unsafe { __gmpz_tdiv_ui(z(&a), y) }
}

/// Three-way comparison: -1, 0, 1 (any signs).
#[inline(never)]
pub fn nat_cmp(a: LBig, b: LBig) -> i64 {
    let c = unsafe { __gmpz_cmp(z(&a), z(&b)) };
    (c > 0) as i64 - (c < 0) as i64
}

#[inline(never)]
pub fn nat_eq(a: LBig, b: LBig) -> bool {
    unsafe { __gmpz_cmp(z(&a), z(&b)) == 0 }
}

#[inline(never)]
pub fn nat_land(a: LBig, b: LBig) -> LBig {
    binop(a, b, __gmpz_and)
}

#[inline(never)]
pub fn nat_land_u64(a: LBig, y: u64) -> u64 {
    low_limb(&a) & y
}

#[inline(never)]
pub fn nat_lor(a: LBig, b: LBig) -> LBig {
    binop(a, b, __gmpz_ior)
}

/// Apply `f` to the lowest limb of a positive `a` (into `a` when unique).
#[inline]
fn with_low_limb(a: LBig, f: impl FnOnce(u64) -> u64) -> LBig {
    let mut a = if a.is_unique() { a } else { make(|r| unsafe { __gmpz_set(r, z(&a)) }) };
    unsafe {
        let r: *mut Mpz = &mut a.data_mut().0;
        let n = (*r).size as i64;
        let d = __gmpz_limbs_modify(r, n);
        *d = f(*d);
        __gmpz_limbs_finish(r, n);
    }
    a
}

/// `a ||| y` for a big `a` (>= 2^63, at least one limb).
#[inline(never)]
pub fn nat_lor_u64(a: LBig, y: u64) -> LBig {
    with_low_limb(a, |l| l | y)
}

#[inline(never)]
pub fn nat_xor(a: LBig, b: LBig) -> LBig {
    binop(a, b, __gmpz_xor)
}

/// `a ^^^ y` for a big `a` (>= 2^63, at least one limb).
#[inline(never)]
pub fn nat_xor_u64(a: LBig, y: u64) -> LBig {
    with_low_limb(a, |l| l ^ y)
}

/// `a <<< s`; `s <= 2^32 - 1` (checked by the caller).
#[inline(never)]
pub fn nat_shl(a: LBig, s: u64) -> LBig {
    op_ui(a, s, __gmpz_mul_2exp)
}

/// `a >>> s` (a non-negative).
#[inline(never)]
pub fn nat_shr(a: LBig, s: u64) -> LBig {
    op_ui(a, s, __gmpz_tdiv_q_2exp)
}

/// Bit length minus one (`Nat.log2`) of a positive value.
#[inline(never)]
pub fn nat_log2(a: LBig) -> u64 {
    if limbs(&a).is_empty() {
        return 0;
    }
    (unsafe { __gmpz_sizeinbase(z(&a), 2) } - 1) as u64
}

/// `a ^ e`.
#[inline(never)]
pub fn nat_pow(a: LBig, e: u64) -> LBig {
    make(|r| unsafe { __gmpz_pow_ui(r, z(&a), e) })
}

#[inline(never)]
pub fn nat_gcd(a: LBig, b: LBig) -> LBig {
    binop(a, b, __gmpz_gcd)
}

// ---------------------------------------------------------------------------
// Int (signed) operations. Small operands are converted by the caller with
// `of_i64`.

/// The magnitude (for `Int.natAbs`/`Int.toNat`).
#[inline(never)]
pub fn int_abs(a: LBig) -> LBig {
    if !is_neg(&a) {
        return a;
    }
    unop(a, __gmpz_abs)
}

#[inline(never)]
pub fn int_add(a: LBig, b: LBig) -> LBig {
    binop(a, b, __gmpz_add)
}

#[inline(never)]
pub fn int_sub(a: LBig, b: LBig) -> LBig {
    binop(a, b, __gmpz_sub)
}

#[inline(never)]
pub fn int_mul(a: LBig, b: LBig) -> LBig {
    binop(a, b, __gmpz_mul)
}

#[inline(never)]
pub fn int_neg(a: LBig) -> LBig {
    if limbs(&a).is_empty() {
        return a;
    }
    unop(a, __gmpz_neg)
}

/// Truncating quotient (`Int.tdiv`, C `/`); `b` must be nonzero.
#[inline(never)]
pub fn int_tdiv(a: LBig, b: LBig) -> LBig {
    binop(a, b, __gmpz_tdiv_q)
}

/// Truncating remainder (`Int.tmod`, C `%`, sign of the dividend); `b` nonzero.
#[inline(never)]
pub fn int_tmod(a: LBig, b: LBig) -> LBig {
    binop(a, b, __gmpz_tdiv_r)
}

/// Euclidean quotient (`Int.ediv`); `b` nonzero: the floor of `a / b` for
/// `b > 0`, the ceiling for `b < 0` (so that `a - b * q` is in `[0, |b|)`).
#[inline(never)]
pub fn int_ediv(a: LBig, b: LBig) -> LBig {
    if is_neg(&b) { binop(a, b, __gmpz_cdiv_q) } else { binop(a, b, __gmpz_fdiv_q) }
}

/// Euclidean remainder (`Int.emod`, always `>= 0`); `b` nonzero.
#[inline(never)]
pub fn int_emod(a: LBig, b: LBig) -> LBig {
    binop(a, b, __gmpz_mod)
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
        // Lean's `lean_mpz_object`: the count at 0, the tag at 7, the mpz_t at 8.
        let b = of_decimal("123456789012345678901234567890");
        let p = unsafe { std::mem::transmute_copy::<LBig, *const u8>(&b) };
        unsafe {
            assert_eq!(*(p as *const u32), 1);
            assert_eq!(*p.add(7), LEAN_MPZ_TAG);
            assert_eq!(*(p.add(12) as *const i32), 2); // _mp_size: two limbs
        }
        let c = b.clone();
        unsafe { assert_eq!(*(p as *const u32), 2) };
        drop(c);
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
        // in place on a unique value, a copy for a shared one
        let s = a.clone();
        let t = nat_add_u64(s, 1);
        assert_eq!(dec(&a), "18446744073709551616");
        assert_eq!(dec(&t), "18446744073709551617");
    }
}
