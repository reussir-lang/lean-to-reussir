//! Big natural numbers and integers: the slow paths of `Nat` and `Int`.
//!
//! A big number is `Rc<(neg, limbs)>`: sign and magnitude, little-endian
//! 64-bit limbs without high zero limbs (zero is the empty vector, never
//! negative). The Reussir side keeps small values unboxed (`Nat::Small(u64)`,
//! `Int::Small(i64)`) and only stores values outside the machine-word range
//! here (`Nat::Big` holds values `>= 2^64`, `Int::Big` values outside the
//! `i64` range). Functions whose result may fall back into the word range
//! return an `LBig` anyway; the caller normalizes with `is_u64`/`fits_i64`.
//!
//! Semantics follow Lean's runtime (`src/runtime/object.cpp`), which uses
//! the same GMP operations: truncating subtraction, `x / 0 = 0`,
//! `x % 0 = x`, `Int.div`/`Int.mod` truncate (`mpz_tdiv_*`), `Int.ediv`/
//! `Int.emod` are Euclidean.
//!
//! All functions consume their `LBig` arguments. When an argument is
//! uniquely referenced its buffer is reused in place.

use crate::gmp::*;
use reussir_rt::rc::Rc;

pub type LBig = Rc<(bool, Vec<u64>)>;

#[inline]
fn norm(v: &mut Vec<u64>) {
    while let Some(&0) = v.last() {
        v.pop();
    }
}

#[inline]
fn mk(neg: bool, mut v: Vec<u64>) -> LBig {
    norm(&mut v);
    let neg = neg && !v.is_empty();
    Rc::new((neg, v))
}

/// A vector of `n` uninitialized-then-zeroed limbs (GMP writes all of them).
#[inline]
fn zeroed(n: usize) -> Vec<u64> {
    vec![0u64; n]
}

// ---------------------------------------------------------------------------
// Construction and inspection

#[inline(never)]
pub fn of_u64(x: u64) -> LBig {
    Rc::new((false, if x == 0 { Vec::new() } else { vec![x] }))
}

/// `hi * 2^64 + lo`.
#[inline(never)]
pub fn of_limbs2(lo: u64, hi: u64) -> LBig {
    mk(false, vec![lo, hi])
}

#[inline(never)]
pub fn of_i64(x: i64) -> LBig {
    let m = x.unsigned_abs();
    Rc::new((x < 0, if m == 0 { Vec::new() } else { vec![m] }))
}

/// Whether a non-negative value fits in a `u64`.
#[inline]
pub fn is_u64(b: &LBig) -> bool {
    !b.0 && b.1.len() <= 1
}

/// The lowest limb of the magnitude (`0` for zero).
#[inline]
pub fn low_limb(b: &LBig) -> u64 {
    b.1.first().copied().unwrap_or(0)
}

/// Whether the value is in the `i64` range.
#[inline]
pub fn fits_i64(b: &LBig) -> bool {
    match b.1.len() {
        0 => true,
        1 => {
            let m = b.1[0];
            if b.0 { m <= 1u64 << 63 } else { m < 1u64 << 63 }
        }
        _ => false,
    }
}

/// The value modulo 2^64 in two's complement (for `Int64.ofInt`,
/// `Int8.ofInt`, ... which take the low bits, like `mpz::smod64`).
#[inline]
pub fn low_u64_twos(b: &LBig) -> u64 {
    let m = low_limb(b);
    if b.0 { m.wrapping_neg() } else { m }
}

#[inline]
pub fn is_neg(b: &LBig) -> bool {
    b.0
}

/// Parse a decimal digit string (as produced by lean2rr for big literals).
#[inline(never)]
pub fn of_decimal(s: &str) -> LBig {
    let digits: Vec<u8> = s.bytes().filter(|c| c.is_ascii_digit()).map(|c| c - b'0').collect();
    let start = digits.iter().position(|&d| d != 0).unwrap_or(digits.len());
    let digits = &digits[start..];
    if digits.is_empty() {
        return of_u64(0);
    }
    // 10^19 < 2^64: at most one limb per 19 digits, plus one.
    let mut r = zeroed(digits.len() / 19 + 2);
    let n = unsafe { __gmpn_set_str(r.as_mut_ptr(), digits.as_ptr(), digits.len(), 10) };
    r.truncate(n as usize);
    mk(false, r)
}

/// Decimal digits of a magnitude.
fn mag_to_decimal(m: &[u64], out: &mut Vec<u8>) {
    if m.is_empty() {
        out.push(b'0');
        return;
    }
    let mut tmp = m.to_vec(); // mpn_get_str clobbers its input
    // Allocate one extra limb as mpn_get_str requires s1p to have n+1 limbs available.
    tmp.push(0);
    let cap = unsafe { __gmpn_sizeinbase(m.as_ptr(), m.len() as i64, 10) } + 1;
    let start = out.len();
    out.resize(start + cap, 0);
    let n = unsafe { __gmpn_get_str(out.as_mut_ptr().add(start), 10, tmp.as_mut_ptr(), m.len() as i64) };
    out.truncate(start + n);
    // Leading zeros are possible only for the value 0, which is handled above.
    for d in &mut out[start..] {
        *d += b'0';
    }
}

/// The decimal representation (with a leading `-` for negative values).
#[inline(never)]
pub fn to_decimal(b: &LBig) -> Vec<u8> {
    let mut out = Vec::new();
    if b.0 {
        out.push(b'-');
    }
    mag_to_decimal(&b.1, &mut out);
    out
}

// ---------------------------------------------------------------------------
// Magnitude arithmetic (slices, no signs)

fn mag_cmp(a: &[u64], b: &[u64]) -> std::cmp::Ordering {
    use std::cmp::Ordering;
    if a.len() != b.len() {
        return a.len().cmp(&b.len());
    }
    if a.is_empty() {
        return Ordering::Equal;
    }
    let c = unsafe { __gmpn_cmp(a.as_ptr(), b.as_ptr(), a.len() as i64) };
    c.cmp(&0)
}

fn mag_add(a: &[u64], b: &[u64]) -> Vec<u64> {
    let (x, y) = if a.len() >= b.len() { (a, b) } else { (b, a) };
    if y.is_empty() {
        return x.to_vec();
    }
    let mut r = zeroed(x.len() + 1);
    let c = unsafe { __gmpn_add(r.as_mut_ptr(), x.as_ptr(), x.len() as i64, y.as_ptr(), y.len() as i64) };
    r[x.len()] = c;
    norm(&mut r);
    r
}

/// `a - b`, requires `a >= b`.
fn mag_sub(a: &[u64], b: &[u64]) -> Vec<u64> {
    if b.is_empty() {
        return a.to_vec();
    }
    let mut r = zeroed(a.len());
    unsafe { __gmpn_sub(r.as_mut_ptr(), a.as_ptr(), a.len() as i64, b.as_ptr(), b.len() as i64) };
    norm(&mut r);
    r
}

fn mag_mul(a: &[u64], b: &[u64]) -> Vec<u64> {
    if a.is_empty() || b.is_empty() {
        return Vec::new();
    }
    let (x, y) = if a.len() >= b.len() { (a, b) } else { (b, a) };
    let mut r = zeroed(x.len() + y.len());
    unsafe {
        if x.as_ptr() == y.as_ptr() && x.len() == y.len() {
            __gmpn_sqr(r.as_mut_ptr(), x.as_ptr(), x.len() as i64);
        } else {
            __gmpn_mul(r.as_mut_ptr(), x.as_ptr(), x.len() as i64, y.as_ptr(), y.len() as i64);
        }
    }
    norm(&mut r);
    r
}

/// Truncating division of magnitudes, `b` nonzero: `(q, r)`.
fn mag_divmod(a: &[u64], b: &[u64]) -> (Vec<u64>, Vec<u64>) {
    debug_assert!(!b.is_empty());
    if mag_cmp(a, b) == std::cmp::Ordering::Less {
        return (Vec::new(), a.to_vec());
    }
    if b.len() == 1 {
        let mut q = zeroed(a.len());
        let r = unsafe { __gmpn_divrem_1(q.as_mut_ptr(), 0, a.as_ptr(), a.len() as i64, b[0]) };
        norm(&mut q);
        return (q, if r == 0 { Vec::new() } else { vec![r] });
    }
    let mut q = zeroed(a.len() - b.len() + 1);
    let mut r = zeroed(b.len());
    unsafe {
        __gmpn_tdiv_qr(q.as_mut_ptr(), r.as_mut_ptr(), 0, a.as_ptr(), a.len() as i64, b.as_ptr(), b.len() as i64)
    };
    norm(&mut q);
    norm(&mut r);
    (q, r)
}

// ---------------------------------------------------------------------------
// Nat (non-negative) operations. Arguments are `Nat::Big` handles (>= 2^64)
// unless stated otherwise.

/// `a + b`; reuses `a`'s buffer when it is unique.
#[inline(never)]
pub fn nat_add(a: LBig, b: LBig) -> LBig {
    let (mut x, y) = if a.1.len() >= b.1.len() { (a, b) } else { (b, a) };
    if x.is_unique() {
        let v = unsafe { &mut x.data_mut().1 };
        let n = v.len();
        v.push(0);
        let c = unsafe { __gmpn_add(v.as_mut_ptr(), v.as_ptr(), n as i64, y.1.as_ptr(), y.1.len() as i64) };
        if c == 0 {
            v.pop();
        } else {
            v[n] = c;
        }
        x
    } else {
        Rc::new((false, mag_add(&x.1, &y.1)))
    }
}

/// `a + y` for a big `a` and any `y`.
#[inline(never)]
pub fn nat_add_u64(a: LBig, y: u64) -> LBig {
    let mut a = a;
    if a.is_unique() {
        let v = unsafe { &mut a.data_mut().1 };
        let n = v.len();
        v.push(0);
        let c = unsafe { __gmpn_add_1(v.as_mut_ptr(), v.as_ptr(), n as i64, y) };
        if c == 0 {
            v.pop();
        } else {
            v[n] = c;
        }
        a
    } else {
        Rc::new((false, mag_add(&a.1, &[y])))
    }
}

/// `x + y` when the sum overflows 64 bits.
#[inline(never)]
pub fn u64_add_overflow(x: u64, y: u64) -> LBig {
    of_limbs2(x.wrapping_add(y), 1)
}

/// Truncated subtraction `a - b` (0 when `a < b`).
#[inline(never)]
pub fn nat_sub(a: LBig, b: LBig) -> LBig {
    if mag_cmp(&a.1, &b.1) != std::cmp::Ordering::Greater {
        return of_u64(0);
    }
    let mut a = a;
    if a.is_unique() {
        let v = unsafe { &mut a.data_mut().1 };
        unsafe { __gmpn_sub(v.as_mut_ptr(), v.as_ptr(), v.len() as i64, b.1.as_ptr(), b.1.len() as i64) };
        norm(v);
        a
    } else {
        Rc::new((false, mag_sub(&a.1, &b.1)))
    }
}

/// `a - y` for a big `a` (never truncates).
#[inline(never)]
pub fn nat_sub_u64(a: LBig, y: u64) -> LBig {
    let mut a = a;
    if a.is_unique() {
        let v = unsafe { &mut a.data_mut().1 };
        unsafe { __gmpn_sub_1(v.as_mut_ptr(), v.as_ptr(), v.len() as i64, y) };
        norm(v);
        a
    } else {
        Rc::new((false, mag_sub(&a.1, &[y])))
    }
}

#[inline(never)]
pub fn nat_mul(a: LBig, b: LBig) -> LBig {
    Rc::new((false, mag_mul(&a.1, &b.1)))
}

/// `a * y` for `y != 0`; reuses `a`'s buffer when it is unique.
#[inline(never)]
pub fn nat_mul_u64(a: LBig, y: u64) -> LBig {
    if y == 0 {
        return of_u64(0);
    }
    let mut a = a;
    if a.is_unique() {
        let v = unsafe { &mut a.data_mut().1 };
        let n = v.len();
        v.push(0);
        let c = unsafe { __gmpn_mul_1(v.as_mut_ptr(), v.as_ptr(), n as i64, y) };
        if c == 0 {
            v.pop();
        } else {
            v[n] = c;
        }
        a
    } else {
        let mut r = zeroed(a.1.len() + 1);
        let n = a.1.len();
        let c = unsafe { __gmpn_mul_1(r.as_mut_ptr(), a.1.as_ptr(), n as i64, y) };
        r[n] = c;
        mk(false, r)
    }
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

/// `a / b` for a nonzero big `b` (any `a`, as a handle).
#[inline(never)]
pub fn nat_div(a: LBig, b: LBig) -> LBig {
    Rc::new((false, mag_divmod(&a.1, &b.1).0))
}

/// `a / y` for `y != 0`.
#[inline(never)]
pub fn nat_div_u64(a: LBig, y: u64) -> LBig {
    let mut a = a;
    if a.is_unique() {
        let v = unsafe { &mut a.data_mut().1 };
        unsafe { __gmpn_divrem_1(v.as_mut_ptr(), 0, v.as_ptr(), v.len() as i64, y) };
        norm(v);
        a
    } else {
        let mut q = zeroed(a.1.len());
        unsafe { __gmpn_divrem_1(q.as_mut_ptr(), 0, a.1.as_ptr(), a.1.len() as i64, y) };
        mk(false, q)
    }
}

#[inline(never)]
pub fn nat_mod(a: LBig, b: LBig) -> LBig {
    Rc::new((false, mag_divmod(&a.1, &b.1).1))
}

/// `a % y` for `y != 0`.
#[inline(never)]
pub fn nat_mod_u64(a: LBig, y: u64) -> u64 {
    unsafe { __gmpn_mod_1(a.1.as_ptr(), a.1.len() as i64, y) }
}

/// Three-way comparison of two non-negative values: -1, 0, 1.
#[inline(never)]
pub fn nat_cmp(a: LBig, b: LBig) -> i64 {
    match mag_cmp(&a.1, &b.1) {
        std::cmp::Ordering::Less => -1,
        std::cmp::Ordering::Equal => 0,
        std::cmp::Ordering::Greater => 1,
    }
}

#[inline(never)]
pub fn nat_eq(a: LBig, b: LBig) -> bool {
    a.1 == b.1
}

fn mag_bitop(a: &[u64], b: &[u64], op: u8) -> Vec<u64> {
    let (x, y) = if a.len() >= b.len() { (a, b) } else { (b, a) };
    let n = y.len();
    let mut r: Vec<u64> = match op {
        0 => zeroed(n), // and
        _ => x.to_vec(), // or, xor: high limbs of the longer operand
    };
    if n > 0 {
        unsafe {
            match op {
                0 => __gmpn_and_n(r.as_mut_ptr(), x.as_ptr(), y.as_ptr(), n as i64),
                1 => __gmpn_ior_n(r.as_mut_ptr(), x.as_ptr(), y.as_ptr(), n as i64),
                _ => __gmpn_xor_n(r.as_mut_ptr(), x.as_ptr(), y.as_ptr(), n as i64),
            }
        }
    }
    norm(&mut r);
    r
}

#[inline(never)]
pub fn nat_land(a: LBig, b: LBig) -> LBig {
    Rc::new((false, mag_bitop(&a.1, &b.1, 0)))
}

#[inline(never)]
pub fn nat_land_u64(a: LBig, y: u64) -> u64 {
    low_limb(&a) & y
}

#[inline(never)]
pub fn nat_lor(a: LBig, b: LBig) -> LBig {
    Rc::new((false, mag_bitop(&a.1, &b.1, 1)))
}

#[inline(never)]
pub fn nat_lor_u64(a: LBig, y: u64) -> LBig {
    let mut v = a.1.clone();
    v[0] |= y;
    Rc::new((false, v))
}

#[inline(never)]
pub fn nat_xor(a: LBig, b: LBig) -> LBig {
    Rc::new((false, mag_bitop(&a.1, &b.1, 2)))
}

#[inline(never)]
pub fn nat_xor_u64(a: LBig, y: u64) -> LBig {
    let mut v = a.1.clone();
    v[0] ^= y;
    Rc::new((false, v))
}

fn mag_shl(a: &[u64], s: u64) -> Vec<u64> {
    if a.is_empty() {
        return Vec::new();
    }
    let limbs = (s / 64) as usize;
    let bits = (s % 64) as u32;
    let mut r = zeroed(limbs + a.len() + 1);
    if bits == 0 {
        r[limbs..limbs + a.len()].copy_from_slice(a);
    } else {
        let c = unsafe { __gmpn_lshift(r.as_mut_ptr().add(limbs), a.as_ptr(), a.len() as i64, bits) };
        r[limbs + a.len()] = c;
    }
    norm(&mut r);
    r
}

fn mag_shr(a: &[u64], s: u64) -> Vec<u64> {
    let limbs = s / 64;
    if limbs >= a.len() as u64 {
        return Vec::new();
    }
    let limbs = limbs as usize;
    let bits = (s % 64) as u32;
    let src = &a[limbs..];
    let mut r = zeroed(src.len());
    if bits == 0 {
        r.copy_from_slice(src);
    } else {
        unsafe { __gmpn_rshift(r.as_mut_ptr(), src.as_ptr(), src.len() as i64, bits) };
    }
    norm(&mut r);
    r
}

/// `a <<< s` for any `a` (as a handle); `s <= 2^32 - 1` (checked by the caller).
#[inline(never)]
pub fn nat_shl(a: LBig, s: u64) -> LBig {
    Rc::new((false, mag_shl(&a.1, s)))
}

/// `a >>> s`.
#[inline(never)]
pub fn nat_shr(a: LBig, s: u64) -> LBig {
    Rc::new((false, mag_shr(&a.1, s)))
}

/// Bit length minus one (`Nat.log2`) of a nonzero magnitude.
#[inline(never)]
pub fn nat_log2(a: LBig) -> u64 {
    match a.1.last() {
        None => 0,
        Some(&top) => (a.1.len() as u64 - 1) * 64 + (63 - top.leading_zeros() as u64),
    }
}

/// `a ^ e` for any `a` (as a handle).
#[inline(never)]
pub fn nat_pow(a: LBig, e: u64) -> LBig {
    let mut r = OwnedMpz::new();
    let v = View::new(false, &a.1);
    unsafe { __gmpz_pow_ui(r.ptr(), v.ptr(), e) };
    let (_, limbs) = r.to_parts();
    Rc::new((false, limbs))
}

#[inline(never)]
pub fn nat_gcd(a: LBig, b: LBig) -> LBig {
    let mut r = OwnedMpz::new();
    let (va, vb) = (View::new(false, &a.1), View::new(false, &b.1));
    unsafe { __gmpz_gcd(r.ptr(), va.ptr(), vb.ptr()) };
    let (_, limbs) = r.to_parts();
    Rc::new((false, limbs))
}

/// The magnitude as a Nat handle (for `Int.natAbs`/`Int.toNat`).
#[inline(never)]
pub fn int_abs(a: LBig) -> LBig {
    if !a.0 {
        return a;
    }
    let mut a = a;
    if a.is_unique() {
        unsafe { a.data_mut().0 = false };
        a
    } else {
        Rc::new((false, a.1.clone()))
    }
}

// ---------------------------------------------------------------------------
// Int (signed) operations on handles. Small operands are converted by the
// caller with `of_i64`.

fn signed(neg: bool, m: Vec<u64>) -> LBig {
    mk(neg, m)
}

fn signed_add(an: bool, a: &[u64], bn: bool, b: &[u64]) -> LBig {
    if an == bn {
        return signed(an, mag_add(a, b));
    }
    match mag_cmp(a, b) {
        std::cmp::Ordering::Equal => of_u64(0),
        std::cmp::Ordering::Greater => signed(an, mag_sub(a, b)),
        std::cmp::Ordering::Less => signed(bn, mag_sub(b, a)),
    }
}

#[inline(never)]
pub fn int_add(a: LBig, b: LBig) -> LBig {
    signed_add(a.0, &a.1, b.0, &b.1)
}

#[inline(never)]
pub fn int_sub(a: LBig, b: LBig) -> LBig {
    signed_add(a.0, &a.1, !b.0 && !b.1.is_empty(), &b.1)
}

#[inline(never)]
pub fn int_mul(a: LBig, b: LBig) -> LBig {
    signed(a.0 != b.0, mag_mul(&a.1, &b.1))
}

#[inline(never)]
pub fn int_neg(a: LBig) -> LBig {
    if a.1.is_empty() {
        return a;
    }
    let mut a = a;
    if a.is_unique() {
        let d = unsafe { a.data_mut() };
        d.0 = !d.0;
        a
    } else {
        Rc::new((!a.0, a.1.clone()))
    }
}

/// Truncating quotient (`Int.tdiv`, C `/`); `b` must be nonzero.
#[inline(never)]
pub fn int_tdiv(a: LBig, b: LBig) -> LBig {
    let (q, _) = mag_divmod(&a.1, &b.1);
    signed(a.0 != b.0, q)
}

/// Truncating remainder (`Int.tmod`, C `%`, sign of the dividend); `b` nonzero.
#[inline(never)]
pub fn int_tmod(a: LBig, b: LBig) -> LBig {
    let (_, r) = mag_divmod(&a.1, &b.1);
    signed(a.0, r)
}

/// Euclidean quotient (`Int.ediv`); `b` nonzero. As `mpz::ediv`:
/// `q = tdiv(a, b)`, adjusted by one away from zero-remainder when the
/// truncated remainder is negative.
#[inline(never)]
pub fn int_ediv(a: LBig, b: LBig) -> LBig {
    let (q, r) = mag_divmod(&a.1, &b.1);
    let q = signed(a.0 != b.0, q);
    let r_neg = a.0 && !r.is_empty();
    if r_neg {
        if !b.0 {
            int_sub(q, of_u64(1))
        } else {
            int_add(q, of_u64(1))
        }
    } else {
        q
    }
}

/// Euclidean remainder (`Int.emod`, always `>= 0`); `b` nonzero.
#[inline(never)]
pub fn int_emod(a: LBig, b: LBig) -> LBig {
    let (_, r) = mag_divmod(&a.1, &b.1);
    if a.0 && !r.is_empty() {
        // r < 0: r + |b|
        Rc::new((false, mag_sub(&b.1, &r)))
    } else {
        Rc::new((false, r))
    }
}

#[inline(never)]
pub fn int_cmp(a: LBig, b: LBig) -> i64 {
    use std::cmp::Ordering;
    let o = match (a.0, b.0) {
        (false, true) => Ordering::Greater,
        (true, false) => Ordering::Less,
        (false, false) => mag_cmp(&a.1, &b.1),
        (true, true) => mag_cmp(&b.1, &a.1),
    };
    match o {
        Ordering::Less => -1,
        Ordering::Equal => 0,
        Ordering::Greater => 1,
    }
}

#[inline(never)]
pub fn int_eq(a: LBig, b: LBig) -> bool {
    a.0 == b.0 && a.1 == b.1
}

/// The value as an `i64` (requires `fits_i64`).
#[inline]
pub fn to_i64(b: &LBig) -> i64 {
    low_u64_twos(b) as i64
}

#[cfg(test)]
mod tests {
    use super::*;

    fn dec(b: &LBig) -> String {
        String::from_utf8(to_decimal(b)).unwrap()
    }

    #[test]
    fn decimal_roundtrip() {
        for s in ["0", "1", "18446744073709551616", "123456789012345678901234567890123456789"] {
            assert_eq!(dec(&of_decimal(s)), s);
        }
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
    }
}
