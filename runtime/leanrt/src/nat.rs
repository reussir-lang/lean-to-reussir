//! `Nat` and `Int` as one word each, as Lean represents them.
//!
//! A handle is a single machine word, exactly as in native Lean:
//!
//! - an odd word is a small value, `lean_box(v) = (v << 1) | 1`: a `Nat`
//!   below 2^63 (`LEAN_MAX_SMALL_NAT`), or an `Int` in the `int32` range
//!   (`LEAN_MIN_SMALL_INT..=LEAN_MAX_SMALL_INT`), boxed as Lean does,
//!   `lean_box((unsigned)(int)v)`: its 32-bit two's complement pattern,
//!   zero-extended, so a small `Nat` below 2^31 and the `Int` of the same
//!   value have the same word;
//! - an even word is an owned reference to a big number (`LBig`, a pointer
//!   to one block holding the count, the sign and size, and the limbs, see
//!   `big`): a `Nat` of at least 2^63, an `Int` outside the `int32` range.
//!
//! Every value has exactly one form (small when in range), so equality of
//! two small words is equality of the values, and a small value never
//! equals a big one.
//!
//! On the Reussir side `Nat` and `Int` are `tagged` opaque records
//! (`#[ffi(rust = "::leanrt::nat::LNat", tagged)]`, local Reussir patch):
//! Reussir copies and drops them like any shared handle, but its increment
//! touches the count only for an even word, and its decrement calls the
//! drop hook (`Drop` below) only for an even word. A Nat field therefore
//! takes one word, and a small value is never allocated.
//!
//! The prelude's fast paths work on the raw words (`into_raw`/`from_raw`);
//! everything else comes here. The slow paths below take raw words they own
//! (`u64`, as the prelude passes them) and return normalized handles. Their
//! rules (zero divisors, truncation, rounding, shift and exponent limits,
//! the size of a big result) are lean-runtime's (`semantics::nat`,
//! `semantics::int`, Lean 4.34's `lean.h` and `object.cpp`): a slow path
//! only views its words as the rules' `Nat`/`Int` (a word or a `big::GNat`/
//! `big::GInt`), calls the rule, normalizes its result into a word, and
//! ends the process with the rule's internal panic.

use crate::big::{self, GInt, GNat, LBig};
use lean_runtime::semantics as sem;
use sem::panic::InternalPanic;
use std::mem::forget;

/// A Lean `Nat` (see the module comment).
#[repr(transparent)]
pub struct LNat(*mut u8);

/// A Lean `Int` (see the module comment).
#[repr(transparent)]
pub struct LInt(*mut u8);

/// Small `Int`s are in [INT_MIN, INT_MAX] (`LEAN_MIN_SMALL_INT`,
/// `LEAN_MAX_SMALL_INT` on 64-bit targets).
pub const INT_MIN: i64 = i32::MIN as i64;
pub const INT_MAX: i64 = i32::MAX as i64;

#[inline(always)]
pub fn is_small(w: u64) -> bool {
    w & 1 == 1
}

#[inline(always)]
fn ptr_of(w: u64) -> *mut u8 {
    std::ptr::with_exposed_provenance_mut(w as usize)
}

#[inline(always)]
fn word_of(p: *mut u8) -> u64 {
    p.expose_provenance() as u64
}

/// The big number an even word owns (takes over its reference).
#[inline(always)]
unsafe fn big_of_word(w: u64) -> LBig {
    debug_assert!(!is_small(w));
    std::mem::transmute::<*mut u8, LBig>(ptr_of(w))
}

/// Borrow the big number of an even word.
#[inline(always)]
unsafe fn big_ref(w: &u64) -> &LBig {
    debug_assert!(!is_small(*w));
    &*(w as *const u64 as *const LBig)
}

#[inline(always)]
fn word_of_big(b: LBig) -> u64 {
    // `LBig` is a `#[repr(transparent)]` pointer.
    word_of(unsafe { std::mem::transmute::<LBig, *mut u8>(b) })
}

/// Release the big number an even word owns.
#[inline(always)]
unsafe fn release_word(w: u64) {
    if !is_small(w) {
        crate::rc_release(big_of_word(w));
    }
}

/// Take one more reference to the big number of an even word.
#[inline(always)]
unsafe fn retain_word(w: u64) {
    if !is_small(w) {
        forget(big_ref(&w).clone());
    }
}

// ---------------------------------------------------------------------------
// Nat handles

impl LNat {
    /// The word (the handle keeps its reference).
    #[inline(always)]
    pub fn word(&self) -> u64 {
        word_of(self.0)
    }

    /// The word, owning the handle's reference.
    #[inline(always)]
    pub fn into_raw(self) -> u64 {
        let w = self.word();
        forget(self);
        w
    }

    /// The handle of a word that owns its reference (or is small).
    #[inline(always)]
    pub unsafe fn from_raw(w: u64) -> LNat {
        LNat(ptr_of(w))
    }

    /// A value below 2^63.
    #[inline(always)]
    pub fn small(v: u64) -> LNat {
        debug_assert!(v >> 63 == 0);
        LNat(ptr_of((v << 1) | 1))
    }

    #[inline(always)]
    pub fn of_u64(v: u64) -> LNat {
        if v >> 63 == 0 {
            LNat::small(v)
        } else {
            nat_big_of_u64(v)
        }
    }

    /// A big number as a `Nat` (normalized: small below 2^63).
    #[inline]
    pub fn of_big(b: LBig) -> LNat {
        debug_assert!(!big::is_neg(&b));
        if big::limbs(&b).len() <= 1 {
            let v = big::low_limb(&b);
            if v >> 63 == 0 {
                crate::rc_release(b);
                return LNat::small(v);
            }
        }
        LNat(ptr_of(word_of_big(b)))
    }

    /// The value modulo 2^64 (the handle keeps its reference).
    #[inline(always)]
    pub fn low_u64(&self) -> u64 {
        let w = self.word();
        if is_small(w) { w >> 1 } else { big::low_limb(unsafe { big_ref(&w) }) }
    }
}

impl Drop for LNat {
    #[inline(always)]
    fn drop(&mut self) {
        unsafe { release_word(self.word()) }
    }
}

impl Clone for LNat {
    #[inline(always)]
    fn clone(&self) -> LNat {
        unsafe { retain_word(self.word()) };
        LNat(self.0)
    }
}

/// A `Nat` of at least 2^63 from a word.
#[cold]
#[inline(never)]
pub extern "C" fn nat_big_of_u64(v: u64) -> LNat {
    LNat::of_big(big::of_u64(v))
}

/// The rules' view of a `Nat` word: its value, or the big number it owns.
#[inline(always)]
unsafe fn nat_view(w: u64) -> sem::nat::Nat<GNat> {
    if is_small(w) { sem::nat::Nat::Small(w >> 1) } else { sem::nat::Nat::Big(GNat(big_of_word(w))) }
}

/// A `Nat` the rules computed, as a normalized handle.
#[inline]
fn of_nat_view(n: sem::nat::Nat<GNat>) -> LNat {
    match n {
        sem::nat::Nat::Small(v) => LNat::of_u64(v),
        sem::nat::Nat::Big(GNat(b)) => LNat::of_big(b),
    }
}

/// A rule's result, or the end of the process with its internal panic.
#[inline(always)]
fn ok<T>(r: Result<T, InternalPanic>) -> T {
    match r {
        Ok(v) => v,
        Err(p) => crate::lean_internal_panic(p),
    }
}

// The slow paths of the prelude's `lean_nat_*`: every one takes the raw
// words of its operands (owned) and handles all cases, the both-small one
// included.

#[inline(never)]
pub extern "C" fn nat_add(a: u64, b: u64) -> LNat {
    of_nat_view(ok(sem::nat::add(unsafe { nat_view(a) }, unsafe { nat_view(b) })))
}

#[inline(never)]
pub extern "C" fn nat_sub(a: u64, b: u64) -> LNat {
    of_nat_view(sem::nat::sub(unsafe { nat_view(a) }, unsafe { nat_view(b) }))
}

#[inline(never)]
pub extern "C" fn nat_mul(a: u64, b: u64) -> LNat {
    of_nat_view(ok(sem::nat::mul(unsafe { nat_view(a) }, unsafe { nat_view(b) })))
}

#[inline(never)]
pub extern "C" fn nat_div(a: u64, b: u64) -> LNat {
    of_nat_view(sem::nat::div(unsafe { nat_view(a) }, unsafe { nat_view(b) }))
}

#[inline(never)]
pub extern "C" fn nat_mod(a: u64, b: u64) -> LNat {
    of_nat_view(sem::nat::rem(unsafe { nat_view(a) }, unsafe { nat_view(b) }))
}

/// Three-way comparison: -1, 0, 1.
#[inline(never)]
pub extern "C" fn nat_cmp(a: u64, b: u64) -> i64 {
    let (x, y) = unsafe { (nat_view(a), nat_view(b)) };
    sem::nat::compare(&x, &y) as i64
}

#[inline(never)]
pub extern "C" fn nat_eq(a: u64, b: u64) -> bool {
    let (x, y) = unsafe { (nat_view(a), nat_view(b)) };
    sem::nat::dec_eq(&x, &y)
}

#[inline(never)]
pub extern "C" fn nat_land(a: u64, b: u64) -> LNat {
    of_nat_view(sem::nat::land(unsafe { nat_view(a) }, unsafe { nat_view(b) }))
}

#[inline(never)]
pub extern "C" fn nat_lor(a: u64, b: u64) -> LNat {
    of_nat_view(sem::nat::lor(unsafe { nat_view(a) }, unsafe { nat_view(b) }))
}

#[inline(never)]
pub extern "C" fn nat_xor(a: u64, b: u64) -> LNat {
    of_nat_view(sem::nat::lxor(unsafe { nat_view(a) }, unsafe { nat_view(b) }))
}

/// `Nat.shiftLeft`, for any shift (LB-12 lifted); a result above
/// `big::MAX_BITS` ends the process (`sem::nat::shiftl`).
#[inline(never)]
pub extern "C" fn nat_shiftl(a: u64, b: u64) -> LNat {
    of_nat_view(ok(sem::nat::shiftl(unsafe { nat_view(a) }, unsafe { nat_view(b) })))
}

/// `Nat.shiftRight`, for any shift (LB-04 lifted).
#[inline(never)]
pub extern "C" fn nat_shiftr(a: u64, b: u64) -> LNat {
    of_nat_view(sem::nat::shiftr(unsafe { nat_view(a) }, unsafe { nat_view(b) }))
}

#[inline(never)]
pub extern "C" fn nat_log2(a: u64) -> LNat {
    LNat::of_u64(sem::nat::log2(&unsafe { nat_view(a) }))
}

/// `Nat.pow`, for any exponent (LB-11 lifted); a result above
/// `big::MAX_BITS` ends the process (`sem::nat::pow`).
#[inline(never)]
pub extern "C" fn nat_pow(a: u64, b: u64) -> LNat {
    of_nat_view(ok(sem::nat::pow(unsafe { nat_view(a) }, unsafe { nat_view(b) })))
}

#[inline(never)]
pub extern "C" fn nat_gcd(a: u64, b: u64) -> LNat {
    of_nat_view(sem::nat::gcd(unsafe { nat_view(a) }, unsafe { nat_view(b) }))
}

/// Text that a `fmt::Write` produces (lean-runtime's text rules write into
/// one), collected for a string: ASCII here, the decimal digits of a big
/// number.
struct Digits(Vec<u8>);

impl std::fmt::Write for Digits {
    fn write_str(&mut self, s: &str) -> std::fmt::Result {
        self.0.extend_from_slice(s.as_bytes());
        Ok(())
    }
}

/// The decimal digits (and sign) of a big number as a string
/// (`sem::nat::write_decimal`, `sem::int::write_decimal`).
#[inline(never)]
fn big_decimal(write: impl FnOnce(&mut Digits) -> std::fmt::Result) -> crate::LStr {
    let mut d = Digits(Vec::new());
    if write(&mut d).is_err() {
        crate::lean_internal_panic(InternalPanic::OutOfMemory)
    }
    crate::string::from_vec(d.0)
}

/// `Nat.repr` (decimal); below 128 the shared strings of `Nat.reprArray`,
/// below 2^63 `string::of_u64` (lean-runtime's digits, on the stack).
#[inline(never)]
pub extern "C" fn nat_repr(a: u64) -> crate::LStr {
    match unsafe { nat_view(a) } {
        sem::nat::Nat::Small(x) if x < 128 => crate::string::repr_small(x),
        sem::nat::Nat::Small(x) => crate::string::of_u64(x),
        n => big_decimal(|d| sem::nat::write_decimal(&n, d)),
    }
}

/// A `Nat` from its decimal digits (big literals).
#[inline(never)]
pub fn nat_of_decimal(s: &[u8]) -> LNat {
    LNat::of_big(big::of_decimal(unsafe { std::str::from_utf8_unchecked(s) }))
}

/// A `Nat` size or offset as lean-runtime's array rules take it
/// (`sem::nat::Nat::to_u64_saturating`): the value, or `u64::MAX` for 2^64
/// or more. The big number the word owns is released.
#[inline(never)]
pub extern "C" fn nat_sat_u64(a: u64) -> u64 {
    unsafe { nat_view(a) }.to_u64_saturating()
}

/// `Array.replicate`'s size (`lean_mk_array`, `sem::array::replicate_len`):
/// the element count, or the end of the process for a size that is not a
/// word or whose array's byte size overflows.
#[inline(never)]
pub extern "C" fn nat_replicate_len(a: u64) -> u64 {
    ok(sem::array::replicate_len(unsafe { nat_view(a) }.to_u64())) as u64
}

/// The value modulo 2^64 (`UInt64.ofNat`, `USize.ofNat`, ...).
#[inline(never)]
pub extern "C" fn nat_low_u64(a: u64) -> u64 {
    unsafe { nat_view(a) }.low_u64()
}

/// `Int.ofNat` (`sem::int::of_nat`). A big `Nat` (>= 2^63) is a big `Int`
/// too: the same object.
#[inline(never)]
pub extern "C" fn nat_to_int(a: u64) -> LInt {
    of_int_view(sem::int::of_nat(unsafe { nat_view(a) }))
}

/// `Int.negSucc n = -(n + 1)`.
#[inline(never)]
pub extern "C" fn nat_neg_succ(a: u64) -> LInt {
    of_int_view(ok(sem::int::neg_succ_of_nat(unsafe { nat_view(a) })))
}

// ---------------------------------------------------------------------------
// Int handles

impl LInt {
    #[inline(always)]
    pub fn word(&self) -> u64 {
        word_of(self.0)
    }

    #[inline(always)]
    pub fn into_raw(self) -> u64 {
        let w = self.word();
        forget(self);
        w
    }

    #[inline(always)]
    pub unsafe fn from_raw(w: u64) -> LInt {
        LInt(ptr_of(w))
    }

    /// A value in [INT_MIN, INT_MAX]: `lean_box((unsigned)(int)v)`.
    #[inline(always)]
    pub fn small(v: i64) -> LInt {
        debug_assert!((INT_MIN..=INT_MAX).contains(&v));
        LInt(ptr_of(((v as i32 as u32 as u64) << 1) | 1))
    }

    #[inline(always)]
    pub fn of_i64(v: i64) -> LInt {
        if (INT_MIN..=INT_MAX).contains(&v) { LInt::small(v) } else { int_big_of_i64(v) }
    }

    /// A big number as an `Int` (normalized: small in [INT_MIN, INT_MAX]).
    /// The one place where a big `Int` handle is made: every big `Int` word
    /// is outside the small range (the prelude's `lean_int_dec_eq` answers
    /// a small and a big word unequal without a call).
    #[inline]
    pub fn of_big(b: LBig) -> LInt {
        // What the range test below needs (`fits_i64` reads the limb count):
        // checked in builds with debug assertions.
        debug_assert!(big_trimmed(&b), "a big number with a zero top limb or a negative zero");
        if big::fits_i64(&b) {
            let v = big::to_i64(&b);
            if (INT_MIN..=INT_MAX).contains(&v) {
                crate::rc_release(b);
                return LInt::small(v);
            }
        }
        LInt(ptr_of(word_of_big(b)))
    }
}

impl Drop for LInt {
    #[inline(always)]
    fn drop(&mut self) {
        unsafe { release_word(self.word()) }
    }
}

impl Clone for LInt {
    #[inline(always)]
    fn clone(&self) -> LInt {
        unsafe { retain_word(self.word()) };
        LInt(self.0)
    }
}

#[cold]
#[inline(never)]
pub extern "C" fn int_big_of_i64(v: i64) -> LInt {
    LInt::of_big(big::of_i64(v))
}

/// The value of a small `Int` word (`lean_scalar_to_int64`).
#[inline(always)]
pub fn int_of_small_word(w: u64) -> i64 {
    (w >> 1) as u32 as i32 as i64
}

/// Whether a big number is in its one form: no zero top limb, and a zero
/// never negative (`LBig::set` keeps it so; `fits_i64` and the range test
/// of `LInt::of_big` rely on it).
#[inline]
fn big_trimmed(b: &LBig) -> bool {
    big::limbs(b).last() != Some(&0) && !(big::limbs(b).is_empty() && big::is_neg(b))
}

/// Whether a big number is outside the small `Int` range, as the big
/// number of every `Int` word is (`LInt::of_big`).
#[inline]
fn big_int_normalized(b: &LBig) -> bool {
    !(big::fits_i64(b) && (INT_MIN..=INT_MAX).contains(&big::to_i64(b)))
}

/// The rules' view of an `Int` word: its value, or the big number it owns.
/// Every big `Int` that a slow path computes with or compares comes
/// through here: checked to be normalized in builds with debug assertions.
#[inline(always)]
unsafe fn int_view(w: u64) -> sem::int::Int<GInt> {
    if is_small(w) {
        sem::int::Int::Small(int_of_small_word(w))
    } else {
        debug_assert!(big_trimmed(big_ref(&w)), "a big Int with a zero top limb or a negative zero");
        debug_assert!(big_int_normalized(big_ref(&w)), "a big Int in the small range");
        sem::int::Int::Big(GInt(big_of_word(w)))
    }
}

/// `int_view` for the slow paths of the arithmetic and the comparisons: a
/// big number whose value is in the `i64` range is released and viewed as
/// a word (`Small`). lean2rr's big `Int`s are the values outside the
/// `int32` range, most of them of one limb: with both operands words, the
/// rule computes on its word path (`sem::int`'s `*_small` helpers, exact in
/// `i128`), without the big-number path (the size test, the word methods,
/// a block per operand), and the result is normalized once
/// (`of_int_view`). A rule takes either form for any value
/// (`sem::int::Int`), so the result is the same.
#[inline(always)]
unsafe fn int_view_narrow(w: u64) -> sem::int::Int<GInt> {
    match int_view(w) {
        sem::int::Int::Big(GInt(b)) if big::fits_i64(&b) => {
            let v = big::to_i64(&b);
            crate::rc_release(b);
            sem::int::Int::Small(v)
        }
        i => i,
    }
}

/// An `Int` the rules computed, as a normalized handle.
#[inline]
fn of_int_view(i: sem::int::Int<GInt>) -> LInt {
    match i {
        sem::int::Int::Small(v) => LInt::of_i64(v),
        sem::int::Int::Big(GInt(b)) => LInt::of_big(b),
    }
}

// The slow paths of the prelude's `lean_int_*` (raw owned words, all cases).

#[inline(never)]
pub extern "C" fn int_neg(a: u64) -> LInt {
    of_int_view(sem::int::neg(unsafe { int_view(a) }))
}

#[inline(never)]
pub extern "C" fn int_add(a: u64, b: u64) -> LInt {
    of_int_view(ok(sem::int::add(unsafe { int_view_narrow(a) }, unsafe { int_view_narrow(b) })))
}

#[inline(never)]
pub extern "C" fn int_sub(a: u64, b: u64) -> LInt {
    of_int_view(ok(sem::int::sub(unsafe { int_view_narrow(a) }, unsafe { int_view_narrow(b) })))
}

#[inline(never)]
pub extern "C" fn int_mul(a: u64, b: u64) -> LInt {
    of_int_view(ok(sem::int::mul(unsafe { int_view_narrow(a) }, unsafe { int_view_narrow(b) })))
}

/// `Int.div` (T-division, C's `/`).
#[inline(never)]
pub extern "C" fn int_div(a: u64, b: u64) -> LInt {
    of_int_view(sem::int::tdiv(unsafe { int_view_narrow(a) }, unsafe { int_view_narrow(b) }))
}

/// `Int.mod` (T-remainder, C's `%`, sign of the dividend).
#[inline(never)]
pub extern "C" fn int_mod(a: u64, b: u64) -> LInt {
    of_int_view(sem::int::tmod(unsafe { int_view_narrow(a) }, unsafe { int_view_narrow(b) }))
}

/// `Int.ediv` (Euclidean).
#[inline(never)]
pub extern "C" fn int_ediv(a: u64, b: u64) -> LInt {
    of_int_view(sem::int::ediv(unsafe { int_view_narrow(a) }, unsafe { int_view_narrow(b) }))
}

/// `Int.emod` (Euclidean, never negative for `y != 0`).
#[inline(never)]
pub extern "C" fn int_emod(a: u64, b: u64) -> LInt {
    of_int_view(sem::int::emod(unsafe { int_view_narrow(a) }, unsafe { int_view_narrow(b) }))
}

/// Three-way comparison: -1, 0, 1.
#[inline(never)]
pub extern "C" fn int_cmp(a: u64, b: u64) -> i64 {
    let (x, y) = unsafe { (int_view_narrow(a), int_view_narrow(b)) };
    sem::int::compare(&x, &y) as i64
}

#[inline(never)]
pub extern "C" fn int_eq(a: u64, b: u64) -> bool {
    let (x, y) = unsafe { (int_view_narrow(a), int_view_narrow(b)) };
    sem::int::dec_eq(&x, &y)
}

/// `Int.natAbs`.
#[inline(never)]
pub extern "C" fn int_nat_abs(a: u64) -> LNat {
    of_nat_view(sem::int::nat_abs(unsafe { int_view_narrow(a) }))
}

/// Whether an `Int` is negative (`!Int.decNonneg`).
#[inline(never)]
pub extern "C" fn int_is_neg(a: u64) -> bool {
    !sem::int::dec_nonneg(&unsafe { int_view(a) })
}

/// The value modulo 2^64 in two's complement (`Int64.ofInt`, ...).
#[inline(never)]
pub extern "C" fn int_low_twos(a: u64) -> u64 {
    unsafe { int_view(a) }.low_u64()
}

/// `Int.repr` (decimal); `Int.repr (ofNat m) = Nat.repr m`, shared below
/// 128.
#[inline(never)]
pub extern "C" fn int_repr(a: u64) -> crate::LStr {
    match unsafe { int_view(a) } {
        sem::int::Int::Small(x) if (0..128).contains(&x) => crate::string::repr_small(x as u64),
        sem::int::Int::Small(x) => crate::string::of_i64(x),
        i => big_decimal(|d| sem::int::write_decimal(&i, d)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn n(v: u128) -> LNat {
        if v >> 64 == 0 {
            LNat::of_u64(v as u64)
        } else {
            LNat::of_big(big::of_limbs2(v as u64, (v >> 64) as u64))
        }
    }

    fn val(x: &LNat) -> u128 {
        let w = x.word();
        if is_small(w) {
            (w >> 1) as u128
        } else {
            let b = unsafe { big_ref(&w) };
            assert!(big::limbs(b).len() <= 2);
            big::limbs(b).iter().rev().fold(0u128, |acc, &l| (acc << 64) | l as u128)
        }
    }

    fn canonical(x: &LNat) -> bool {
        is_small(x.word()) == (val(x) >> 63 == 0)
    }

    #[test]
    fn boundaries() {
        let edges: [u128; 10] = [0, 1, (1 << 62) - 1, 1 << 62, (1 << 63) - 1, 1 << 63, (1 << 63) + 1, (1 << 64) - 1, 1 << 64, (1 << 64) + 5];
        for &a in &edges {
            for &b in &edges {
                let add = nat_add(n(a).into_raw(), n(b).into_raw());
                assert_eq!(val(&add), a + b);
                assert!(canonical(&add));
                let sub = nat_sub(n(a).into_raw(), n(b).into_raw());
                assert_eq!(val(&sub), a.saturating_sub(b));
                assert!(canonical(&sub));
                if a.checked_mul(b).is_some_and(|p| p >> 127 == 0) {
                    let mul = nat_mul(n(a).into_raw(), n(b).into_raw());
                    assert_eq!(val(&mul), a * b, "{a} * {b}");
                    assert!(canonical(&mul));
                }
                let div = nat_div(n(a).into_raw(), n(b).into_raw());
                assert_eq!(val(&div), if b == 0 { 0 } else { a / b });
                assert!(canonical(&div));
                let md = nat_mod(n(a).into_raw(), n(b).into_raw());
                assert_eq!(val(&md), if b == 0 { a } else { a % b });
                assert!(canonical(&md));
                assert_eq!(nat_eq(n(a).into_raw(), n(b).into_raw()), a == b);
                assert_eq!(nat_cmp(n(a).into_raw(), n(b).into_raw()), (a > b) as i64 - (a < b) as i64);
                assert_eq!(val(&nat_land(n(a).into_raw(), n(b).into_raw())), a & b);
                assert_eq!(val(&nat_lor(n(a).into_raw(), n(b).into_raw())), a | b);
                assert_eq!(val(&nat_xor(n(a).into_raw(), n(b).into_raw())), a ^ b);
                assert!(canonical(&nat_xor(n(a).into_raw(), n(b).into_raw())));
            }
        }
    }

    /// Powers of a power of two (lean-runtime's `nat::pow` shifts them) and
    /// of other words against GMP's `mpz_pow_ui`.
    #[test]
    fn pow_of_two() {
        for x in [2u64, 3, 4, 8, 10, 1 << 31, (1 << 31) + 1, 1 << 62] {
            for e in [1u64, 2, 31, 32, 62, 63, 64, 65, 100, 1000] {
                let p = nat_pow(LNat::small(x).into_raw(), LNat::small(e).into_raw());
                let r = LNat::of_big(big::nat_pow(big::of_u64(x), e));
                assert!(nat_eq(p.clone().into_raw(), r.clone().into_raw()), "{x} ^ {e}");
                assert_eq!(is_small(p.word()), is_small(r.word()));
            }
        }
    }

    /// Lean's limits that lean-runtime's rules lift (LB-04, LB-11, LB-12)
    /// where the result is small, and the size helpers of the array rules.
    #[test]
    fn lifted_limits() {
        let two64 = || n(1 << 64);
        let big = |v: u128| n(v).into_raw();
        let small = |v: u64| LNat::of_u64(v).into_raw();
        // LB-11: bases 0 and 1 for any exponent
        assert_eq!(val(&nat_pow(small(1), small(1 << 32))), 1);
        assert_eq!(val(&nat_pow(small(0), small(1 << 32))), 0);
        assert_eq!(val(&nat_pow(small(1), two64().into_raw())), 1);
        assert_eq!(val(&nat_pow(small(0), two64().into_raw())), 0);
        assert_eq!(val(&nat_pow(two64().into_raw(), small(0))), 1);
        // LB-12: zero for any shift
        assert_eq!(val(&nat_shiftl(small(0), two64().into_raw())), 0);
        assert_eq!(val(&nat_shiftl(small(0), small(1 << 40))), 0);
        // LB-04: a big shift amount, and a shift past the bits of a big value
        assert_eq!(val(&nat_shiftr(big((1 << 100) + 3), small(1 << 40))), 0);
        assert_eq!(val(&nat_shiftr(big((1 << 100) + 3), two64().into_raw())), 0);
        assert_eq!(val(&nat_shiftr(big((1 << 100) + 3), small(99))), 2);
        // sizes and offsets for the array rules
        assert_eq!(nat_sat_u64(small(7)), 7);
        assert_eq!(nat_sat_u64(big(1 << 63)), 1 << 63);
        assert_eq!(nat_sat_u64(big((1 << 64) - 1)), u64::MAX);
        assert_eq!(nat_sat_u64(two64().into_raw()), u64::MAX);
        assert_eq!(nat_replicate_len(small(5)), 5);
        // `Nat.log2` and `gcd` of a big and a small value
        assert_eq!(val(&nat_log2(big(1 << 100))), 100);
        assert_eq!(val(&nat_gcd(big(3 << 70), small(12))), 12);
        assert_eq!(val(&nat_gcd(small(0), big(1 << 70))), 1 << 70);
        // the text of numbers
        let text = |s: crate::LStr| String::from_utf8(crate::string::bytes(&s).to_vec()).unwrap();
        assert_eq!(text(nat_repr(small(5))), "5");
        assert_eq!(text(nat_repr(small(1234567))), "1234567");
        assert_eq!(text(nat_repr(big(1 << 64))), "18446744073709551616");
        let int = |v: i128| LInt::of_big(<GInt as lean_runtime::semantics::bignum::BigInt>::from_i128(v).0).into_raw();
        assert_eq!(text(int_repr(int(-7))), "-7");
        assert_eq!(text(int_repr(int(i32::MIN as i128))), "-2147483648");
        assert_eq!(text(int_repr(int(-(1 << 64)))), "-18446744073709551616");
        assert_eq!(text(int_repr(int(100))), "100");
    }

    #[test]
    fn counts() {
        let b = big::of_limbs2(3, 3);
        let x = LNat::of_big(b.clone());
        assert_eq!(b.count(), 2);
        let y = x.clone();
        assert_eq!(b.count(), 3);
        drop(x);
        drop(y);
        assert_eq!(b.count(), 1);
        // A slow path consumes its operands.
        let s = nat_add(LNat::of_big(b.clone()).into_raw(), LNat::small(1).into_raw());
        drop(s);
        assert_eq!(b.count(), 1);
        let i = nat_to_int(LNat::of_big(b.clone()).into_raw());
        assert_eq!(b.count(), 2);
        drop(i);
        assert_eq!(b.count(), 1);
    }

    #[test]
    fn ints() {
        let edges: [i128; 13] = [0, 1, -1, INT_MAX as i128, INT_MIN as i128, INT_MAX as i128 + 1, INT_MIN as i128 - 1,
            1 << 62, -(1 << 62), i64::MIN as i128, i64::MAX as i128, 46341, -46341];
        let i = |v: i128| LInt::of_big(<GInt as lean_runtime::semantics::bignum::BigInt>::from_i128(v).0);
        let ival = |x: &LInt| -> i128 {
            let w = x.word();
            if is_small(w) {
                int_of_small_word(w) as i128
            } else {
                let b = unsafe { big_ref(&w) };
                let m = big::limbs(b).iter().rev().fold(0i128, |acc, &l| (acc << 64) | l as i128);
                if big::is_neg(b) { -m } else { m }
            }
        };
        for &a in &edges {
            for &b in &edges {
                let s = int_add(i(a).into_raw(), i(b).into_raw());
                assert_eq!(ival(&s), a + b);
                assert_eq!(is_small(s.word()), (INT_MIN as i128..=INT_MAX as i128).contains(&(a + b)));
                assert_eq!(ival(&int_sub(i(a).into_raw(), i(b).into_raw())), a - b);
                assert_eq!(ival(&int_mul(i(a).into_raw(), i(b).into_raw())), a * b);
                assert_eq!(int_eq(i(a).into_raw(), i(b).into_raw()), a == b);
                assert_eq!(int_cmp(i(a).into_raw(), i(b).into_raw()), (a > b) as i64 - (a < b) as i64);
                if b != 0 {
                    assert_eq!(ival(&int_div(i(a).into_raw(), i(b).into_raw())), a / b);
                    assert_eq!(ival(&int_mod(i(a).into_raw(), i(b).into_raw())), a % b);
                    assert_eq!(ival(&int_emod(i(a).into_raw(), i(b).into_raw())), a.rem_euclid(b));
                    assert_eq!(ival(&int_ediv(i(a).into_raw(), i(b).into_raw())), a.div_euclid(b));
                }
            }
        }
    }
    /// Every `Int` slow path returns a normalized word, small exactly in
    /// the `int32` range, on operands and results at the range's edges and
    /// beyond `i64` (the prelude's `lean_int_dec_eq` relies on it: a small
    /// and a big word are never equal).
    #[test]
    fn int_results_are_normalized() {
        let (lo, hi) = (INT_MIN as i128, INT_MAX as i128);
        let edges: [i128; 18] = [0, 1, -1, 2, -2, hi, lo, hi + 1, lo - 1, hi - 1, lo + 1, 1 << 32, -(1 << 32),
            i64::MIN as i128, i64::MAX as i128, i64::MAX as i128 + 1, 1 << 64, -(1 << 64)];
        let i = |v: i128| LInt::of_big(<GInt as lean_runtime::semantics::bignum::BigInt>::from_i128(v).0);
        let ival = |x: &LInt| -> i128 {
            let w = x.word();
            if is_small(w) {
                int_of_small_word(w) as i128
            } else {
                let b = unsafe { big_ref(&w) };
                let m = big::limbs(b).iter().rev().fold(0i128, |acc, &l| (acc << 64) | l as i128);
                if big::is_neg(b) { -m } else { m }
            }
        };
        let check = |x: LInt, want: i128, what: &str| {
            assert_eq!(ival(&x), want, "{what}");
            assert_eq!(is_small(x.word()), (lo..=hi).contains(&want), "{what}: not normalized");
        };
        for &a in &edges {
            check(i(a), a, "of_big");
            check(int_neg(i(a).into_raw()), -a, "neg");
            if let Ok(v) = i64::try_from(a) {
                check(LInt::of_i64(v), a, "of_i64");
            }
            for &b in &edges {
                let s = format!("{a} {b}");
                check(int_add(i(a).into_raw(), i(b).into_raw()), a + b, &s);
                check(int_sub(i(a).into_raw(), i(b).into_raw()), a - b, &s);
                if a.unsigned_abs().leading_zeros() + b.unsigned_abs().leading_zeros() > 128 {
                    check(int_mul(i(a).into_raw(), i(b).into_raw()), a * b, &s);
                }
                let (q, r, eq, er) = if b == 0 { (0, a, 0, a) } else { (a / b, a % b, a.div_euclid(b), a.rem_euclid(b)) };
                check(int_div(i(a).into_raw(), i(b).into_raw()), q, &s);
                check(int_mod(i(a).into_raw(), i(b).into_raw()), r, &s);
                check(int_ediv(i(a).into_raw(), i(b).into_raw()), eq, &s);
                check(int_emod(i(a).into_raw(), i(b).into_raw()), er, &s);
                assert_eq!(int_eq(i(a).into_raw(), i(b).into_raw()), a == b, "{s}");
            }
        }
        // `Int.ofNat` and `Int.negSucc` of `Nat`s at the small `Int` and the
        // small `Nat` edges.
        for &m in &[0u128, 1, (1 << 31) - 1, 1 << 31, (1 << 31) + 1, 1 << 32, (1 << 63) - 1, 1 << 63, 1 << 64] {
            check(nat_to_int(n(m).into_raw()), m as i128, "ofNat");
            check(nat_neg_succ(n(m).into_raw()), -(m as i128) - 1, "negSucc");
        }
    }
    /// The arithmetic slow paths view a big operand in the `i64` range as a
    /// word (`int_view_narrow`): exact, normalized results with unique
    /// operands, shared ones (a shared operand keeps its value and gives up
    /// the one reference the call took) and one block as both operands, at
    /// the edges of the `int32` and `i64` ranges, beyond `i64` and beyond
    /// two limbs; every product that fits `i128` (`i64::MIN * -1`,
    /// `i64::MIN^2`, ...); the divisions against Lean's definitions on
    /// magnitudes, a zero divisor included; and `Int.natAbs` at the same
    /// edges (review RS12-02).
    #[test]
    fn narrowed_operands() {
        let (lo, hi) = (INT_MIN as i128, INT_MAX as i128);
        let (m, mx) = (i64::MIN as i128, i64::MAX as i128);
        let edges: [i128; 31] = [0, 1, -1, 2, -2, 7, -7, hi, lo, hi + 1, lo - 1, hi + 2, lo - 2, 1 << 32, -(1 << 32),
            1 << 40, -(1 << 40) - 1, mx, m, mx - 1, m + 1, mx + 1, m - 1, mx + 2, m - 2, 1 << 64, -(1 << 64),
            (1 << 64) + 1, -(1 << 64) - 3, 1 << 100, -(1 << 100) + 5];
        // `Int.tdiv`, `Int.tmod`, `Int.ediv` (`/`) and `Int.emod` (`%`) of
        // Lean 4.34, by cases on the signs, on magnitudes (`Nat`).
        fn tdiv(a: i128, b: i128) -> i128 {
            if b == 0 {
                return 0;
            }
            let q = (a.unsigned_abs() / b.unsigned_abs()) as i128;
            if (a < 0) != (b < 0) { -q } else { q }
        }
        fn tmod(a: i128, b: i128) -> i128 {
            if b == 0 {
                return a;
            }
            let r = (a.unsigned_abs() % b.unsigned_abs()) as i128;
            if a < 0 { -r } else { r }
        }
        fn ediv(a: i128, b: i128) -> i128 {
            let (ua, ub) = (a.unsigned_abs(), b.unsigned_abs());
            if b == 0 {
                0
            } else if a >= 0 {
                if b > 0 { (ua / ub) as i128 } else { -((ua / ub) as i128) }
            } else if b > 0 {
                -(((ua - 1) / ub) as i128 + 1)
            } else {
                ((ua - 1) / ub) as i128 + 1
            }
        }
        fn emod(a: i128, b: i128) -> i128 {
            let (ua, ub) = (a.unsigned_abs(), b.unsigned_abs());
            if ub == 0 {
                a
            } else if a >= 0 {
                (ua % ub) as i128
            } else {
                ub as i128 - (((ua - 1) % ub) as i128 + 1)
            }
        }
        let i = |v: i128| LInt::of_big(<GInt as lean_runtime::semantics::bignum::BigInt>::from_i128(v).0);
        let ival = |x: &LInt| -> i128 {
            let w = x.word();
            if is_small(w) {
                int_of_small_word(w) as i128
            } else {
                let b = unsafe { big_ref(&w) };
                let mg = big::limbs(b).iter().rev().fold(0i128, |acc, &l| (acc << 64) | l as i128);
                // -2^127 (a product of the edges) has the magnitude i128::MIN
                if big::is_neg(b) { mg.wrapping_neg() } else { mg }
            }
        };
        let count = |x: &LInt| if is_small(x.word()) { 1 } else { unsafe { big_ref(&x.word()) }.count() };
        let check = |r: LInt, want: i128, what: &str| {
            assert_eq!(ival(&r), want, "{what}");
            assert_eq!(is_small(r.word()), (lo..=hi).contains(&want), "{what}: not normalized");
        };
        let mut products = 0;
        for &a in &edges {
            for &b in &edges {
                let (x, y) = (i(a), i(b));
                // 0: fresh unique operands; 1: shared ones; 2: one shared
                // block as both operands (`a = b`).
                for mode in 0..3 {
                    if mode == 2 && a != b {
                        continue;
                    }
                    let s = format!("{a} {b} mode={mode}");
                    let args = || match mode {
                        0 => (i(a).into_raw(), i(b).into_raw()),
                        1 => (x.clone().into_raw(), y.clone().into_raw()),
                        _ => (x.clone().into_raw(), x.clone().into_raw()),
                    };
                    let (p, q) = args();
                    check(int_add(p, q), a + b, &s);
                    let (p, q) = args();
                    check(int_sub(p, q), a - b, &s);
                    if let Some(pr) = a.checked_mul(b) {
                        let (p, q) = args();
                        check(int_mul(p, q), pr, &s);
                        products += 1;
                    }
                    let (p, q) = args();
                    check(int_div(p, q), tdiv(a, b), &s);
                    let (p, q) = args();
                    check(int_mod(p, q), tmod(a, b), &s);
                    let (p, q) = args();
                    check(int_ediv(p, q), ediv(a, b), &s);
                    let (p, q) = args();
                    check(int_emod(p, q), emod(a, b), &s);
                    let (p, q) = args();
                    assert_eq!(int_eq(p, q), a == b, "{s}");
                    let (p, q) = args();
                    assert_eq!(int_cmp(p, q), (a > b) as i64 - (a < b) as i64, "{s}");
                    assert_eq!((ival(&x), ival(&y), count(&x), count(&y)), (a, b, 1, 1), "{s}: the operands changed");
                }
            }
            let r = int_nat_abs(i(a).into_raw());
            assert_eq!(val(&r), a.unsigned_abs(), "natAbs {a}");
            assert!(canonical(&r), "natAbs {a}: not normalized");
            let x = i(a);
            let r = int_nat_abs(x.clone().into_raw());
            let v = val(&r);
            drop(r); // a big result may be the operand's block
            assert_eq!((v, ival(&x), count(&x)), (a.unsigned_abs(), a, 1), "natAbs {a} shared");
        }
        // Every product of two edges below 2^127 in magnitude was checked.
        assert!(products > 900, "{products}");
    }
    /// A big `Int` in the small range (never made: `of_big` normalizes) is
    /// caught where a slow path reads it, in builds with debug assertions.
    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "a big Int in the small range")]
    fn unnormalized_big_int_is_caught() {
        let w = word_of_big(big::of_i64(5));
        drop(unsafe { int_view(w) });
    }
}
