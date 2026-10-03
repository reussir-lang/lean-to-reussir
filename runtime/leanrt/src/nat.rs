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
//! - an even word is an owned reference to a big number (`LBig`, the raw
//!   `Rc` pointer, laid out as Lean's `lean_mpz_object`, see `big`): a
//!   `Nat` of at least 2^63, an `Int` outside the `int32` range.
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
//! (`u64`, as the prelude passes them) and return normalized handles.
//! Semantics follow Lean's runtime (`lean.h`, `src/runtime/object.cpp`).

use crate::big::{self, LBig};
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
    // `Rc` is a `#[repr(transparent)]` pointer.
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

/// A big `Nat` operand or result: small value or big number, owned.
enum N {
    S(u64),
    B(LBig),
}

#[inline(always)]
unsafe fn take(w: u64) -> N {
    if is_small(w) { N::S(w >> 1) } else { N::B(big_of_word(w)) }
}

fn to_big(n: N) -> LBig {
    match n {
        N::S(x) => big::of_u64(x),
        N::B(b) => b,
    }
}

/// `x * y` of two words, normalized.
fn mul_wide(x: u64, y: u64) -> LNat {
    let p = (x as u128) * (y as u128);
    if p >> 63 == 0 { LNat::small(p as u64) } else { LNat::of_big(big::of_limbs2(p as u64, (p >> 64) as u64)) }
}

#[cold]
#[inline(never)]
fn panic_code(code: u64) -> ! {
    crate::internal_panic(match code {
        1 => "Nat.pow exponent is too big",
        2 => "Nat.shiftl exponent is too big",
        3 => "Nat.shiftr exponent is too big",
        _ => "internal error",
    })
}

// The slow paths of the prelude's `lean_nat_*`: every one takes the raw
// words of its operands (owned) and handles all cases, the both-small one
// included.

#[inline(never)]
pub extern "C" fn nat_add(a: u64, b: u64) -> LNat {
    match unsafe { (take(a), take(b)) } {
        // x, y < 2^63: the sum fits a word.
        (N::S(x), N::S(y)) => LNat::of_u64(x + y),
        (N::S(x), N::B(y)) | (N::B(y), N::S(x)) => LNat::of_big(big::nat_add_u64(y, x)),
        (N::B(x), N::B(y)) => LNat::of_big(big::nat_add(x, y)),
    }
}

#[inline(never)]
pub extern "C" fn nat_sub(a: u64, b: u64) -> LNat {
    match unsafe { (take(a), take(b)) } {
        (N::S(x), N::S(y)) => LNat::small(x.saturating_sub(y)),
        // A small value is below every big one.
        (N::S(_), N::B(y)) => {
            drop(y);
            LNat::small(0)
        }
        (N::B(x), N::S(y)) => LNat::of_big(big::nat_sub_u64(x, y)),
        (N::B(x), N::B(y)) => LNat::of_big(big::nat_sub(x, y)),
    }
}

#[inline(never)]
pub extern "C" fn nat_mul(a: u64, b: u64) -> LNat {
    match unsafe { (take(a), take(b)) } {
        (N::S(x), N::S(y)) => mul_wide(x, y),
        (N::S(x), N::B(y)) | (N::B(y), N::S(x)) => {
            if x == 0 {
                drop(y);
                LNat::small(0)
            } else {
                LNat::of_big(big::nat_mul_u64(y, x))
            }
        }
        (N::B(x), N::B(y)) => LNat::of_big(big::nat_mul(x, y)),
    }
}

/// `a / b`, `a / 0 = 0`.
#[inline(never)]
pub extern "C" fn nat_div(a: u64, b: u64) -> LNat {
    match unsafe { (take(a), take(b)) } {
        (N::S(x), N::S(y)) => LNat::small(if y == 0 { 0 } else { x / y }),
        (N::S(_), N::B(y)) => {
            drop(y);
            LNat::small(0)
        }
        (N::B(x), N::S(y)) => {
            if y == 0 {
                drop(x);
                LNat::small(0)
            } else {
                LNat::of_big(big::nat_div_u64(x, y))
            }
        }
        (N::B(x), N::B(y)) => LNat::of_big(big::nat_div(x, y)),
    }
}

/// `a % b`, `a % 0 = a`.
#[inline(never)]
pub extern "C" fn nat_mod(a: u64, b: u64) -> LNat {
    match unsafe { (take(a), take(b)) } {
        (N::S(x), N::S(y)) => LNat::small(if y == 0 { x } else { x % y }),
        (N::S(x), N::B(y)) => {
            drop(y);
            LNat::small(x)
        }
        (N::B(x), N::S(y)) => {
            if y == 0 {
                LNat::of_big(x)
            } else {
                let r = big::nat_mod_u64(x, y);
                LNat::small(r)
            }
        }
        (N::B(x), N::B(y)) => LNat::of_big(big::nat_mod(x, y)),
    }
}

/// Three-way comparison: -1, 0, 1.
#[inline(never)]
pub extern "C" fn nat_cmp(a: u64, b: u64) -> i64 {
    match unsafe { (take(a), take(b)) } {
        (N::S(x), N::S(y)) => (x > y) as i64 - (x < y) as i64,
        (N::S(_), N::B(y)) => {
            drop(y);
            -1
        }
        (N::B(x), N::S(_)) => {
            drop(x);
            1
        }
        (N::B(x), N::B(y)) => big::nat_cmp(x, y),
    }
}

#[inline(never)]
pub extern "C" fn nat_eq(a: u64, b: u64) -> bool {
    match unsafe { (take(a), take(b)) } {
        (N::S(x), N::S(y)) => x == y,
        (N::B(x), N::B(y)) => big::nat_eq(x, y),
        (x, y) => {
            drop((x, y));
            false
        }
    }
}

#[inline(never)]
pub extern "C" fn nat_land(a: u64, b: u64) -> LNat {
    match unsafe { (take(a), take(b)) } {
        (N::S(x), N::S(y)) => LNat::small(x & y),
        (N::S(x), N::B(y)) | (N::B(y), N::S(x)) => LNat::small(big::nat_land_u64(y, x)),
        (N::B(x), N::B(y)) => LNat::of_big(big::nat_land(x, y)),
    }
}

#[inline(never)]
pub extern "C" fn nat_lor(a: u64, b: u64) -> LNat {
    match unsafe { (take(a), take(b)) } {
        (N::S(x), N::S(y)) => LNat::small(x | y),
        (N::S(x), N::B(y)) | (N::B(y), N::S(x)) => LNat::of_big(big::nat_lor_u64(y, x)),
        (N::B(x), N::B(y)) => LNat::of_big(big::nat_lor(x, y)),
    }
}

#[inline(never)]
pub extern "C" fn nat_xor(a: u64, b: u64) -> LNat {
    match unsafe { (take(a), take(b)) } {
        (N::S(x), N::S(y)) => LNat::small(x ^ y),
        (N::S(x), N::B(y)) | (N::B(y), N::S(x)) => LNat::of_big(big::nat_xor_u64(y, x)),
        (N::B(x), N::B(y)) => LNat::of_big(big::nat_xor(x, y)),
    }
}

/// `Nat.shiftLeft`: 0 stays 0; otherwise a shift amount above 2^32 - 1 (a
/// big one included) is an internal panic (`lean_nat_shiftl`).
#[inline(never)]
pub extern "C" fn nat_shiftl(a: u64, b: u64) -> LNat {
    match unsafe { (take(a), take(b)) } {
        (N::S(0), b) => {
            drop(b);
            LNat::small(0)
        }
        (_, N::B(_)) => panic_code(2),
        (a, N::S(s)) => {
            if s > u32::MAX as u64 {
                panic_code(2)
            }
            match a {
                N::S(x) if s < 63 && (x << s) >> s == x && (x << s) >> 63 == 0 => LNat::small(x << s),
                a => LNat::of_big(big::nat_shl(to_big(a), s)),
            }
        }
    }
}

/// `Nat.shiftRight`: a big shift amount gives 0; a big value shifted by
/// more than 2^32 - 1 panics unless every bit is shifted out
/// (`lean_nat_big_shiftr`).
#[inline(never)]
pub extern "C" fn nat_shiftr(a: u64, b: u64) -> LNat {
    match unsafe { (take(a), take(b)) } {
        (N::S(x), N::S(s)) => LNat::small(if s < 64 { x >> s } else { 0 }),
        (a, N::B(s)) => {
            drop((a, s));
            LNat::small(0)
        }
        (N::B(x), N::S(s)) => {
            if s > u32::MAX as u64 {
                if big::nat_log2(x) >= s { panic_code(3) } else { LNat::small(0) }
            } else {
                LNat::of_big(big::nat_shr(x, s))
            }
        }
    }
}

#[inline(never)]
pub extern "C" fn nat_log2(a: u64) -> LNat {
    match unsafe { take(a) } {
        N::S(x) => LNat::small(if x == 0 { 0 } else { 63 - x.leading_zeros() as u64 }),
        N::B(x) => LNat::small(big::nat_log2(x)),
    }
}

/// `Nat.pow`: an exponent above 2^32 - 1 is an internal panic, whatever the
/// base (`lean_nat_pow`).
#[inline(never)]
pub extern "C" fn nat_pow(a: u64, b: u64) -> LNat {
    let e = match unsafe { take(b) } {
        N::S(e) if e <= u32::MAX as u64 => e,
        _ => panic_code(1),
    };
    if e == 0 {
        unsafe { release_word(a) };
        return LNat::small(1);
    }
    match unsafe { take(a) } {
        N::S(x) if x < 2 => LNat::small(x),
        N::S(x) => match x.checked_pow(e.min(64) as u32) {
            Some(r) if e < 64 => LNat::of_u64(r),
            _ => LNat::of_big(big::nat_pow(big::of_u64(x), e)),
        },
        N::B(x) => LNat::of_big(big::nat_pow(x, e)),
    }
}

fn gcd_u64(mut x: u64, mut y: u64) -> u64 {
    while y != 0 {
        let r = x % y;
        x = y;
        y = r;
    }
    x
}

#[inline(never)]
pub extern "C" fn nat_gcd(a: u64, b: u64) -> LNat {
    match unsafe { (take(a), take(b)) } {
        (N::S(x), N::S(y)) => LNat::small(gcd_u64(x, y)),
        (N::S(0), N::B(y)) | (N::B(y), N::S(0)) => LNat::of_big(y),
        (N::S(x), N::B(y)) | (N::B(y), N::S(x)) => LNat::small(gcd_u64(x, big::nat_mod_u64(y, x))),
        (N::B(x), N::B(y)) => LNat::of_big(big::nat_gcd(x, y)),
    }
}

/// `Nat.repr` (decimal); below 128 the shared strings of `Nat.reprArray`.
#[inline(never)]
pub extern "C" fn nat_repr(a: u64) -> crate::LStr {
    match unsafe { take(a) } {
        N::S(x) if x < 128 => crate::string::repr_small(x),
        N::S(x) => crate::string::of_u64(x),
        N::B(x) => crate::string::from_vec(big::to_decimal(&x)),
    }
}

/// A `Nat` from its decimal digits (big literals).
#[inline(never)]
pub fn nat_of_decimal(s: &[u8]) -> LNat {
    LNat::of_big(big::of_decimal(unsafe { std::str::from_utf8_unchecked(s) }))
}

/// `lean_nat_to_size_t`: the value, or an internal "out of memory" panic
/// when it does not fit a word (2^64 or more).
#[inline(never)]
pub extern "C" fn nat_to_size_t(a: u64) -> u64 {
    match unsafe { take(a) } {
        N::S(x) => x,
        N::B(b) => {
            if big::limbs(&b).len() > 1 {
                crate::internal_panic("out of memory")
            }
            big::low_limb(&b)
        }
    }
}

/// The value modulo 2^64 (`UInt64.ofNat`, `USize.ofNat`, ...).
#[inline(never)]
pub extern "C" fn nat_low_u64(a: u64) -> u64 {
    let n = unsafe { LNat::from_raw(a) };
    n.low_u64()
}

/// `Int.ofNat`. A big `Nat` (>= 2^63) is a big `Int` too: the same object.
#[inline(never)]
pub extern "C" fn nat_to_int(a: u64) -> LInt {
    match unsafe { take(a) } {
        N::S(x) => LInt::of_i128(x as i128),
        N::B(b) => LInt(ptr_of(word_of_big(b))),
    }
}

/// `Int.negSucc n = -(n + 1)`.
#[inline(never)]
pub extern "C" fn nat_neg_succ(a: u64) -> LInt {
    match unsafe { take(a) } {
        N::S(x) => LInt::of_i128(-(x as i128) - 1),
        N::B(b) => LInt::of_big(big::int_neg(big::nat_add_u64(b, 1))),
    }
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

    pub fn of_i128(v: i128) -> LInt {
        if v >= INT_MIN as i128 && v <= INT_MAX as i128 {
            LInt::small(v as i64)
        } else if v >= i64::MIN as i128 && v <= i64::MAX as i128 {
            int_big_of_i64(v as i64)
        } else {
            let m = v.unsigned_abs();
            let b = big::of_limbs2(m as u64, (m >> 64) as u64);
            LInt::of_big(if v < 0 { big::int_neg(b) } else { b })
        }
    }

    /// A big number as an `Int` (normalized: small in [INT_MIN, INT_MAX]).
    #[inline]
    pub fn of_big(b: LBig) -> LInt {
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

/// A big `Int` operand: small value or big number, owned.
enum I {
    S(i64),
    B(LBig),
}

/// The value of a small `Int` word (`lean_scalar_to_int64`).
#[inline(always)]
pub fn int_of_small_word(w: u64) -> i64 {
    (w >> 1) as u32 as i32 as i64
}

#[inline(always)]
unsafe fn take_int(w: u64) -> I {
    if is_small(w) { I::S(int_of_small_word(w)) } else { I::B(big_of_word(w)) }
}

fn int_to_big(i: I) -> LBig {
    match i {
        I::S(x) => big::of_i64(x),
        I::B(b) => b,
    }
}

// The slow paths of the prelude's `lean_int_*` (raw owned words, all cases).

#[inline(never)]
pub extern "C" fn int_neg(a: u64) -> LInt {
    match unsafe { take_int(a) } {
        I::S(x) => LInt::of_i128(-(x as i128)),
        I::B(b) => LInt::of_big(big::int_neg(b)),
    }
}

#[inline(never)]
pub extern "C" fn int_add(a: u64, b: u64) -> LInt {
    match unsafe { (take_int(a), take_int(b)) } {
        (I::S(x), I::S(y)) => LInt::of_i128(x as i128 + y as i128),
        (x, y) => LInt::of_big(big::int_add(int_to_big(x), int_to_big(y))),
    }
}

#[inline(never)]
pub extern "C" fn int_sub(a: u64, b: u64) -> LInt {
    match unsafe { (take_int(a), take_int(b)) } {
        (I::S(x), I::S(y)) => LInt::of_i128(x as i128 - y as i128),
        (x, y) => LInt::of_big(big::int_sub(int_to_big(x), int_to_big(y))),
    }
}

#[inline(never)]
pub extern "C" fn int_mul(a: u64, b: u64) -> LInt {
    match unsafe { (take_int(a), take_int(b)) } {
        (I::S(x), I::S(y)) => LInt::of_i128(x as i128 * y as i128),
        (x, y) => LInt::of_big(big::int_mul(int_to_big(x), int_to_big(y))),
    }
}

/// `Int.div` (T-division, C's `/`); `x / 0 = 0`.
#[inline(never)]
pub extern "C" fn int_div(a: u64, b: u64) -> LInt {
    match unsafe { (take_int(a), take_int(b)) } {
        (x, I::S(0)) => {
            drop(x);
            LInt::small(0)
        }
        (I::S(x), I::S(y)) => LInt::of_i128(x as i128 / y as i128),
        (x, y) => LInt::of_big(big::int_tdiv(int_to_big(x), int_to_big(y))),
    }
}

/// `Int.mod` (T-remainder, C's `%`, sign of the dividend); `x % 0 = x`.
#[inline(never)]
pub extern "C" fn int_mod(a: u64, b: u64) -> LInt {
    match unsafe { (take_int(a), take_int(b)) } {
        (x, I::S(0)) => match x {
            I::S(x) => LInt::small(x),
            I::B(x) => LInt::of_big(x),
        },
        (I::S(x), I::S(y)) => LInt::of_i128(x as i128 % y as i128),
        (x, y) => LInt::of_big(big::int_tmod(int_to_big(x), int_to_big(y))),
    }
}

/// `Int.ediv` (Euclidean); `x / 0 = 0`.
#[inline(never)]
pub extern "C" fn int_ediv(a: u64, b: u64) -> LInt {
    match unsafe { (take_int(a), take_int(b)) } {
        (x, I::S(0)) => {
            drop(x);
            LInt::small(0)
        }
        (I::S(x), I::S(y)) => {
            let (x, y) = (x as i128, y as i128);
            let q = x / y;
            let r = x % y;
            LInt::of_i128(if r < 0 { if y > 0 { q - 1 } else { q + 1 } } else { q })
        }
        (x, y) => LInt::of_big(big::int_ediv(int_to_big(x), int_to_big(y))),
    }
}

/// `Int.emod` (Euclidean, never negative for `y != 0`); `x % 0 = x`.
#[inline(never)]
pub extern "C" fn int_emod(a: u64, b: u64) -> LInt {
    match unsafe { (take_int(a), take_int(b)) } {
        (x, I::S(0)) => match x {
            I::S(x) => LInt::small(x),
            I::B(x) => LInt::of_big(x),
        },
        (I::S(x), I::S(y)) => {
            let (x, y) = (x as i128, y as i128);
            let r = x % y;
            LInt::of_i128(if r < 0 { if y > 0 { r + y } else { r - y } } else { r })
        }
        (x, y) => LInt::of_big(big::int_emod(int_to_big(x), int_to_big(y))),
    }
}

/// Three-way comparison: -1, 0, 1.
#[inline(never)]
pub extern "C" fn int_cmp(a: u64, b: u64) -> i64 {
    match unsafe { (take_int(a), take_int(b)) } {
        (I::S(x), I::S(y)) => (x > y) as i64 - (x < y) as i64,
        // A big value is beyond every small one, on its side of zero.
        (I::S(_), I::B(y)) => {
            if big::is_neg(&y) { 1 } else { -1 }
        }
        (I::B(x), I::S(_)) => {
            if big::is_neg(&x) { -1 } else { 1 }
        }
        (I::B(x), I::B(y)) => big::int_cmp(x, y),
    }
}

#[inline(never)]
pub extern "C" fn int_eq(a: u64, b: u64) -> bool {
    match unsafe { (take_int(a), take_int(b)) } {
        (I::S(x), I::S(y)) => x == y,
        (I::B(x), I::B(y)) => big::int_eq(x, y),
        (x, y) => {
            drop((x, y));
            false
        }
    }
}

/// `Int.natAbs`.
#[inline(never)]
pub extern "C" fn int_nat_abs(a: u64) -> LNat {
    match unsafe { take_int(a) } {
        I::S(x) => LNat::small(x.unsigned_abs()),
        I::B(b) => LNat::of_big(big::int_abs(b)),
    }
}

/// Whether a big `Int` is negative (a small one: its sign bit).
#[inline(never)]
pub extern "C" fn int_is_neg(a: u64) -> bool {
    match unsafe { take_int(a) } {
        I::S(x) => x < 0,
        I::B(b) => big::is_neg(&b),
    }
}

/// The value modulo 2^64 in two's complement (`Int64.ofInt`, ...).
#[inline(never)]
pub extern "C" fn int_low_twos(a: u64) -> u64 {
    match unsafe { take_int(a) } {
        I::S(x) => x as u64,
        I::B(b) => big::low_u64_twos(&b),
    }
}

/// `Int.repr` (decimal); `Int.repr (ofNat m) = Nat.repr m`, shared below 128.
#[inline(never)]
pub extern "C" fn int_repr(a: u64) -> crate::LStr {
    match unsafe { take_int(a) } {
        I::S(x) if (0..128).contains(&x) => crate::string::repr_small(x as u64),
        I::S(x) => crate::string::of_i64(x),
        I::B(b) => crate::string::from_vec(big::to_decimal(&b)),
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

    #[test]
    fn counts() {
        let b = big::of_limbs2(3, 3);
        let x = LNat::of_big(b.clone());
        assert_eq!(b.count_ref().get(), 2);
        let y = x.clone();
        assert_eq!(b.count_ref().get(), 3);
        drop(x);
        drop(y);
        assert_eq!(b.count_ref().get(), 1);
        // A slow path consumes its operands.
        let s = nat_add(LNat::of_big(b.clone()).into_raw(), LNat::small(1).into_raw());
        drop(s);
        assert_eq!(b.count_ref().get(), 1);
        let i = nat_to_int(LNat::of_big(b.clone()).into_raw());
        assert_eq!(b.count_ref().get(), 2);
        drop(i);
        assert_eq!(b.count_ref().get(), 1);
    }

    #[test]
    fn ints() {
        let edges: [i128; 13] = [0, 1, -1, INT_MAX as i128, INT_MIN as i128, INT_MAX as i128 + 1, INT_MIN as i128 - 1,
            1 << 62, -(1 << 62), i64::MIN as i128, i64::MAX as i128, 46341, -46341];
        let i = |v: i128| LInt::of_i128(v);
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
}
