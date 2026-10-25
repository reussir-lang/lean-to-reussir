//! Reussir's built-in `Nat` and `Int` (rcgmp) under `--int-backend rcgmp`
//! (leanrt built with `--cfg leanrt_rcgmp`).
//!
//! The prelude's `Nat` and `Int` sections are then Reussir code over the
//! built-in integers: Lean's rules composed of Reussir's operators and
//! `core::intrinsic::bigint`. leanrt never reads a handle's encoding (the
//! clean-integration rule): a handle is an opaque pointer that this module
//! passes to rcgmp's public C API (`include/RCGMP/Runtime/Mpz.h`). Small
//! values are tested and converted in Reussir code (`trunci_overflow`), so
//! leanrt only sees the values that are not words, and only where the
//! prelude has no Reussir operation for the step: a box's cell, decimal
//! text.
//!
//! In an `#[ffi(import)]` signature a `Nat`/`Int` parameter is the raw handle
//! (`*mut c_void`), borrowed by the body (the wrapper releases the caller's
//! reference after it); a returned handle carries one reference, which the
//! caller owns. Counts are non-atomic (`atomic` 0), as Reussir's own for a
//! value that is not an `Arc`.

use std::ffi::c_void;

use crate::any::LAny;
use crate::string::Utf8;
use lean_runtime::semantics as sem;

/// The owned handle of a built-in integer (`Clone` retains, `Drop`
/// releases): Reussir's own (local Reussir patch R2), the spelling of a
/// `Nat` or `Int` at a polyffi type argument, so leanrt's boxes hold the
/// type that the textures give them.
pub use reussir_rt::rcgmp::Mpz;

unsafe extern "C" {
    fn rcgmp_mpz_decimal_size(value: *mut c_void) -> usize;
    fn rcgmp_mpz_to_decimal(value: *mut c_void, buffer: *mut u8) -> usize;
    fn rcgmp_mpz_from_decimal(text: *const u8, length: usize, atomic: u32) -> *mut c_void;
    fn rcgmp_mpz_from_word(magnitude: usize, negative: u32, atomic: u32) -> *mut c_void;
}

/// A new reference to the borrowed handle `p` (a texture's parameter).
///
/// # Safety
/// `p` is a live handle.
#[inline(always)]
pub unsafe fn retained(p: *mut c_void) -> Mpz {
    (*std::mem::ManuallyDrop::new(unsafe { Mpz::from_raw(p) })).clone()
}

/// The integer `-v` (`negative`) or `v`, an owned handle.
#[inline]
pub fn of_word(v: u64, negative: bool) -> Mpz {
    unsafe { Mpz::from_raw(rcgmp_mpz_from_word(v as usize, negative as u32, 0)) }
}

/// The box of a big `Nat` (`num` = `any::NUM_NAT`) or `Int` (`NUM_INT`),
/// the borrowed handle `p` (a value the prelude did not box as an
/// immediate: a `Nat` of 2^63 or more, an `Int` outside the `int32` range):
/// a leanrt cell holding a new reference (`any::of_mpz`).
#[cold]
#[inline(never)]
pub extern "C" fn box_big(p: *mut c_void, num: u64) -> LAny {
    crate::any::of_mpz(unsafe { retained(p) }, num)
}

/// The handle a big `Nat` or `Int` box of kind `num` holds, as a returned
/// handle (one reference, the caller's); the box's reference is given up.
/// An immediate never comes here (the prelude decodes it); another pointer
/// is `any::mismatch`.
#[cold]
#[inline(never)]
pub extern "C" fn unbox_big(a: LAny, num: u64) -> *mut c_void {
    crate::any::mpz_of(a, num).into_raw()
}

/// The decimal text of the borrowed handle `p` (`Nat.repr` of a value of
/// 2^63 or more, `Int.repr` of one outside `i64`): rcgmp's digits, a sign
/// first for a negative value.
#[cold]
#[inline(never)]
pub extern "C" fn repr(p: *mut c_void) -> crate::LStr {
    let size = unsafe { rcgmp_mpz_decimal_size(p) };
    let mut d: Vec<u8> = Vec::new();
    if d.try_reserve_exact(size).is_err() {
        crate::big::oom()
    }
    let len = unsafe { rcgmp_mpz_to_decimal(p, d.as_mut_ptr()) };
    debug_assert!(len <= size);
    unsafe { d.set_len(len) };
    crate::string::from_vec(d)
}

/// A `Nat` from its decimal digits, a returned handle; the string is
/// released. (Unit tests only: lean2rr's big literals are Reussir's own.)
#[cfg(test)]
pub extern "C" fn of_decimal(s: crate::LStr) -> *mut c_void {
    let b = s.utf8();
    let p = unsafe { rcgmp_mpz_from_decimal(b.as_ptr(), b.len(), 0) };
    crate::rc_release(s);
    if p.is_null() {
        crate::unreachable_code()
    }
    p
}

/// `Array.replicate`'s size (`lean_mk_array`, `sem::array::replicate_len`)
/// of a `Nat` that is not below 2^63: `v` when it is the value (`fits`),
/// none for 2^64 or more; either way an array that cannot be allocated,
/// which ends the process.
#[cold]
#[inline(never)]
pub extern "C" fn replicate_len(v: u64, fits: bool) -> u64 {
    match sem::array::replicate_len(fits.then_some(v)) {
        Ok(n) => n as u64,
        Err(e) => crate::lean_internal_panic(e),
    }
}

/// The largest `Nat` or `Int` result in bits that the prelude's rules ask
/// for (lean-runtime's `BigNat::MAX_BITS`, leanrt's `big::MAX_BITS`: the
/// same GMP below rcgmp): `Nat.pow` and `Nat.shiftLeft` above it end the
/// process as lean-runtime's rules do (`sem::nat::check_result_bits`).
pub const MAX_BITS: u64 = crate::big::MAX_BITS;
// The prelude's `l2r_nat_max_bits` spells the value as a literal.
const _: () = assert!(MAX_BITS == 137_438_953_088);

/// The unit tests' own `Mpz` glue: a program gets Reussir's, emitted with
/// its bigint code (`rcgmp.retain`/`rcgmp.release`, local Reussir patch
/// R2b); a test binary has none, so these call rcgmp's C entry points.
#[cfg(test)]
mod test_glue {
    use std::ffi::c_void;
    unsafe extern "C" {
        fn rcgmp_mpz_retain(value: *mut c_void, atomic: u32) -> *mut c_void;
        fn rcgmp_mpz_release(value: *mut c_void, atomic: u32);
    }
    #[unsafe(no_mangle)]
    extern "C" fn __reussir_rcgmp_ffi_acquire(value: *mut c_void) {
        unsafe { rcgmp_mpz_retain(value, 0) };
    }
    #[unsafe(no_mangle)]
    extern "C" fn __reussir_rcgmp_ffi_release(value: *mut c_void) {
        unsafe { rcgmp_mpz_release(value, 0) }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::any::NUM_NAT;

    fn of_text(t: &[u8]) -> *mut c_void {
        of_decimal(crate::string::from_vec(t.to_vec()))
    }

    fn text(p: *mut c_void) -> Vec<u8> {
        let s = repr(p);
        let v = s.utf8().to_vec();
        crate::rc_release(s);
        v
    }

    const TWO_100: &[u8] = b"1267650600228229401496703205376";

    /// A big `Nat` in a box: the cell holds its own reference; unboxing a
    /// shared cell gives a new reference and leaves the cell to its other
    /// holder, unboxing the last one moves the reference out.
    #[test]
    fn box_cell_shared_then_unique() {
        let p = of_text(TWO_100);
        let a = box_big(p, NUM_NAT);
        drop(unsafe { Mpz::from_raw(p) });
        assert_eq!(a.num(), NUM_NAT);
        let b = a.clone();
        assert!(!a.is_exclusive());
        let q = unbox_big(b, NUM_NAT);
        assert!(a.is_exclusive());
        let r = unbox_big(a, NUM_NAT);
        assert_eq!(text(q), TWO_100);
        assert_eq!(text(r), TWO_100);
        drop(unsafe { Mpz::from_raw(q) });
        drop(unsafe { Mpz::from_raw(r) });
    }

    /// A box dropped while it holds the last reference to its cell releases
    /// the integer (`any::release_kind`).
    #[test]
    fn box_cell_dropped() {
        let p = of_text(b"-340282366920938463463374607431768211456");
        let a = box_big(p, crate::any::NUM_INT);
        drop(a.clone());
        drop(a);
        assert_eq!(text(p), b"-340282366920938463463374607431768211456");
        drop(unsafe { Mpz::from_raw(p) });
    }

    /// `of_word`: a word of either sign, compared by value with the
    /// decimal text of the same integer.
    #[test]
    fn of_word_values() {
        let a = of_word(u64::MAX, false);
        let b = of_word(u64::MAX, true);
        let c = of_text(b"-18446744073709551615");
        assert_eq!(text(a.as_ptr()), b"18446744073709551615");
        assert_eq!(text(b.as_ptr()), b"-18446744073709551615");
        assert!(b == unsafe { Mpz::from_raw(c) });
        assert!(a > b);
    }
}
