//! Float formatting and the float functions without an LLVM intrinsic.

use crate::string::{from_bytes, LStr};

extern "C" {
    fn snprintf(buf: *mut u8, n: usize, fmt: *const u8, ...) -> i32;
}

/// `lean_float_to_string`: `std::to_string(double)`, i.e. C's
/// `snprintf("%f")` — called directly, so the output is Lean's by
/// construction — with every NaN printed as `NaN`.
#[inline(never)]
pub fn to_string(x: f64) -> LStr {
    if x.is_nan() {
        return from_bytes(b"NaN");
    }
    let mut buf = [0u8; 64];
    let n = unsafe { snprintf(buf.as_mut_ptr(), buf.len(), b"%f\0".as_ptr(), x) };
    if n >= 0 && (n as usize) < buf.len() {
        return from_bytes(&buf[..n as usize]);
    }
    // Up to 309 integer digits for large magnitudes.
    let mut big = vec![0u8; n.max(0) as usize + 1];
    let m = unsafe { snprintf(big.as_mut_ptr(), big.len(), b"%f\0".as_ptr(), x) };
    big.truncate(m.max(0) as usize);
    from_bytes(&big)
}

/// `lean_float32_to_string`: the float is printed through `double`.
#[inline(never)]
pub fn to_string32(x: f32) -> LStr {
    to_string(x as f64)
}

/// `lean_float_of_bits`: NaNs are canonicalized to the quiet NaN.
#[inline]
pub fn of_bits(u: u64) -> f64 {
    let x = f64::from_bits(u);
    if x.is_nan() { f64::from_bits(0x7ff8000000000000) } else { x }
}

/// `lean_float_to_bits`.
#[inline]
pub fn to_bits(x: f64) -> u64 {
    if x.is_nan() { 0x7ff8000000000000 } else { x.to_bits() }
}

#[inline]
pub fn of_bits32(u: u32) -> f32 {
    let x = f32::from_bits(u);
    if x.is_nan() { f32::from_bits(0x7fc00000) } else { x }
}

#[inline]
pub fn to_bits32(x: f32) -> u32 {
    if x.is_nan() { 0x7fc00000 } else { x.to_bits() }
}

extern "C" {
    fn frexp(x: f64, e: *mut i32) -> f64;
    fn frexpf(x: f32, e: *mut i32) -> f32;
    fn scalbn(x: f64, n: i32) -> f64;
    fn scalbnf(x: f32, n: i32) -> f32;
    fn log(x: f64) -> f64;
    fn logf(x: f32) -> f32;
}

/// Mantissa of `frexp`.
#[inline]
pub fn frexp_mant(x: f64) -> f64 {
    let mut e = 0;
    unsafe { frexp(x, &mut e) }
}

/// Exponent of `frexp` (0 for non-finite values, as Lean returns).
#[inline]
pub fn frexp_exp(x: f64) -> i64 {
    if !x.is_finite() {
        return 0;
    }
    let mut e = 0;
    unsafe { frexp(x, &mut e) };
    e as i64
}

#[inline]
pub fn frexp_mant32(x: f32) -> f32 {
    let mut e = 0;
    unsafe { frexpf(x, &mut e) }
}

#[inline]
pub fn frexp_exp32(x: f32) -> i64 {
    if !x.is_finite() {
        return 0;
    }
    let mut e = 0;
    unsafe { frexpf(x, &mut e) };
    e as i64
}

#[inline]
pub fn scalb(x: f64, n: i32) -> f64 {
    unsafe { scalbn(x, n) }
}

#[inline]
pub fn scalb32(x: f32, n: i32) -> f32 {
    unsafe { scalbnf(x, n) }
}

#[inline]
pub fn ln(x: f64) -> f64 {
    unsafe { log(x) }
}

#[inline]
pub fn ln32(x: f32) -> f32 {
    unsafe { logf(x) }
}

/// C libm functions without a lowering for Reussir's math intrinsics. These
/// call glibc directly: Rust's own `f64::asinh` & co. are not libm and
/// differ in the last bits.
pub mod libm {
    use std::sync::atomic::{AtomicUsize, Ordering};

    extern "C" {
        pub fn acosh(x: f64) -> f64;
        pub fn asinh(x: f64) -> f64;
        pub fn atanh(x: f64) -> f64;
        pub fn acoshf(x: f32) -> f32;
        pub fn asinhf(x: f32) -> f32;
        pub fn atanhf(x: f32) -> f32;
        fn dlopen(name: *const std::ffi::c_char, flags: i32) -> *mut std::ffi::c_void;
        fn dlsym(handle: *mut std::ffi::c_void, name: *const std::ffi::c_char) -> *mut std::ffi::c_void;
    }

    /// `Float.cbrt` and `Float32.cbrt` are glibc's `cbrt` and `cbrtf`
    /// natively. A direct `extern "C"` declaration cannot reach them:
    /// Rust's `compiler_builtins`, linked into every executable ahead of
    /// libm, defines its own `cbrt` (a port of CORE-MATH's correctly rounded
    /// one) and `cbrtf` (FreeBSD's) on Linux, and the static link binds
    /// every reference named `cbrt` to those; they differ from glibc's by
    /// 1-2 ulps on about half the doubles (cbrt 27.0 is 3.0 there,
    /// 3.0000000000000004 in glibc). So glibc's are looked up by name, in
    /// libm.so.6 opened explicitly: the global scope (`RTLD_DEFAULT`) holds
    /// libm only while the executable imports some other libm function (it
    /// does today, `asinh` & co. above, but nothing guarantees it; a Rust
    /// program without one finds no `cbrt` there). Without a C library
    /// `cbrt` at all, Rust's is the fallback.
    fn resolve(cache: &AtomicUsize, name: &[u8]) -> usize {
        const RTLD_NOW: i32 = 2;
        let p = cache.load(Ordering::Relaxed);
        if p != 0 {
            return p;
        }
        let name = name.as_ptr() as *const std::ffi::c_char;
        let libm = unsafe { dlopen(b"libm.so.6\0".as_ptr() as *const std::ffi::c_char, RTLD_NOW) };
        let mut p = if libm.is_null() { 0 } else { unsafe { dlsym(libm, name) as usize } };
        if p == 0 {
            p = unsafe { dlsym(std::ptr::null_mut(), name) as usize };
        }
        let p = if p == 0 { MISSING } else { p };
        cache.store(p, Ordering::Relaxed);
        p
    }

    /// `resolve`'s answer when there is no C library function (0: not
    /// looked up yet).
    const MISSING: usize = 1;
    static CBRT: AtomicUsize = AtomicUsize::new(0);
    static CBRTF: AtomicUsize = AtomicUsize::new(0);

    pub unsafe fn cbrt(x: f64) -> f64 {
        match resolve(&CBRT, b"cbrt\0") {
            MISSING => x.cbrt(),
            p => unsafe { std::mem::transmute::<usize, extern "C" fn(f64) -> f64>(p)(x) },
        }
    }

    pub unsafe fn cbrtf(x: f32) -> f32 {
        match resolve(&CBRTF, b"cbrtf\0") {
            MISSING => x.cbrt(),
            p => unsafe { std::mem::transmute::<usize, extern "C" fn(f32) -> f32>(p)(x) },
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        /// glibc's `cbrt` and `cbrtf` are found in an executable that
        /// imports no libm function (this test binary), whose global scope
        /// has no libm (fix-r9-misc).
        #[test]
        fn cbrt_is_the_c_librarys() {
            assert_ne!(resolve(&CBRT, b"cbrt\0"), MISSING);
            assert_ne!(resolve(&CBRTF, b"cbrtf\0"), MISSING);
        }
    }
}
