//! Float formatting and the float functions without an LLVM intrinsic.

use crate::string::{from_bytes, LStr};

/// `lean_float_to_string`: `std::to_string(double)`, i.e. `printf("%f")`,
/// with every NaN printed as `NaN`. Rust's `{:.6}` formatting is exact and
/// rounds ties to even like glibc (checked on ~800k values including exact
/// ties, infinities and `-0.0`).
#[inline(never)]
pub fn to_string(x: f64) -> LStr {
    if x.is_nan() {
        return from_bytes(b"NaN");
    }
    from_bytes(format!("{:.6}", x).as_bytes())
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
        fn dlsym(handle: *mut std::ffi::c_void, name: *const std::ffi::c_char) -> *mut std::ffi::c_void;
    }

    /// Rust's `compiler_builtins` defines its own (musl-derived) `cbrt` and
    /// `cbrtf`, which the static link binds to; they differ from glibc's by
    /// an ulp. Resolve glibc's through the dynamic symbol table instead.
    fn resolve(cache: &AtomicUsize, name: &[u8]) -> usize {
        let p = cache.load(Ordering::Relaxed);
        if p != 0 {
            return p;
        }
        let p = unsafe { dlsym(std::ptr::null_mut(), name.as_ptr() as *const std::ffi::c_char) } as usize;
        cache.store(p, Ordering::Relaxed);
        p
    }

    static CBRT: AtomicUsize = AtomicUsize::new(0);
    static CBRTF: AtomicUsize = AtomicUsize::new(0);

    pub unsafe fn cbrt(x: f64) -> f64 {
        match resolve(&CBRT, b"cbrt\0") {
            0 => x.cbrt(),
            p => unsafe { std::mem::transmute::<usize, extern "C" fn(f64) -> f64>(p)(x) },
        }
    }

    pub unsafe fn cbrtf(x: f32) -> f32 {
        match resolve(&CBRTF, b"cbrtf\0") {
            0 => x.cbrt(),
            p => unsafe { std::mem::transmute::<usize, extern "C" fn(f32) -> f32>(p)(x) },
        }
    }
}
