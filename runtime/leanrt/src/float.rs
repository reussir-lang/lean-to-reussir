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

/// The C library's math functions behind `Float`'s and `Float32`'s libm
/// externs (`Float.sin` is `sin`, `Float32.pow` is `powf`, ...), called so
/// that the compiler can neither evaluate nor rewrite them: natively Lean's
/// C calls glibc's function at run time, also on a literal operand (a
/// closed term sits in a once-cell that clang cannot see through, and
/// `lean_float_of_bits` & co. are runtime functions), and glibc's results
/// are not always the correctly rounded ones LLVM assumes.
/// - LLVM constant-folds a libm call whose operand it knows (a literal, or
///   a value it forwarded through an inlined reference): `f32` functions by
///   evaluating the `f64` one and rounding to `float` (`cosf`, `sinf`,
///   `logf`, ... one ulp off glibc's on some inputs, cross-test XT-4), and
///   `exp2` through the host's `pow(2, x)` (`exp2(35.74477454358792)` one
///   ulp off).
/// - LLVM's library-call simplifier rewrites `pow` with a constant operand:
///   `pow(x, 0.5)` into `sqrt`, `pow(x, 2.0)` into `x * x`, `pow(2.0, y)`
///   into `exp2`, `pow(x, -1.0)` into `1 / x`, each one ulp off glibc's
///   `pow` on some inputs (cross-test XT-3).
/// So each function is called through a pointer that `dlsym` finds in
/// libm.so.6 at run time (once, cached): an indirect call the optimizer
/// knows nothing about, to glibc's function by construction (see `resolve`
/// for why a plain `extern "C"` declaration may bind elsewhere). Without
/// libm.so.6 (a static build), the same name declared `extern "C"` is
/// called on operands passed through `black_box`, which keeps it opaque.
/// The exact operations (`sqrt`, `floor`, `ceil`, `round`, `fabs`) stay
/// LLVM intrinsics: every evaluation of them gives the same bits.
pub mod libm {
    use std::hint::black_box;
    use std::sync::atomic::{AtomicUsize, Ordering};

    extern "C" {
        fn dlopen(name: *const std::ffi::c_char, flags: i32) -> *mut std::ffi::c_void;
        fn dlsym(handle: *mut std::ffi::c_void, name: *const std::ffi::c_char) -> *mut std::ffi::c_void;
    }

    /// The functions declared directly: the fallback when `resolve` finds
    /// no C library function.
    mod c {
        extern "C" {
            pub fn sin(x: f64) -> f64;
            pub fn cos(x: f64) -> f64;
            pub fn tan(x: f64) -> f64;
            pub fn asin(x: f64) -> f64;
            pub fn acos(x: f64) -> f64;
            pub fn atan(x: f64) -> f64;
            pub fn atan2(y: f64, x: f64) -> f64;
            pub fn sinh(x: f64) -> f64;
            pub fn cosh(x: f64) -> f64;
            pub fn tanh(x: f64) -> f64;
            pub fn asinh(x: f64) -> f64;
            pub fn acosh(x: f64) -> f64;
            pub fn atanh(x: f64) -> f64;
            pub fn exp(x: f64) -> f64;
            pub fn exp2(x: f64) -> f64;
            pub fn log(x: f64) -> f64;
            pub fn log2(x: f64) -> f64;
            pub fn log10(x: f64) -> f64;
            pub fn pow(x: f64, y: f64) -> f64;
            pub fn cbrt(x: f64) -> f64;
            pub fn sinf(x: f32) -> f32;
            pub fn cosf(x: f32) -> f32;
            pub fn tanf(x: f32) -> f32;
            pub fn asinf(x: f32) -> f32;
            pub fn acosf(x: f32) -> f32;
            pub fn atanf(x: f32) -> f32;
            pub fn atan2f(y: f32, x: f32) -> f32;
            pub fn sinhf(x: f32) -> f32;
            pub fn coshf(x: f32) -> f32;
            pub fn tanhf(x: f32) -> f32;
            pub fn asinhf(x: f32) -> f32;
            pub fn acoshf(x: f32) -> f32;
            pub fn atanhf(x: f32) -> f32;
            pub fn expf(x: f32) -> f32;
            pub fn exp2f(x: f32) -> f32;
            pub fn logf(x: f32) -> f32;
            pub fn log2f(x: f32) -> f32;
            pub fn log10f(x: f32) -> f32;
            pub fn powf(x: f32, y: f32) -> f32;
            pub fn cbrtf(x: f32) -> f32;
        }
    }

    /// The address of the C library's function `name` (NUL-terminated),
    /// looked up once and cached in `cache`; `MISSING` if there is none.
    ///
    /// glibc's functions are looked up by name in libm.so.6 opened
    /// explicitly. A direct `extern "C"` declaration cannot be relied on:
    /// Rust's `compiler_builtins`, linked into every executable ahead of
    /// libm, defines its own `cbrt` (a port of CORE-MATH's correctly rounded
    /// one) and `cbrtf` (FreeBSD's) on Linux, and the static link binds
    /// every reference named `cbrt` to those; they differ from glibc's by
    /// 1-2 ulps on about half the doubles (cbrt 27.0 is 3.0 there,
    /// 3.0000000000000004 in glibc). It defines no other function here
    /// today, but Rust keeps moving float functions into `core`. The global
    /// scope (`RTLD_DEFAULT`) is only the second choice: it holds libm only
    /// while the executable imports some libm function (a Rust program
    /// without one finds no `cbrt` there).
    #[cold]
    #[inline(never)]
    fn resolve(cache: &AtomicUsize, name: &[u8]) -> usize {
        const RTLD_NOW: i32 = 2;
        static LIBM: AtomicUsize = AtomicUsize::new(0);
        let p = cache.load(Ordering::Relaxed);
        if p != 0 {
            return p;
        }
        let name = name.as_ptr() as *const std::ffi::c_char;
        let mut libm = LIBM.load(Ordering::Relaxed);
        if libm == 0 {
            libm = unsafe { dlopen(b"libm.so.6\0".as_ptr() as *const std::ffi::c_char, RTLD_NOW) } as usize;
            LIBM.store(if libm == 0 { MISSING } else { libm }, Ordering::Relaxed);
        }
        let mut p = if libm == 0 || libm == MISSING { 0 } else { unsafe { dlsym(libm as *mut std::ffi::c_void, name) as usize } };
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

    /// `pub fn name(x: T) -> T` (or `(x: T, y: T)`) calling the C library's
    /// `name`, as described above.
    macro_rules! glibc {
        ($($name:ident($x:ident : $t:ty);)*) => {$(
            #[inline]
            pub fn $name($x: $t) -> $t {
                static P: AtomicUsize = AtomicUsize::new(0);
                let p = match P.load(Ordering::Relaxed) {
                    0 => resolve(&P, concat!(stringify!($name), "\0").as_bytes()),
                    p => p,
                };
                match p {
                    MISSING => unsafe { c::$name(black_box($x)) },
                    p => unsafe { std::mem::transmute::<usize, extern "C" fn($t) -> $t>(p)($x) },
                }
            }
        )*};
        ($($name:ident($x:ident : $t:ty, $y:ident);)*) => {$(
            #[inline]
            pub fn $name($x: $t, $y: $t) -> $t {
                static P: AtomicUsize = AtomicUsize::new(0);
                let p = match P.load(Ordering::Relaxed) {
                    0 => resolve(&P, concat!(stringify!($name), "\0").as_bytes()),
                    p => p,
                };
                match p {
                    MISSING => unsafe { c::$name(black_box($x), black_box($y)) },
                    p => unsafe { std::mem::transmute::<usize, extern "C" fn($t, $t) -> $t>(p)($x, $y) },
                }
            }
        )*};
    }

    glibc! {
        sin(x: f64); cos(x: f64); tan(x: f64); asin(x: f64); acos(x: f64); atan(x: f64);
        sinh(x: f64); cosh(x: f64); tanh(x: f64); asinh(x: f64); acosh(x: f64); atanh(x: f64);
        exp(x: f64); exp2(x: f64); log(x: f64); log2(x: f64); log10(x: f64); cbrt(x: f64);
        sinf(x: f32); cosf(x: f32); tanf(x: f32); asinf(x: f32); acosf(x: f32); atanf(x: f32);
        sinhf(x: f32); coshf(x: f32); tanhf(x: f32); asinhf(x: f32); acoshf(x: f32); atanhf(x: f32);
        expf(x: f32); exp2f(x: f32); logf(x: f32); log2f(x: f32); log10f(x: f32); cbrtf(x: f32);
    }
    glibc! {
        atan2(y: f64, x); pow(x: f64, y); atan2f(y: f32, x); powf(x: f32, y);
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        /// glibc's `cbrt` and `cbrtf` are found in an executable that
        /// imports no libm function (this test binary), whose global scope
        /// has no libm (fix-r9-misc).
        #[test]
        fn cbrt_is_the_c_librarys() {
            assert_ne!(resolve(&AtomicUsize::new(0), b"cbrt\0"), MISSING);
            assert_ne!(resolve(&AtomicUsize::new(0), b"cbrtf\0"), MISSING);
            // 27.0 is 3.0 in Rust's (`compiler_builtins`) cbrt.
            assert_eq!(cbrt(27.0).to_bits(), 3.0000000000000004f64.to_bits());
        }

        /// Literal operands give glibc's results, not LLVM's folded or
        /// rewritten ones (cross-tests XT-3, XT-4; the values are native
        /// Lean's).
        #[test]
        fn literal_operands_are_not_folded() {
            assert_eq!(pow(f64::from_bits(4607190032495475448), 0.5).to_bits(), 4607186224040159859);
            assert_eq!(pow(f64::from_bits(4607189316783422666), 2.0).to_bits(), 4607196225332193187);
            assert_eq!(pow(2.0, f64::from_bits(4600071516463376106)).to_bits(), 4608439918779900865);
            assert_eq!(exp2(35.74477454358792).to_bits(), 4767851543770847998);
            assert_eq!(cosf(f32::from_bits(0x3dce4fee)).to_bits(), 1065268159);
        }
    }
}
