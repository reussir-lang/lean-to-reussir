//! Float formatting into lean2rr strings. The rules are lean-runtime's
//! (`semantics::float`, `semantics::float32`); this makes their text a
//! string. (The libm functions are lean-runtime's `semantics::libm`, which
//! the prelude calls directly.)

use crate::string::{from_bytes, from_counted, LStr};
use lean_runtime::semantics as sem;
use std::fmt;

/// A `fmt::Write` into a stack buffer: lean-runtime's formatting functions
/// write their text here. `%f` of a finite double takes at most 317 bytes
/// (309 integer digits, the sign, the point and six decimals).
struct StackText {
    buf: [u8; 320],
    len: usize,
}

impl fmt::Write for StackText {
    #[inline]
    fn write_str(&mut self, s: &str) -> fmt::Result {
        let end = self.len + s.len();
        let dst = self.buf.get_mut(self.len..end).ok_or(fmt::Error)?;
        dst.copy_from_slice(s.as_bytes());
        self.len = end;
        Ok(())
    }
}

impl StackText {
    #[inline(always)]
    fn new() -> Self {
        StackText { buf: [0; 320], len: 0 }
    }

    /// The text as a string (float texts are ASCII: one character a byte).
    #[inline(always)]
    fn to_str(&self) -> LStr {
        from_counted(&self.buf[..self.len], self.len as u64)
    }
}

/// `lean_float_to_string` (lean-runtime's `float::to_string`), formatted on
/// the stack (on the heap should a text not fit).
#[inline(never)]
pub fn to_string(x: f64) -> LStr {
    let mut t = StackText::new();
    if sem::float::to_string(x, &mut t).is_ok() {
        return t.to_str();
    }
    let mut h = String::new();
    let _ = sem::float::to_string(x, &mut h);
    from_bytes(h.as_bytes())
}

/// `lean_float32_to_string` (lean-runtime's `float32::to_string`).
#[inline(never)]
pub fn to_string32(x: f32) -> LStr {
    let mut t = StackText::new();
    if sem::float32::to_string(x, &mut t).is_ok() {
        return t.to_str();
    }
    let mut h = String::new();
    let _ = sem::float32::to_string(x, &mut h);
    from_bytes(h.as_bytes())
}

/// lean-runtime's libm functions that the prelude calls out of line:
///
/// - those that hide their operands from LLVM with `black_box` (`exp2`,
///   `pow`, `Float32`'s inexact functions, `atan2f`, `powf`). Inlined into
///   Reussir code, `black_box`'s stack slot escapes into the caller, and LLVM
///   does not turn a tail call into a jump while an escaped stack slot is
///   live: a Lean loop (a self-tail-calling Reussir function) that calls one
///   of them would grow the stack at every iteration and overflow it (100
///   million iterations of `Float.pow` in the 1 GiB main stack);
/// - lean-runtime's ports of glibc's `cbrt`, `cbrtf`, `atanh`, `atanhf`:
///   too big for a texture that LLVM inlines, and a texture that is not
///   inlined is a call through the packed-argument FFI boundary, whose stack
///   slots in the caller have the same effect (2 million iterations of
///   `Float.cbrt` overflowed a 1 MiB stack; review RULR-01). They exist only
///   where lean-runtime has ports (aarch64 Linux with glibc); on any other
///   target the wrappers end the program with an internal panic when called,
///   so programs that do not call them still build and run (RULR-02).
///
/// Out of line the slots are the callee's; the call costs one more hop than
/// native Lean's direct call into libm (the wrapper, then lean-runtime's
/// function). LLVM cannot see into them from Reussir code either. Remove
/// these wrappers when lean-runtime marks the functions `#[inline(never)]`
/// itself (agreed by lean-runtime's users).
pub mod libm_call {
    use lean_runtime::semantics::libm;

    macro_rules! out_of_line {
        ($($name:ident($($a:ident),*) -> $t:ty;)*) => {
            $(
                #[inline(never)]
                pub fn $name($($a: $t),*) -> $t {
                    libm::$name($($a),*)
                }
            )*
        };
    }

    out_of_line! {
        exp2(x) -> f64;
        pow(x, y) -> f64;
        acosf(x) -> f32;
        acoshf(x) -> f32;
        asinf(x) -> f32;
        asinhf(x) -> f32;
        atanf(x) -> f32;
        cosf(x) -> f32;
        coshf(x) -> f32;
        expf(x) -> f32;
        exp2f(x) -> f32;
        logf(x) -> f32;
        log10f(x) -> f32;
        log2f(x) -> f32;
        sinf(x) -> f32;
        sinhf(x) -> f32;
        tanf(x) -> f32;
        tanhf(x) -> f32;
        atan2f(y, x) -> f32;
        powf(x, y) -> f32;
    }

    /// lean-runtime's ports of glibc's functions, where it has them.
    macro_rules! ported {
        ($($name:ident($a:ident) -> $t:ty;)*) => {
            $(
                #[cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]
                #[inline(never)]
                pub fn $name($a: $t) -> $t {
                    libm::$name($a)
                }

                #[cfg(not(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu")))]
                #[inline(never)]
                pub fn $name(_: $t) -> $t {
                    crate::internal_panic(concat!(
                        "no lean-runtime port of ", stringify!($name), " for this target yet"))
                }
            )*
        };
    }

    ported! {
        cbrt(x) -> f64;
        atanh(x) -> f64;
        cbrtf(x) -> f32;
        atanhf(x) -> f32;
    }
}
