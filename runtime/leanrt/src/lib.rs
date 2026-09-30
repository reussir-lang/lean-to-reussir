//! `leanrt`: the Rust half of lean2rr's runtime.
//!
//! The Reussir prelude (`runtime/prelude.rr`) implements each Lean extern:
//! fast paths in Reussir, everything else through small `#[ffi(import)]`
//! textures that call into this crate. Keeping the code here (rather than in
//! the prelude's `extern "rust"` block, which is copied into every texture)
//! keeps texture compilation cheap and gives the runtime one copy of its
//! global state: the stdout buffer, once-cells, and panic settings.
//!
//! Small hot functions are `#[inline]` so they are instantiated into the
//! textures (and can be inlined into Reussir code); slow paths are
//! `#[inline(never)]`. The cold paths of hot textures are `extern "C"`
//! (they cannot unwind: runtime failures exit or abort), so calls to them
//! need no landing pads, which keeps the textures under LLVM's inlining
//! threshold.

#![allow(improper_ctypes_definitions)]

extern crate reussir_rt;

pub mod alloc;
pub mod array;
pub mod big;
pub mod cfile;
pub mod float;
pub mod fs;
pub mod gmp;
pub mod hash;
pub mod io;
pub mod once;
pub mod proc;
pub mod rt;
pub mod string;
pub mod tagvec;
pub mod task;

pub use big::LBig;
pub use string::LStr;

/// A fresh "address" for `ptrAddrUnsafe` of a value without one: odd (so
/// never a real pointer) and never repeated.
pub fn fresh_addr() -> u64 {
    static NEXT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(1);
    NEXT.fetch_add(2, std::sync::atomic::Ordering::Relaxed)
}

/// Give up a handle a texture received by value but only borrowed (every
/// FFI call consumes its arguments). A shared handle is just decremented;
/// freeing the last reference is out of line, which keeps textures small
/// enough for LLVM to inline them into Reussir code.
#[inline(always)]
pub fn rc_release<T>(r: reussir_rt::rc::Rc<T>) {
    let c = r.count_ref().get();
    if c == 1 {
        rc_drop_last(r)
    } else {
        r.count_ref().set(c - 1);
        std::mem::forget(r);
    }
}

#[cold]
#[inline(never)]
extern "C" fn rc_drop_last<T>(r: reussir_rt::rc::Rc<T>) {
    drop(r)
}

/// `lean_panic_fn`: print the message (Lean has already formatted it as
/// `PANIC at ...`) to stderr and continue. Native executables also print
/// `backtrace:` and a stack trace unless `LEAN_BACKTRACE=0`; we print the
/// header and no frames (tests compare stderr with backtraces removed).
/// `LEAN_ABORT_ON_PANIC` aborts, as natively.
///
/// Output order as `lean_panic_impl`: normally the lines go through Lean's
/// (unbuffered) stderr stream; with `LEAN_ABORT_ON_PANIC` they go to
/// `std::cerr`, which is tied to `std::cout` and so flushes stdout first,
/// and the process then aborts.
#[inline(never)]
pub fn panic_msg(msg: &[u8]) {
    let abort = std::env::var_os("LEAN_ABORT_ON_PANIC").is_some();
    if abort {
        io::flush_stdout();
    }
    let mut line = msg.to_vec();
    line.push(b'\n');
    io::eprint(&line);
    let bt = std::env::var("LEAN_BACKTRACE").map(|v| v != "0").unwrap_or(true);
    if bt {
        io::eprint(b"backtrace:\n(stack trace unavailable)\n");
    }
    if abort {
        std::process::abort();
    }
}

/// `lean_internal_panic`: `INTERNAL PANIC: msg` straight to stderr, then
/// `exit(1)` (which flushes stdout afterwards), or `abort()` without flushing
/// under `LEAN_ABORT_ON_PANIC`.
#[inline(never)]
pub fn internal_panic(msg: &str) -> ! {
    io::eprint(format!("INTERNAL PANIC: {}\n", msg).as_bytes());
    if std::env::var_os("LEAN_ABORT_ON_PANIC").is_some() {
        std::process::abort();
    }
    io::exit(1)
}

/// An uncaught `IO` exception at the top level: printed with `std::cerr`
/// (which flushes stdout first), exit status 1.
#[inline(never)]
pub fn uncaught_exception(msg: &[u8]) -> ! {
    io::flush_stdout();
    let mut line = b"uncaught exception: ".to_vec();
    // `string_cstr`: up to the first NUL.
    line.extend_from_slice(&msg[..msg.iter().position(|&b| b == 0).unwrap_or(msg.len())]);
    line.push(b'\n');
    io::eprint(&line);
    io::exit(1)
}

/// `Option.getOrBlock!` on `none` (`Promise.result!` of a dropped promise):
/// a forced panic message (to `std::cerr`, so stdout is flushed first), then
/// block forever, as natively.
#[inline(never)]
pub fn promise_dropped() -> ! {
    io::flush_stdout();
    io::eprint(b"PANIC: Promise.result!: promise has been dropped without ever being resolved\n");
    let bt = std::env::var("LEAN_BACKTRACE").map(|v| v != "0").unwrap_or(true);
    if bt {
        io::eprint(b"backtrace:\n(stack trace unavailable)\n");
    }
    if std::env::var_os("LEAN_ABORT_ON_PANIC").is_some() {
        std::process::abort();
    }
    loop {
        std::thread::sleep(std::time::Duration::from_secs(3600));
    }
}
