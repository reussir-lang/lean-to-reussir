//! Glue for the standard streams, the exit, the clocks and the runtime's own
//! standard-error lines, over lean-runtime's io (`lean_runtime::io`).
//!
//! The standard streams are lean-runtime's models of glibc's `stdin`,
//! `stdout` and `stderr` `FILE`s (`io::handle`, `io::cfile`): stdout
//! buffered in `st_blksize` blocks (line buffered on a terminal), stderr
//! unbuffered, stdin read in blocks. Lean's `IO.getStdout` & co. are streams
//! over them, which lean2rr builds as closures over `stream_*` (the current
//! streams of `IO.setStdout` & co. are lean2rr's own cells, generated with
//! the program: lean2rr's representation of `IO.FS.Stream`). Their outcomes
//! go to the last-error slot (`fs::ok()` & co.), so lean2rr turns errors into
//! Lean's `IO.Error`s as `lean_io_prim_handle_*` do.
//!
//! The exit is lean-runtime's (`io::exit`): every path that ends the process
//! normally calls [`exit`], which writes the streams' pending output as a
//! native Lean program's C `exit` does (libc++'s flush of `std::cout`, then
//! glibc's `_IO_cleanup`), then exits. `main`'s return ([`main_exit`]) and
//! an uncaught error first wait for the io layer's dedicated tasks
//! (`io::exit::after_main`, as `lean_finalize_task_manager` does). No path
//! exits while holding one of lean-runtime's stream locks: the sink of
//! `getLine`, the one call back into lean2rr under such a lock, is a `Vec`
//! whose failed allocation aborts (as Rust's does, status 134), never exits
//! (`fs`, "sinks").

use crate::fs::{lean_get_line, lean_read, record};
use lean_runtime::io::{self as lio, Handle};

/// The standard stream `fd` (0, 1 or 2; anything else is stderr).
#[inline]
fn std_handle(fd: u64) -> Handle {
    match fd {
        0 => Handle::stdin(),
        1 => Handle::stdout(),
        _ => Handle::stderr(),
    }
}

/// Whether standard stream `fd` is a terminal (`isatty`).
pub fn is_tty(fd: u64) -> bool {
    std_handle(fd).is_tty()
}

/// `putStr`/`write` on a standard stream (`fwrite`), recording the outcome
/// in the last-error slot.
#[inline(never)]
pub fn stream_put(fd: u64, data: &[u8]) {
    // Output is where the order of threads shows (`sched::effect`).
    crate::sched::effect();
    record(std_handle(fd).put_str(data));
}

/// `flush` on a standard stream (`fflush`).
#[inline(never)]
pub fn stream_flush(fd: u64) {
    crate::sched::effect();
    record(std_handle(fd).flush());
}

/// `read n` on a standard stream (`fread`).
#[inline(never)]
pub fn stream_read(fd: u64, n: u64) -> crate::array::RVec<u8> {
    lean_read(&std_handle(fd), n)
}

/// `getLine` on a standard stream.
#[inline(never)]
pub fn stream_get_line(fd: u64) -> crate::string::LStr {
    lean_get_line(&std_handle(fd))
}

/// Write all buffered stdout bytes (`fflush(stdout)`, as `std::cerr`'s tie
/// does before a runtime message), ignoring errors.
#[inline(never)]
pub fn flush_stdout() {
    let _ = Handle::stdout().flush();
}

/// Runtime diagnostics (panics, traces, timings) on stderr: errors are
/// ignored and the last-error slot is left alone.
#[inline(never)]
pub fn eprint(data: &[u8]) {
    let _ = Handle::stderr().put_str(data);
}

extern "C" {
    /// lean2rr's `l2r_stderr_put(s : LStr) -> u64` (the current stderr
    /// stream's `putStr`), exported by every program as
    /// `extern "C" trampoline "l2r_stderr_put_c" = l2r_stderr_put;` (one
    /// pointer argument, consumed; a trivial trampoline). Weak: null when
    /// the program does not define it.
    #[linkage = "extern_weak"]
    static l2r_stderr_put_c: *const std::ffi::c_void;
}

/// A runtime diagnostic (the runtime's own panics, `dbgTraceIfShared`)
/// through the program's current stderr stream (native `io_eprintln`),
/// called from Rust so that Reussir sees no call from the prelude's helpers
/// into the stream code; descriptor 2 when the program has no
/// `l2r_stderr_put_c`.
#[inline(never)]
pub fn diag_put(s: crate::string::LStr) {
    let f = unsafe { l2r_stderr_put_c };
    if f.is_null() {
        eprint(crate::string::bytes(&s));
        crate::rc_release(s);
    } else {
        let put: unsafe extern "C" fn(*mut std::ffi::c_void) -> u64 = unsafe { std::mem::transmute(f) };
        let raw: *mut std::ffi::c_void = unsafe { std::mem::transmute(s) };
        unsafe { put(raw) };
    }
}

/// C's `exit(code)` in a native Lean program (`IO.Process.exit`, internal
/// panics, the end of `main`): the streams' pending output written as
/// natively (`io::exit::exit`), then the process ends.
pub fn exit(code: i32) -> ! {
    lio::exit::exit(code)
}

/// `IO.Process.forceExit` (`std::_Exit`): no flushing, no exit handlers.
/// First the writer threads of the streams this context's drops handed off
/// end (lean-runtime's writers point, `sched::before_publish`): natively the
/// drop's `fclose` had written those bytes before any `_Exit` (lean-runtime
/// docs/sched.md, "The glue", item 11). lean-runtime's own
/// `io::exit::force_exit` ends with `std::process::exit`, which runs the
/// handlers of linked C code (mimalloc's); its documentation asks a glue that
/// needs `_Exit` exactly to call `_exit`.
pub fn force_exit(code: i32) -> ! {
    extern "C" {
        fn _exit(code: i32) -> !;
    }
    crate::sched::before_publish();
    unsafe { _exit(code) }
}

/// The end of the process after `main` has returned (`l2r_exit`): the io
/// layer's dedicated tasks are waited for (`io::exit::after_main`, part of
/// `lean_finalize_task_manager`), then [`exit`].
pub fn main_exit(code: i32) -> ! {
    lio::exit::after_main();
    exit(code)
}

/// `CLOCK_MONOTONIC` in nanoseconds (`IO.monoNanosNow`, `IO.monoMsNow`,
/// `timeit`), lean-runtime's. Out of line: inlined, its `timespec` buffer is a
/// stack slot whose address escapes, and LLVM then keeps the calling loop's
/// self tail calls as calls.
#[inline(never)]
pub fn mono_nanos() -> u64 {
    lio::env::mono_nanos_now()
}

/// A clock read of the program (`IO.monoNanosNow`, `IO.monoMsNow`): a
/// polling point of lean-runtime's scheduler (docs/sched.md, "The glue",
/// item 5), so that a loop waiting for the time to pass lets the others go
/// on, then [`mono_nanos`].
#[inline(never)]
pub fn mono_nanos_polled() -> u64 {
    crate::sched::poll();
    mono_nanos()
}

/// `Std.Time.Timestamp.now`'s clock read: a polling point, then
/// [`realtime_nanos`].
#[inline(never)]
pub fn realtime_nanos_polled() -> i64 {
    crate::sched::poll();
    realtime_nanos()
}

/// The system (real-time) clock in nanoseconds since the Unix epoch, signed,
/// from lean-runtime's seconds and nanoseconds (`lean_get_current_time`,
/// which `Std.Time.Timestamp.now` calls; lean2rr's shim builds the
/// timestamp).
#[inline(never)]
pub fn realtime_nanos() -> i64 {
    let (s, ns) = lio::time::current_time();
    s.wrapping_mul(1_000_000_000).wrapping_add(ns)
}

/// `timeit`'s line (`lean_io_timeit`): lean-runtime's text of `msg` and the
/// time since `start` (a [`mono_nanos`] reading), with its newline; lean2rr
/// writes it with the current stderr stream's `putStr` (`io_eprintln`).
#[inline(never)]
pub fn timeit_text(msg: crate::string::LStr, start: u64) -> crate::string::LStr {
    let nanos = mono_nanos().saturating_sub(start);
    let mut line = lio::time::timeit_line(crate::string::bytes(&msg), nanos);
    line.push(b'\n');
    crate::rc_release(msg);
    crate::string::from_bytes(&line)
}

/// `allocprof`'s text after the action (`lean_io_allocprof`): `msg` up to
/// its first NUL, a newline, lean-runtime's note and a newline, with the
/// newline of `io_eprintln`.
#[inline(never)]
pub fn allocprof_text(msg: crate::string::LStr) -> crate::string::LStr {
    let m = crate::string::bytes(&msg);
    let m = &m[..m.iter().position(|&b| b == 0).unwrap_or(m.len())];
    let mut out = m.to_vec();
    out.push(b'\n');
    out.extend_from_slice(lio::debug::ALLOCPROF_NOTE);
    out.extend_from_slice(b"\n\n");
    crate::rc_release(msg);
    crate::string::from_bytes(&out)
}
