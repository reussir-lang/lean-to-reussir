//! The standard streams, as glibc's `stdin`, `stdout` and `stderr` `FILE`s
//! (see `cfile`): stdout buffered in `st_blksize` blocks (line buffered on
//! a terminal), stderr unbuffered, stdin read in blocks. Lean's
//! `IO.getStdout` & co. are streams over these `FILE`s, so their operations
//! are the handle operations (`CFile::put`, `read`, `get_line`, `flush`).
//!
//! Errors (a closed descriptor, `EPIPE`, the wrong direction, ...) are
//! reported through the runtime's last-error slot (`fs::ok()` & co.), so
//! lean2rr can turn them into Lean's `IO.Error`s exactly as
//! `lean_io_prim_handle_*` do.
//!
//! At exit (also `IO.Process.exit` and internal panics) the streams are
//! finished as a native Lean program's are: libc++'s `ios_base::Init`
//! destructor flushes stdout, then glibc's `_IO_cleanup` writes the pending
//! output of every `FILE` (most recently opened first; stderr, stdout,
//! stdin last) and syncs every used buffered one, which gives seekable
//! read-ahead back (stdin's position is left where the program stopped
//! reading, for the next process).
//!
//! The runtime is single-threaded (Reussir reference counts are not atomic),
//! so the global state is a plain cell. It lives here, in the one `leanrt`
//! crate every texture links against.

use crate::cfile::{CFile, NO_READS, NO_WRITES, UNBUFFERED};
use crate::fs::{set_err, set_ok};
use std::cell::UnsafeCell;

struct Global<T>(UnsafeCell<T>);
unsafe impl<T> Sync for Global<T> {}

static STDIN: Global<CFile> = Global(UnsafeCell::new(CFile::new(0, NO_WRITES)));
static STDOUT: Global<CFile> = Global(UnsafeCell::new(CFile::new(1, NO_READS)));
static STDERR: Global<CFile> = Global(UnsafeCell::new(CFile::new(2, NO_READS | UNBUFFERED)));

/// The standard stream `fd` (0, 1 or 2; anything else is stderr).
#[inline]
fn std_file(fd: u64) -> &'static mut CFile {
    let g = match fd {
        0 => &STDIN,
        1 => &STDOUT,
        _ => &STDERR,
    };
    unsafe { &mut *g.0.get() }
}

extern "C" {
    fn atexit(f: extern "C" fn()) -> i32;
    fn isatty(fd: i32) -> i32;
}

/// What a native Lean program's exit does with stdio (see the module
/// comment).
extern "C" fn flush_at_exit() {
    let _ = std_file(1).flush();
    crate::fs::for_each_open(|f| f.exit_flush());
    for fd in [2, 1, 0] {
        std_file(fd).exit_flush();
    }
    crate::fs::for_each_open(|f| f.exit_unbuffer());
    for fd in [2, 1, 0] {
        std_file(fd).exit_unbuffer();
    }
}

static AT_EXIT: Global<bool> = Global(UnsafeCell::new(false));

/// Register the exit processing (once; on the first use of any `FILE`).
pub(crate) fn flush_at_exit_registered() {
    let r = unsafe { &mut *AT_EXIT.0.get() };
    if !*r {
        *r = true;
        unsafe { atexit(flush_at_exit) };
    }
}

/// `_IO_new_file_underflow`'s courtesy flush: reading a line-buffered or
/// unbuffered stream first writes a line-buffered stdout's pending output.
pub(crate) fn flush_line_buffered_stdout() {
    let out = std_file(1);
    if out.is_line_buffered() {
        let _ = out.flush_pending();
    }
}

/// Whether a file descriptor is a terminal.
pub fn is_tty(fd: u64) -> bool {
    unsafe { isatty(fd as i32) == 1 }
}

fn record(r: Result<(), i32>) {
    match r {
        Ok(()) => set_ok(),
        Err(e) => set_err(e, None),
    }
}

/// `putStr`/`write` on a standard stream (`fwrite`), recording the outcome
/// in the last-error slot.
#[inline(never)]
pub fn stream_put(fd: u64, data: &[u8]) {
    record(std_file(fd).put(data))
}

/// `flush` on a standard stream (`fflush`).
#[inline(never)]
pub fn stream_flush(fd: u64) {
    record(std_file(fd).flush())
}

/// `read n` on a standard stream (`fread`).
#[inline(never)]
pub fn stream_read(fd: u64, n: u64) -> Vec<u8> {
    match crate::fs::lean_read(std_file(fd), n) {
        Ok(v) => {
            set_ok();
            v
        }
        Err(e) => {
            set_err(e, None);
            Vec::new()
        }
    }
}

/// `getLine` on a standard stream.
#[inline(never)]
pub fn stream_get_line(fd: u64) -> Vec<u8> {
    match std_file(fd).get_line() {
        Ok(v) => {
            set_ok();
            v
        }
        Err(e) => {
            set_err(e, None);
            Vec::new()
        }
    }
}

/// Write all buffered stdout bytes (`fflush(stdout)`, as `std::cerr`'s tie
/// does before a runtime message), ignoring errors.
#[inline(never)]
pub fn flush_stdout() {
    let _ = std_file(1).flush();
}

/// Runtime diagnostics (panics, traces, timings) on stderr: errors are
/// ignored and the last-error slot is left alone.
#[inline(never)]
pub fn eprint(data: &[u8]) {
    let _ = std_file(2).put(data);
}

/// Flush as at exit and terminate the process.
pub fn exit(code: i32) -> ! {
    flush_at_exit_registered();
    std::process::exit(code)
}
