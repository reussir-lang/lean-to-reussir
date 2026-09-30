//! Standard streams with C stdio buffering.
//!
//! Native Lean writes through C `FILE*`s: stdout is fully buffered when it
//! is not a terminal and line buffered when it is; stderr is unbuffered.
//! stdout is flushed when the process exits (`exit`, return from `main`,
//! uncaught exceptions, `IO.Process.exit`). The buffer lives here, in the
//! one `leanrt` crate every texture links against, so all output goes
//! through a single buffer in program order.
//!
//! The runtime is single-threaded (Reussir reference counts are not atomic),
//! so the global state is a plain cell.

use std::cell::UnsafeCell;
use std::io::Write;

struct Global<T>(UnsafeCell<T>);
unsafe impl<T> Sync for Global<T> {}

const BUF_CAP: usize = 1 << 16;

struct Out {
    buf: Vec<u8>,
    /// `None` until the first write decides the buffering mode.
    line_buffered: Option<bool>,
    atexit_registered: bool,
}

static OUT: Global<Out> = Global(UnsafeCell::new(Out { buf: Vec::new(), line_buffered: None, atexit_registered: false }));

struct In {
    buf: Vec<u8>,
    pos: usize,
    eof: bool,
}

static IN: Global<In> = Global(UnsafeCell::new(In { buf: Vec::new(), pos: 0, eof: false }));

#[inline]
fn out() -> &'static mut Out {
    unsafe { &mut *OUT.0.get() }
}

#[inline]
fn inp() -> &'static mut In {
    unsafe { &mut *IN.0.get() }
}

extern "C" {
    fn atexit(f: extern "C" fn()) -> i32;
    fn isatty(fd: i32) -> i32;
    fn write(fd: i32, buf: *const std::ffi::c_void, n: usize) -> isize;
    fn read(fd: i32, buf: *mut std::ffi::c_void, n: usize) -> isize;
}

extern "C" fn flush_at_exit() {
    flush_stdout();
}

/// Whether a file descriptor is a terminal.
pub fn is_tty(fd: u64) -> bool {
    unsafe { isatty(fd as i32) == 1 }
}

fn write_fd(fd: i32, mut data: &[u8]) -> bool {
    while !data.is_empty() {
        let n = unsafe { write(fd, data.as_ptr() as *const std::ffi::c_void, data.len()) };
        if n < 0 {
            if std::io::Error::last_os_error().kind() == std::io::ErrorKind::Interrupted {
                continue;
            }
            return false;
        }
        data = &data[n as usize..];
    }
    true
}

/// Write all buffered stdout bytes.
#[inline(never)]
pub fn flush_stdout() {
    let o = out();
    if !o.buf.is_empty() {
        write_fd(1, &o.buf);
        o.buf.clear();
    }
}

#[inline(never)]
fn stdout_init(o: &mut Out) -> bool {
    let lb = is_tty(1);
    o.line_buffered = Some(lb);
    if !o.atexit_registered {
        o.atexit_registered = true;
        unsafe { atexit(flush_at_exit) };
    }
    o.buf.reserve(BUF_CAP);
    lb
}

/// Append bytes to stdout.
#[inline(never)]
pub fn write_stdout(data: &[u8]) {
    let o = out();
    let lb = match o.line_buffered {
        Some(b) => b,
        None => stdout_init(o),
    };
    if o.buf.len() + data.len() > BUF_CAP {
        flush_stdout();
        if data.len() >= BUF_CAP {
            write_fd(1, data);
            return;
        }
    }
    let o = out();
    o.buf.extend_from_slice(data);
    if lb && data.contains(&b'\n') {
        flush_stdout();
    }
}

/// stderr is unbuffered (as C's `stderr`).
#[inline(never)]
pub fn write_stderr(data: &[u8]) {
    write_fd(2, data);
}

/// Write to a standard stream by descriptor (1 = stdout, 2 = stderr).
#[inline(never)]
pub fn write_std(fd: u64, data: &[u8]) {
    if fd == 2 {
        write_stderr(data)
    } else {
        write_stdout(data)
    }
}

pub fn flush_std(fd: u64) {
    if fd != 2 {
        flush_stdout();
    }
}

/// C stdio flushes line-buffered output streams before reading from a
/// terminal; do the same so prompts appear.
fn before_read() {
    if out().line_buffered == Some(true) {
        flush_stdout();
    }
}

fn fill_stdin() -> bool {
    let i = inp();
    if i.eof {
        return false;
    }
    if i.pos >= i.buf.len() {
        i.buf.clear();
        i.pos = 0;
    }
    let start = i.buf.len();
    i.buf.resize(start + BUF_CAP, 0);
    loop {
        let n = unsafe { read(0, i.buf.as_mut_ptr().add(start) as *mut std::ffi::c_void, BUF_CAP) };
        if n < 0 && std::io::Error::last_os_error().kind() == std::io::ErrorKind::Interrupted {
            continue;
        }
        let n = if n < 0 { 0 } else { n as usize };
        i.buf.truncate(start + n);
        if n == 0 {
            // Like `clearerr` after EOF in Lean's getLine/read: a later read
            // tries again (a terminal may produce more input).
            return false;
        }
        return true;
    }
}

/// `getLine`: bytes up to and including the next newline (or to EOF).
#[inline(never)]
pub fn read_line_stdin() -> Vec<u8> {
    before_read();
    let mut line = Vec::new();
    loop {
        let i = inp();
        let avail = &i.buf[i.pos..];
        if let Some(k) = avail.iter().position(|&b| b == b'\n') {
            line.extend_from_slice(&avail[..=k]);
            i.pos += k + 1;
            return line;
        }
        line.extend_from_slice(avail);
        i.pos = i.buf.len();
        if !fill_stdin() {
            return line;
        }
    }
}

/// `read n`: up to `n` bytes (fewer only at EOF), like `fread`.
#[inline(never)]
pub fn read_stdin(n: usize) -> Vec<u8> {
    before_read();
    let mut res = Vec::with_capacity(n.min(BUF_CAP));
    while res.len() < n {
        let i = inp();
        let avail = &i.buf[i.pos..];
        let k = avail.len().min(n - res.len());
        res.extend_from_slice(&avail[..k]);
        i.pos += k;
        if res.len() < n && !fill_stdin() {
            break;
        }
    }
    res
}

/// Flush and terminate the process.
pub fn exit(code: i32) -> ! {
    flush_stdout();
    let _ = std::io::stderr().flush();
    std::process::exit(code)
}
