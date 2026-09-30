//! Standard streams with glibc stdio behaviour.
//!
//! Native Lean writes through C `FILE*`s. stdout is buffered like glibc's
//! stdio: the buffer is `st_blksize` bytes (at most `BUFSIZ` = 8192; 4096 for
//! pipes and files on Linux), line buffered on a terminal; a write that does
//! not fit fills the buffer, flushes it, writes whole blocks directly and
//! buffers the rest (`_IO_new_file_xsputn`). So stdout reaches the file
//! descriptor in exactly the same chunks as natively, and interleaves with
//! the unbuffered stderr at the same points. stdout is flushed when the
//! process exits.
//!
//! Errors (a closed descriptor, `EPIPE`, ...) are reported through the
//! runtime's last-error slot (`fs::ok()` & co.), so lean2rr can turn them
//! into Lean's `IO.Error`s exactly as `lean_io_prim_handle_*` do.
//!
//! The runtime is single-threaded (Reussir reference counts are not atomic),
//! so the global state is a plain cell. It lives here, in the one `leanrt`
//! crate every texture links against, so all output goes through one buffer.

use crate::fs::{set_err, set_ok};
use std::cell::UnsafeCell;

struct Global<T>(UnsafeCell<T>);
unsafe impl<T> Sync for Global<T> {}

/// glibc's `BUFSIZ`.
const BUFSIZ: usize = 8192;

/// The write side of a glibc `FILE`.
pub(crate) struct WBuf {
    pub(crate) buf: Vec<u8>,
    /// The buffer size (glibc's block size); 0 until the first write.
    pub(crate) size: usize,
    pub(crate) line_buffered: bool,
    /// glibc's `_IO_CURRENTLY_PUTTING`: the put area is set up. Until then
    /// (and after reading) a write finds no room in the buffer.
    pub(crate) putting: bool,
}

impl WBuf {
    pub(crate) const fn new() -> WBuf {
        WBuf { buf: Vec::new(), size: 0, line_buffered: false, putting: false }
    }
}

static OUT: Global<WBuf> = Global(UnsafeCell::new(WBuf::new()));

struct In {
    buf: Vec<u8>,
    pos: usize,
    /// Whether stdin is a terminal (line buffered): 0 unknown, 1 yes, 2 no.
    tty: u8,
    /// The `FILE`'s sticky end-of-file and error indicators (see
    /// `fs::FileHandle`; Lean's stdin stream uses the same primitives).
    eof: bool,
    err: bool,
}

static IN: Global<In> =
    Global(UnsafeCell::new(In { buf: Vec::new(), pos: 0, tty: 0, eof: false, err: false }));

#[inline]
fn out() -> &'static mut WBuf {
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
    fn __errno_location() -> *mut i32;
}

fn errno_now() -> i32 {
    unsafe { *__errno_location() }
}

/// What C's `exit` does with stdio: flush every open file (most recently
/// opened first), then stdout.
extern "C" fn flush_at_exit() {
    crate::fs::flush_all();
    let _ = flush_stdout_result();
}

static AT_EXIT: Global<bool> = Global(UnsafeCell::new(false));

/// Register the flush at exit (once).
pub(crate) fn flush_at_exit_registered() {
    let r = unsafe { &mut *AT_EXIT.0.get() };
    if !*r {
        *r = true;
        unsafe { atexit(flush_at_exit) };
    }
}

/// Whether a file descriptor is a terminal.
pub fn is_tty(fd: u64) -> bool {
    unsafe { isatty(fd as i32) == 1 }
}

/// Write everything (like `_IO_new_file_write`); `Err(errno)` on failure.
pub(crate) fn write_fd(fd: i32, mut data: &[u8]) -> Result<(), i32> {
    while !data.is_empty() {
        let n = unsafe { write(fd, data.as_ptr() as *const std::ffi::c_void, data.len()) };
        if n < 0 {
            let e = errno_now();
            if e == 4 {
                continue;
            }
            return Err(e);
        }
        data = &data[n as usize..];
    }
    Ok(())
}

/// `_IO_file_doallocate`: the block size of a descriptor's `FILE` buffer
/// (`st_blksize`, at most `BUFSIZ`) and whether it is line buffered (a
/// terminal).
#[cold]
#[inline(never)]
pub(crate) fn block_size(fd: i32) -> (usize, bool) {
    use std::os::unix::fs::{FileTypeExt, MetadataExt};
    use std::os::unix::io::FromRawFd;
    let f = std::mem::ManuallyDrop::new(unsafe { std::fs::File::from_raw_fd(fd) });
    let mut size = BUFSIZ;
    let mut line = false;
    if let Ok(m) = f.metadata() {
        if m.file_type().is_char_device() && is_tty(fd as u64) {
            line = true;
        }
        let b = m.blksize() as usize;
        if b > 0 && b < BUFSIZ {
            size = b;
        }
    }
    (size, line)
}

#[cold]
#[inline(never)]
fn init_wbuf(fd: i32, w: &mut WBuf) {
    let (size, line) = block_size(fd);
    w.size = size;
    w.line_buffered = line;
    w.buf = crate::alloc::vec_with_capacity(size);
}

/// Flush a buffer; the buffered bytes are dropped even on failure (as
/// glibc's `new_do_write` resets the buffer).
fn flush_wbuf(fd: i32, w: &mut WBuf) -> Result<(), i32> {
    if w.buf.is_empty() {
        return Ok(());
    }
    let r = write_fd(fd, &w.buf);
    w.buf.clear();
    r
}

/// `fwrite` (`_IO_new_file_xsputn`): fill the free space of the buffer
/// (only up to the last newline when line buffered, then flush), and if
/// that is not all, flush, write whole blocks directly and buffer the rest
/// (flushing it up to its last newline when line buffered, as
/// `_IO_default_xsputn` does character by character).
pub(crate) fn xsputn(fd: i32, w: &mut WBuf, data: &[u8]) -> Result<(), i32> {
    let n = data.len();
    if n == 0 {
        return Ok(());
    }
    if w.size == 0 {
        init_wbuf(fd, w);
    }
    let mut count = if w.putting { w.size - w.buf.len() } else { 0 };
    let mut must_flush = false;
    if w.line_buffered && w.putting && count >= n {
        if let Some(p) = data.iter().rposition(|&c| c == b'\n') {
            count = p + 1;
            must_flush = true;
        }
    }
    let c = count.min(n);
    w.buf.extend_from_slice(&data[..c]);
    let rest = &data[c..];
    if !rest.is_empty() || must_flush {
        w.putting = true;
        if let Err(e) = flush_wbuf(fd, w) {
            // `fwrite` reports success when everything was buffered and
            // only the flush failed (glibc's `written == EOF` case).
            return if rest.is_empty() { Ok(()) } else { Err(e) };
        }
        let block = w.size;
        let direct = rest.len() - if block >= 128 { rest.len() % block } else { 0 };
        if direct > 0 {
            write_fd(fd, &rest[..direct])?;
        }
        let tail = &rest[direct..];
        if w.line_buffered {
            if let Some(k) = tail.iter().rposition(|&c| c == b'\n') {
                w.buf.extend_from_slice(&tail[..=k]);
                flush_wbuf(fd, w)?;
                w.buf.extend_from_slice(&tail[k + 1..]);
                return Ok(());
            }
        }
        w.buf.extend_from_slice(tail);
    }
    Ok(())
}

fn flush_stdout_result() -> Result<(), i32> {
    flush_wbuf(1, out())
}

/// Write all buffered stdout bytes (ignoring errors, as at exit).
#[inline(never)]
pub fn flush_stdout() {
    let _ = flush_stdout_result();
}

/// `fwrite` to stdout.
#[inline(never)]
fn write_stdout_result(data: &[u8]) -> Result<(), i32> {
    let o = out();
    if o.size == 0 {
        flush_at_exit_registered();
    }
    xsputn(1, o, data)
}

/// Append bytes to stdout, recording the outcome in the last-error slot.
#[inline(never)]
pub fn write_stdout(data: &[u8]) {
    match write_stdout_result(data) {
        Ok(()) => set_ok(),
        Err(e) => set_err(e, None),
    }
}

/// stderr is unbuffered (as C's `stderr`); errors are recorded.
#[inline(never)]
pub fn write_stderr(data: &[u8]) {
    match write_fd(2, data) {
        Ok(()) => set_ok(),
        Err(e) => set_err(e, None),
    }
}

/// Runtime diagnostics (panics, traces, timings) to stderr: errors are
/// ignored and the last-error slot is left alone.
#[inline(never)]
pub fn eprint(data: &[u8]) {
    let _ = write_fd(2, data);
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

/// Writing to stdin or reading from stdout/stderr (`fd`): `EBADF`, as
/// glibc's `fwrite`/`fread` on a stream opened in the other direction, which
/// also sets the stream's error indicator (only stdin's matters: see
/// `read_line_stdin`).
pub fn wrong_direction(fd: u64) {
    if fd == 0 {
        inp().err = true;
    }
    set_c_errno(9);
    set_err(9, None)
}

fn set_c_errno(e: i32) {
    unsafe { *__errno_location() = e }
}

/// `IO.FS.Stream.flush` of a standard stream (`fflush`). Flushing stdin
/// only drops glibc's read-ahead (seeking back), which is invisible here.
pub fn flush_std(fd: u64) {
    let r = if fd == 1 { flush_stdout_result() } else { Ok(()) };
    match r {
        Ok(()) => set_ok(),
        Err(e) => set_err(e, None),
    }
}

/// Refill the stdin buffer: `Ok(false)` at end of file (a later read tries
/// again, as after Lean's `clearerr`). As glibc's `_IO_new_file_underflow`,
/// reading a line-buffered (terminal) stdin first flushes a line-buffered
/// stdout, so prompts appear.
fn fill_stdin() -> Result<bool, i32> {
    let i = inp();
    if i.tty == 0 {
        i.tty = if block_size(0).1 { 1 } else { 2 };
    }
    if i.tty == 1 && out().line_buffered {
        let _ = flush_stdout_result();
    }
    if i.pos >= i.buf.len() {
        i.buf.clear();
        i.pos = 0;
    }
    let start = i.buf.len();
    i.buf.resize(start + BUFSIZ, 0);
    loop {
        let n = unsafe { read(0, i.buf.as_mut_ptr().add(start) as *mut std::ffi::c_void, BUFSIZ) };
        if n < 0 {
            let e = errno_now();
            if e == 4 {
                continue;
            }
            i.buf.truncate(start);
            return Err(e);
        }
        i.buf.truncate(start + n as usize);
        return Ok(n > 0);
    }
}

/// Make buffered stdin available: `false` at (sticky) end of file or after
/// a read error (which sets the error indicator).
fn more_stdin() -> bool {
    let i = inp();
    if i.pos < i.buf.len() {
        return true;
    }
    if i.eof {
        return false;
    }
    match fill_stdin() {
        Ok(true) => true,
        Ok(false) => {
            inp().eof = true;
            false
        }
        Err(_) => {
            inp().err = true;
            false
        }
    }
}

/// `getLine` (as `fs::get_line`): bytes up to and including the next
/// newline, or to end of file or a read error; if the error indicator is
/// set the line is lost and the error reported with the current `errno`.
#[inline(never)]
pub fn read_line_stdin() -> Vec<u8> {
    let mut line = Vec::new();
    while more_stdin() {
        let i = inp();
        let avail = &i.buf[i.pos..];
        if let Some(k) = avail.iter().position(|&b| b == b'\n') {
            line.extend_from_slice(&avail[..=k]);
            i.pos += k + 1;
            break;
        }
        line.extend_from_slice(avail);
        i.pos = i.buf.len();
    }
    let i = inp();
    if i.err {
        set_err(errno_now(), None);
        return Vec::new();
    }
    i.eof = false;
    set_ok();
    line
}

/// `read n` (as `fs::read_bytes`): up to `n` bytes; with nothing read, end
/// of file clears both indicators and is a success, otherwise the error is
/// reported with the current `errno`.
#[inline(never)]
pub fn read_stdin(n: usize) -> Vec<u8> {
    let mut res = Vec::with_capacity(n.min(BUFSIZ));
    if n == 0 {
        set_ok();
        return res;
    }
    while res.len() < n && more_stdin() {
        let i = inp();
        let avail = &i.buf[i.pos..];
        let k = avail.len().min(n - res.len());
        res.extend_from_slice(&avail[..k]);
        i.pos += k;
    }
    if res.is_empty() {
        let i = inp();
        if !i.eof {
            set_err(errno_now(), None);
            return res;
        }
        i.eof = false;
        i.err = false;
    }
    set_ok();
    res
}

/// Flush and terminate the process.
pub fn exit(code: i32) -> ! {
    flush_at_exit();
    std::process::exit(code)
}
