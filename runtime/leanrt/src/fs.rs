//! Files (`IO.FS.Handle`) and file-system operations, following
//! `src/runtime/io.cpp`.
//!
//! A handle is a shared, mutable, buffered file (`FILE*` in Lean). The
//! Reussir-visible type is `Rc<Box<dyn Any>>` (spellable with std and
//! reussir_rt only); the box holds a [`FileHandle`]. Handles are closed when
//! the last reference goes away (Lean's handle finalizer `fclose`s).
//!
//! Errors: every primitive records its outcome in a global "last error"
//! (errno 0 = success, plus the file name Lean's C code attaches). lean2rr's
//! glue checks `ok()` after the call and otherwise builds the `IO.Error`
//! from `error_kind()` (which `lean_mk_io_error_*` constructor
//! `decode_io_error` would use), `errno()`, `error_fname()` and
//! `error_details()` (`strerror`, or Lean's own message).
//!
//! The operations Lean implements with libuv (`metadata`, `symlinkMetadata`,
//! `removeFile`, `hardLink`, `createTempFile`, `createTempDir`) report their
//! errors as `decode_uv_error` does: the error code is libuv's negated errno
//! (so `4294967294` for `ENOENT` as a `UInt32`), the message is
//! `uv_strerror`'s, and errnos libuv does not map are `otherError`s.
//!
//! Buffering follows glibc's `FILE`: a write buffer of `st_blksize` bytes
//! (at most `BUFSIZ`), line buffered on a terminal, filled and flushed as
//! `_IO_new_file_xsputn` does, so other readers of the file see the same
//! bytes at the same points as natively. Open handles are flushed when the
//! process exits (as C's `exit` flushes every `FILE`).

use crate::string::{from_bytes, from_bytes_lossy, LStr};
use reussir_rt::rc::Rc;
use std::any::Any;
use std::cell::UnsafeCell;
use std::ffi::c_void;

pub type LHandle = Rc<Box<dyn Any>>;

struct Global<T>(UnsafeCell<T>);
unsafe impl<T> Sync for Global<T> {}

struct LastError {
    errno: i32,
    /// Reported by a libuv-based operation (`decode_uv_error`).
    uv: bool,
    fname: Option<Vec<u8>>,
    details: Option<Vec<u8>>,
}

static LAST: Global<LastError> =
    Global(UnsafeCell::new(LastError { errno: 0, uv: false, fname: None, details: None }));

fn last() -> &'static mut LastError {
    unsafe { &mut *LAST.0.get() }
}

pub(crate) fn set_ok() {
    let l = last();
    l.errno = 0;
    l.uv = false;
    l.fname = None;
    l.details = None;
}

pub(crate) fn set_err(errno: i32, fname: Option<&[u8]>) {
    let l = last();
    l.errno = errno;
    l.uv = false;
    l.fname = fname.map(|f| f.to_vec());
    l.details = None;
}

/// An error of a libuv-based operation (`errno` is the positive errno).
fn set_err_uv(errno: i32, fname: Option<&[u8]>) {
    set_err(errno, fname);
    last().uv = true;
}

/// An error with Lean's own message instead of `strerror`'s.
fn set_err_msg(errno: i32, fname: Option<&[u8]>, details: &[u8]) {
    set_err(errno, fname);
    last().details = Some(details.to_vec());
}

/// The errno slot value of a user error (`io_result_mk_error(msg)`).
const USER_ERROR: i32 = -1;

/// Lean's `IO.userError msg` (error kind 23; `msg` is `error_details()`).
fn set_user_error(msg: &[u8]) {
    set_err_msg(USER_ERROR, None, msg)
}

extern "C" {
    fn open(path: *const std::ffi::c_char, flags: i32, ...) -> i32;
    fn close(fd: i32) -> i32;
    fn read(fd: i32, buf: *mut c_void, n: usize) -> isize;
    fn lseek(fd: i32, off: i64, whence: i32) -> i64;
    fn ftruncate(fd: i32, len: i64) -> i32;
    fn flock(fd: i32, op: i32) -> i32;
    fn isatty(fd: i32) -> i32;
    fn unlink(path: *const std::ffi::c_char) -> i32;
    fn rename(from: *const std::ffi::c_char, to: *const std::ffi::c_char) -> i32;
    fn mkdir(path: *const std::ffi::c_char, mode: u32) -> i32;
    fn rmdir(path: *const std::ffi::c_char) -> i32;
    fn chmod(path: *const std::ffi::c_char, mode: u32) -> i32;
    fn link(from: *const std::ffi::c_char, to: *const std::ffi::c_char) -> i32;
    fn chdir(path: *const std::ffi::c_char) -> i32;
    fn mkostemp(template: *mut std::ffi::c_char, flags: i32) -> i32;
    fn mkdtemp(template: *mut std::ffi::c_char) -> *mut std::ffi::c_char;
    fn strerror(e: i32) -> *const std::ffi::c_char;
    fn __errno_location() -> *mut i32;
}

fn errno_now() -> i32 {
    unsafe { *__errno_location() }
}

const O_RDONLY: i32 = 0;
const O_WRONLY: i32 = 1;
const O_RDWR: i32 = 2;
const O_CREAT: i32 = 0o100;
const O_EXCL: i32 = 0o200;
const O_TRUNC: i32 = 0o1000;
const O_APPEND: i32 = 0o2000;
const O_CLOEXEC: i32 = 0o2000000;
const EINVAL: i32 = 22;
const LOCK_SH: i32 = 1;
const LOCK_EX: i32 = 2;
const LOCK_NB: i32 = 4;
const LOCK_UN: i32 = 8;
const EWOULDBLOCK: i32 = 11;

/// A path as a NUL-terminated C string, or the "embedded NUL" error of
/// `mk_embedded_nul_error` (invalid argument, EINVAL, own message).
fn c_path(p: &[u8]) -> Option<Vec<u8>> {
    if p.contains(&0) {
        set_err_msg(EINVAL, Some(p), b"string contains NUL bytes");
        return None;
    }
    let mut v = p.to_vec();
    v.push(0);
    Some(v)
}

pub struct FileHandle {
    fd: i32,
    /// Opened for reading / for writing (glibc's `_IO_NO_READS` and
    /// `_IO_NO_WRITES`: the other direction fails at once with `EBADF`).
    readable: bool,
    writable: bool,
    rbuf: Vec<u8>,
    rpos: usize,
    w: crate::io::WBuf,
    /// C's sticky end-of-file indicator (`feof`), cleared by `clearerr`
    /// (Lean's read and getLine clear it when they return at end of file)
    /// and by seeking.
    eof: bool,
    /// C's sticky error indicator (`ferror`), set by any failed read or
    /// write. Lean's `getLine` checks it after reading: once set, every
    /// `getLine` fails (with the current `errno`); `read` clears it only
    /// when it returns at end of file.
    err: bool,
}

const EBADF: i32 = 9;

fn set_c_errno(e: i32) {
    unsafe { *__errno_location() = e }
}

const BUF: usize = 1 << 16;

/// The open handles, oldest first, flushed at exit.
static OPEN: Global<Vec<usize>> = Global(UnsafeCell::new(Vec::new()));

/// Flush every open handle, most recently opened first (as glibc's
/// `_IO_flush_all` at `exit`), ignoring errors.
pub(crate) fn flush_all() {
    let open = unsafe { &*OPEN.0.get() };
    for &p in open.iter().rev() {
        let _ = unsafe { &mut *(p as *mut FileHandle) }.flush();
    }
}

impl FileHandle {
    /// A failed operation: sets the error indicator.
    fn failed<T>(&mut self, e: i32) -> Result<T, i32> {
        self.err = true;
        Err(e)
    }

    fn flush(&mut self) -> Result<(), i32> {
        if self.w.buf.is_empty() {
            return Ok(());
        }
        // The buffer is dropped even when the write fails (glibc).
        let r = crate::io::write_fd(self.fd, &self.w.buf);
        self.w.buf.clear();
        match r {
            Ok(()) => Ok(()),
            Err(e) => self.failed(e),
        }
    }

    fn write_bytes(&mut self, b: &[u8]) -> Result<(), i32> {
        if !self.writable {
            if b.is_empty() {
                return Ok(());
            }
            set_c_errno(EBADF);
            return self.failed(EBADF);
        }
        if !self.rbuf.is_empty() {
            // C stdio needs a seek between reading and writing; drop the
            // read-ahead and position the file where the reader was.
            let back = (self.rbuf.len() - self.rpos) as i64;
            unsafe { lseek(self.fd, -back, 1) };
            self.rbuf.clear();
            self.rpos = 0;
        }
        match crate::io::xsputn(self.fd, &mut self.w, b) {
            Ok(()) => Ok(()),
            Err(e) => self.failed(e),
        }
    }

    /// Fill the read buffer; `Ok(false)` at end of file.
    fn fill(&mut self) -> Result<bool, i32> {
        if !self.readable {
            set_c_errno(EBADF);
            return self.failed(EBADF);
        }
        if !self.w.buf.is_empty() {
            self.flush()?;
        }
        // Switching to reading: the next write finds no room (glibc).
        self.w.putting = false;
        self.rbuf.clear();
        self.rpos = 0;
        self.rbuf.resize(BUF, 0);
        loop {
            let n = unsafe { read(self.fd, self.rbuf.as_mut_ptr() as *mut c_void, BUF) };
            if n < 0 {
                let e = errno_now();
                if e == 4 {
                    continue;
                }
                self.rbuf.clear();
                return self.failed(e);
            }
            self.rbuf.truncate(n as usize);
            return Ok(n > 0);
        }
    }
}

impl Drop for FileHandle {
    fn drop(&mut self) {
        if self.fd >= 0 {
            let open = unsafe { &mut *OPEN.0.get() };
            let me = self as *mut FileHandle as usize;
            if let Some(i) = open.iter().rposition(|&p| p == me) {
                open.remove(i);
            }
            let _ = self.flush();
            unsafe { close(self.fd) };
        }
    }
}

#[inline(always)]
fn fh(h: &LHandle) -> &mut FileHandle {
    // Handles are shared and mutable (like `FILE*`); only this module
    // creates them, always holding a `FileHandle`.
    let b: &Box<dyn Any> = h;
    unsafe { &mut *(*(&**b as *const dyn Any as *const UnsafeCell<FileHandle>)).get() }
}

fn mk(fd: i32, readable: bool, writable: bool) -> LHandle {
    let b = Box::new(UnsafeCell::new(FileHandle {
        fd,
        readable,
        writable,
        rbuf: Vec::new(),
        rpos: 0,
        w: crate::io::WBuf::new(),
        eof: false,
        err: false,
    }));
    if fd >= 0 {
        crate::io::flush_at_exit_registered();
        unsafe { &mut *OPEN.0.get() }.push(b.get() as usize);
    }
    Rc::new(b as Box<dyn Any>)
}

/// `IO.FS.Handle.mk path mode` (`read`, `write`, `writeNew`, `readWrite`,
/// `append` = 0..4). On failure the result is a closed handle.
pub fn open_file(path: &[u8], mode: u8) -> LHandle {
    let Some(c) = c_path(path) else { return mk(-1, false, false) };
    let flags = O_CLOEXEC
        | match mode {
            0 => O_RDONLY,
            1 => O_WRONLY | O_CREAT | O_TRUNC,
            2 => O_WRONLY | O_CREAT | O_TRUNC | O_EXCL,
            3 => O_RDWR,
            _ => O_WRONLY | O_CREAT | O_APPEND,
        };
    let fd = unsafe { open(c.as_ptr() as *const std::ffi::c_char, flags, 0o666 as std::ffi::c_uint) };
    if fd < 0 {
        set_err(errno_now(), Some(path));
    } else {
        set_ok();
    }
    mk(fd, mode == 0 || mode == 3, mode != 0)
}

fn outcome(r: Result<(), i32>) {
    match r {
        Ok(()) => set_ok(),
        Err(e) => set_err(e, None),
    }
}

pub fn put_str(h: &LHandle, s: &[u8]) {
    outcome(fh(h).write_bytes(s))
}

pub fn flush(h: &LHandle) {
    outcome(fh(h).flush())
}

/// Make buffered input available: `false` at end of file (sticky: nothing
/// is read once it was seen) or after a read error (which sets the error
/// indicator), as `getc`/`fread` stop.
fn more_input(f: &mut FileHandle) -> bool {
    if f.rpos < f.rbuf.len() {
        return true;
    }
    if f.eof {
        return false;
    }
    match f.fill() {
        Ok(true) => true,
        Ok(false) => {
            f.eof = true;
            false
        }
        Err(_) => false,
    }
}

/// `Handle.read n` (`lean_io_prim_handle_read`): `fread` up to `n` bytes;
/// any bytes read are a success. With nothing read, end of file clears
/// both indicators (`clearerr`) and is a success, otherwise the error is
/// reported with the current `errno`.
pub fn read_bytes(h: &LHandle, n: u64) -> Vec<u8> {
    let f = fh(h);
    let n = n as usize;
    let mut out = Vec::with_capacity(n.min(BUF));
    if n == 0 {
        set_ok();
        return out;
    }
    while out.len() < n && more_input(f) {
        let k = (f.rbuf.len() - f.rpos).min(n - out.len());
        out.extend_from_slice(&f.rbuf[f.rpos..f.rpos + k]);
        f.rpos += k;
    }
    if out.is_empty() {
        if !f.eof {
            set_err(errno_now(), None);
            return out;
        }
        f.eof = false;
        f.err = false;
    }
    set_ok();
    out
}

/// `Handle.isEof` (`feof`; cannot fail).
pub fn is_eof(h: &LHandle) -> bool {
    set_ok();
    fh(h).eof
}

/// `Handle.getLine` (`lean_io_prim_handle_get_line`): characters up to and
/// including `\n`, or to end of file or a read error. Then, if the error
/// indicator is set (now or by any earlier failure) the line is lost and
/// the error reported with the current `errno`; otherwise end of file is
/// cleared.
pub fn get_line(h: &LHandle) -> LStr {
    let f = fh(h);
    let mut line = Vec::new();
    while more_input(f) {
        let avail = &f.rbuf[f.rpos..];
        if let Some(k) = avail.iter().position(|&b| b == b'\n') {
            line.extend_from_slice(&avail[..=k]);
            f.rpos += k + 1;
            break;
        }
        line.extend_from_slice(avail);
        f.rpos = f.rbuf.len();
    }
    if f.err {
        set_err(errno_now(), None);
        return from_bytes(b"");
    }
    f.eof = false;
    set_ok();
    from_bytes_lossy(&line)
}

/// `Handle.isTty` (cannot fail; records success so a fallible-glue caller
/// sees no stale error).
pub fn is_tty(h: &LHandle) -> bool {
    set_ok();
    unsafe { isatty(fh(h).fd) == 1 }
}

pub fn rewind(h: &LHandle) {
    let f = fh(h);
    if let Err(e) = f.flush() {
        return set_err(e, None);
    }
    f.rbuf.clear();
    f.rpos = 0;
    f.eof = false;
    f.w.putting = false;
    if unsafe { lseek(f.fd, 0, 0) } < 0 { set_err(errno_now(), None) } else { set_ok() }
}

/// `Handle.truncate`: truncate at the current position.
pub fn truncate(h: &LHandle) {
    let f = fh(h);
    if let Err(e) = f.flush() {
        return set_err(e, None);
    }
    let back = (f.rbuf.len() - f.rpos) as i64;
    let pos = unsafe { lseek(f.fd, 0, 1) } - back;
    if unsafe { ftruncate(f.fd, pos) } != 0 { set_err(errno_now(), None) } else { set_ok() }
}

pub fn lock(h: &LHandle, exclusive: bool) {
    let op = if exclusive { LOCK_EX } else { LOCK_SH };
    if unsafe { flock(fh(h).fd, op) } != 0 { set_err(errno_now(), None) } else { set_ok() }
}

/// `Handle.tryLock`: `false` when the lock is held elsewhere.
pub fn try_lock(h: &LHandle, exclusive: bool) -> bool {
    let op = (if exclusive { LOCK_EX } else { LOCK_SH }) | LOCK_NB;
    if unsafe { flock(fh(h).fd, op) } == 0 {
        set_ok();
        true
    } else {
        let e = errno_now();
        if e == EWOULDBLOCK { set_ok() } else { set_err(e, None) }
        false
    }
}

pub fn unlock(h: &LHandle) {
    if unsafe { flock(fh(h).fd, LOCK_UN) } != 0 { set_err(errno_now(), None) } else { set_ok() }
}

fn path_op(p: &[u8], f: impl FnOnce(*const std::ffi::c_char) -> i32) {
    let Some(c) = c_path(p) else { return };
    if f(c.as_ptr() as *const std::ffi::c_char) != 0 { set_err(errno_now(), Some(p)) } else { set_ok() }
}

/// `IO.FS.removeFile` (libuv's `uv_fs_unlink` natively).
pub fn remove_file(p: &[u8]) {
    let Some(c) = c_path(p) else { return };
    if unsafe { unlink(c.as_ptr() as *const std::ffi::c_char) } != 0 {
        set_err_uv(errno_now(), Some(p))
    } else {
        set_ok()
    }
}

pub fn create_dir(p: &[u8]) {
    path_op(p, |c| unsafe { mkdir(c, 0o777) })
}

pub fn remove_dir(p: &[u8]) {
    path_op(p, |c| unsafe { rmdir(c) })
}

/// `IO.currentDir`: `getcwd`; a failure is Lean's user error.
pub fn current_dir() -> LStr {
    match std::env::current_dir() {
        Ok(p) => {
            set_ok();
            from_bytes_lossy(std::os::unix::ffi::OsStrExt::as_bytes(p.as_os_str()))
        }
        Err(_) => {
            set_user_error(b"failed to retrieve current working directory");
            from_bytes(b"")
        }
    }
}

/// `IO.appPath`: `/proc/self/exe`; a failure is Lean's user error.
pub fn app_path() -> LStr {
    match std::fs::read_link("/proc/self/exe") {
        Ok(p) => {
            set_ok();
            from_bytes_lossy(std::os::unix::ffi::OsStrExt::as_bytes(p.as_os_str()))
        }
        Err(_) => {
            set_user_error(b"failed to locate application");
            from_bytes(b"")
        }
    }
}

/// `IO.Process.getCurrentDir`: `getcwd`; errors are decoded without a file.
pub fn process_current_dir() -> LStr {
    match std::env::current_dir() {
        Ok(p) => {
            set_ok();
            from_bytes_lossy(std::os::unix::ffi::OsStrExt::as_bytes(p.as_os_str()))
        }
        Err(e) => {
            set_err(e.raw_os_error().unwrap_or(EINVAL), None);
            from_bytes(b"")
        }
    }
}

/// `IO.Process.setCurrentDir`: `chdir` of the path up to its first NUL
/// (Lean passes `string_cstr` unchecked); the error names the whole path.
pub fn set_current_dir(p: &[u8]) {
    let cut = p.iter().position(|&b| b == 0).unwrap_or(p.len());
    let mut c = p[..cut].to_vec();
    c.push(0);
    if unsafe { chdir(c.as_ptr() as *const std::ffi::c_char) } != 0 {
        set_err(errno_now(), Some(p))
    } else {
        set_ok()
    }
}

/// libuv's `uv_os_tmpdir`: `TMPDIR`, `TMP`, `TEMP` or `TEMPDIR` (the first
/// set and non-empty), else `/tmp`, without a trailing slash; Lean then
/// appends `/tmp.XXXXXXXX`.
fn temp_template() -> Vec<u8> {
    use std::os::unix::ffi::OsStrExt;
    let mut dir = b"/tmp".to_vec();
    for v in ["TMPDIR", "TMP", "TEMP", "TEMPDIR"] {
        if let Some(d) = std::env::var_os(v) {
            if !d.is_empty() {
                dir = d.as_bytes().to_vec();
                break;
            }
        }
    }
    if dir.len() > 1 && dir.last() == Some(&b'/') {
        dir.pop();
    }
    if dir.last() != Some(&b'/') {
        dir.push(b'/');
    }
    dir.extend_from_slice(b"tmp.XXXXXXXX\0");
    dir
}

/// The path of the file the last `create_temp_file` created.
static TEMP_PATH: Global<Vec<u8>> = Global(UnsafeCell::new(Vec::new()));

/// `IO.FS.createTempFile`: a new file (`mkostemp`, as libuv) opened for
/// reading and writing; its path is `temp_file_path()`. Errors are libuv's,
/// without a file name.
pub fn create_temp_file() -> LHandle {
    let mut t = temp_template();
    let fd = unsafe { mkostemp(t.as_mut_ptr() as *mut std::ffi::c_char, O_CLOEXEC) };
    t.pop();
    if fd < 0 {
        set_err_uv(errno_now(), None);
        unsafe { *TEMP_PATH.0.get() = Vec::new() };
        return mk(-1, false, false);
    }
    set_ok();
    unsafe { *TEMP_PATH.0.get() = t };
    mk(fd, true, true)
}

pub fn temp_file_path() -> LStr {
    from_bytes(unsafe { &*TEMP_PATH.0.get() })
}

/// `IO.FS.createTempDir` (`mkdtemp`, as libuv).
pub fn create_temp_dir() -> LStr {
    let mut t = temp_template();
    let r = unsafe { mkdtemp(t.as_mut_ptr() as *mut std::ffi::c_char) };
    t.pop();
    if r.is_null() {
        set_err_uv(errno_now(), None);
        return from_bytes(b"");
    }
    set_ok();
    from_bytes(&t)
}

pub fn set_access_rights(p: &[u8], mode: u32) {
    path_op(p, |c| unsafe { chmod(c, mode) })
}

/// `IO.FS.rename`; the error names both files as Lean does.
pub fn rename_file(from: &[u8], to: &[u8]) {
    let Some(a) = c_path(from) else { return };
    let Some(b) = c_path(to) else { return };
    if unsafe { rename(a.as_ptr() as *const std::ffi::c_char, b.as_ptr() as *const std::ffi::c_char) } != 0 {
        let mut both = from.to_vec();
        both.extend_from_slice(b" and/or ");
        both.extend_from_slice(to);
        set_err(errno_now(), Some(&both));
    } else {
        set_ok()
    }
}

/// `IO.FS.hardLink` (libuv's `uv_fs_link` natively; the error names the
/// original).
pub fn hard_link(from: &[u8], to: &[u8]) {
    let Some(a) = c_path(from) else { return };
    let Some(b) = c_path(to) else { return };
    if unsafe { link(a.as_ptr() as *const std::ffi::c_char, b.as_ptr() as *const std::ffi::c_char) } != 0 {
        set_err_uv(errno_now(), Some(from))
    } else {
        set_ok()
    }
}

/// A path as an `OsStr` (Lean strings are valid UTF-8; NULs are rejected
/// first by `c_path`).
fn os_path(p: &[u8]) -> &std::path::Path {
    std::path::Path::new(<std::ffi::OsStr as std::os::unix::ffi::OsStrExt>::from_bytes(p))
}

/// `IO.FS.realPath`: any failure of `realpath` is Lean's "file not found"
/// (`ENOENT`, empty message).
pub fn real_path(p: &[u8]) -> LStr {
    if c_path(p).is_none() {
        return from_bytes(p);
    }
    match std::fs::canonicalize(os_path(p)) {
        Ok(r) => {
            set_ok();
            from_bytes_lossy(std::os::unix::ffi::OsStrExt::as_bytes(r.as_os_str()))
        }
        Err(_) => {
            set_err_msg(2, Some(p), b"");
            from_bytes(p)
        }
    }
}

/// Entry names of a directory in `readdir` order, without `.` and `..`.
pub fn read_dir(p: &[u8]) -> Vec<LStr> {
    if c_path(p).is_none() {
        return Vec::new();
    }
    match std::fs::read_dir(os_path(p)) {
        Ok(it) => {
            set_ok();
            it.filter_map(|e| e.ok())
                .map(|e| from_bytes_lossy(std::os::unix::ffi::OsStrExt::as_bytes(e.file_name().as_os_str())))
                .collect()
        }
        Err(e) => {
            set_err(e.raw_os_error().unwrap_or(EINVAL), Some(p));
            Vec::new()
        }
    }
}

/// `System.FilePath.metadata` fields: accessed (sec as an i64 bit pattern,
/// nsec), modified (sec, nsec), byte size, file type (0 dir, 1 file,
/// 2 symlink, 3 other), number of hard links. Errors are libuv's
/// (`uv_fs_stat`/`uv_fs_lstat` natively).
pub fn metadata(p: &[u8], follow: bool) -> [u64; 7] {
    use std::os::unix::fs::MetadataExt;
    if c_path(p).is_none() {
        return [0; 7];
    }
    let s = os_path(p);
    let m = if follow { std::fs::metadata(s) } else { std::fs::symlink_metadata(s) };
    match m {
        Ok(m) => {
            set_ok();
            let ft = m.file_type();
            let t = if ft.is_dir() { 0 } else if ft.is_file() { 1 } else if ft.is_symlink() { 2 } else { 3 };
            [m.atime() as u64, m.atime_nsec() as u64, m.mtime() as u64, m.mtime_nsec() as u64, m.size(), t, m.nlink()]
        }
        Err(e) => {
            set_err_uv(e.raw_os_error().unwrap_or(EINVAL), Some(p));
            [0; 7]
        }
    }
}

// ---- error decoding (`decode_io_error`/`decode_uv_error` in io.cpp) ----

pub fn ok() -> bool {
    last().errno == 0
}

/// The error code of the last error: the errno, or libuv's negated errno
/// (as a `UInt32` bit pattern) for libuv-based operations.
pub fn errno() -> u32 {
    let l = last();
    if l.errno == USER_ERROR {
        0
    } else if l.uv {
        l.errno.wrapping_neg() as u32
    } else {
        l.errno as u32
    }
}

pub fn error_fname() -> LStr {
    from_bytes(last().fname.as_deref().unwrap_or(b""))
}

pub fn error_details() -> LStr {
    let l = last();
    match &l.details {
        Some(d) => from_bytes(d),
        None if l.uv => match uv_strerror(l.errno) {
            Some(m) => from_bytes(m.as_bytes()),
            None => from_bytes(format!("Unknown system error {}", -l.errno).as_bytes()),
        },
        None => {
            let p = unsafe { strerror(l.errno) };
            let c = unsafe { std::ffi::CStr::from_ptr(p) };
            from_bytes_lossy(c.to_bytes())
        }
    }
}

/// Which `lean_mk_io_error_*` constructor Lean's `decode_io_error` (or
/// `decode_uv_error`) uses for the last error (see the table in
/// runtime/README.md).
pub fn error_kind() -> u32 {
    let l = last();
    if l.errno == USER_ERROR {
        return 23;
    }
    if l.uv && !uv_maps(l.errno) {
        return 0;
    }
    decode_kind(l.errno, l.fname.is_some())
}

/// Whether `decode_uv_error` has a case for this errno: libuv (1.48) does
/// not map EDOM, ENOEXEC, ENOSTR, ENOLCK, ENOSR, EBADMSG, ECHILD, ENOMSG,
/// EINPROGRESS, EIDRM, ENETRESET, ENOLINK, ETIME or EDEADLK, which are
/// therefore `otherError`s.
fn uv_maps(e: i32) -> bool {
    !matches!(e, 33 | 8 | 60 | 37 | 63 | 74 | 10 | 42 | 115 | 43 | 102 | 67 | 62 | 35)
}

/// libuv's `uv_strerror` for a (positive) errno, as linked into Lean 4.33;
/// `None` for errnos libuv has no name for.
fn uv_strerror(e: i32) -> Option<&'static str> {
    Some(match e {
        1 => "operation not permitted",
        2 => "no such file or directory",
        3 => "no such process",
        4 => "interrupted system call",
        5 => "i/o error",
        6 => "no such device or address",
        7 => "argument list too long",
        9 => "bad file descriptor",
        11 => "resource temporarily unavailable",
        12 => "not enough memory",
        13 => "permission denied",
        14 => "bad address in system call argument",
        16 => "resource busy or locked",
        17 => "file already exists",
        18 => "cross-device link not permitted",
        19 => "no such device",
        20 => "not a directory",
        21 => "illegal operation on a directory",
        22 => "invalid argument",
        23 => "file table overflow",
        24 => "too many open files",
        25 => "inappropriate ioctl for device",
        26 => "text file is busy",
        27 => "file too large",
        28 => "no space left on device",
        29 => "invalid seek",
        30 => "read-only file system",
        31 => "too many links",
        32 => "broken pipe",
        34 => "result too large",
        36 => "name too long",
        38 => "function not implemented",
        39 => "directory not empty",
        40 => "too many symbolic links encountered",
        49 => "protocol driver not attached",
        61 => "no data available",
        64 => "machine is not on the network",
        71 => "protocol error",
        75 => "value too large for defined data type",
        84 => "illegal byte sequence",
        88 => "socket operation on non-socket",
        89 => "destination address required",
        90 => "message too long",
        91 => "protocol wrong type for socket",
        92 => "protocol not available",
        93 => "protocol not supported",
        94 => "socket type not supported",
        95 => "operation not supported on socket",
        97 => "address family not supported",
        98 => "address already in use",
        99 => "address not available",
        100 => "network is down",
        101 => "network is unreachable",
        103 => "software caused connection abort",
        104 => "connection reset by peer",
        105 => "no buffer space available",
        106 => "socket is already connected",
        107 => "socket is not connected",
        108 => "cannot send after transport endpoint shutdown",
        110 => "connection timed out",
        111 => "connection refused",
        112 => "host is down",
        113 => "host is unreachable",
        114 => "connection already in progress",
        121 => "remote I/O error",
        125 => "operation canceled",
        _ => return None,
    })
}

pub fn decode_kind(e: i32, has_fname: bool) -> u32 {
    let file = |no: u32, yes: u32| if has_fname { yes } else { no };
    match e {
        4 => 1,                                                          // EINTR: interrupted
        40 | 36 | 89 | 9 | 33 | 22 | 84 | 8 | 60 | 107 | 88 => file(2, 3), // invalid argument
        2 => 4,                                                          // ENOENT
        13 | 30 | 103 | 27 | 1 => file(5, 6),                            // permission denied
        24 | 23 | 28 | 7 | 11 | 31 | 90 | 105 | 37 | 12 | 63 => file(7, 8), // resource exhausted
        21 | 74 | 20 => file(9, 10),                                     // inappropriate type
        6 | 113 | 101 | 10 | 111 | 61 | 42 | 3 => file(11, 12),          // no such thing
        17 | 115 | 106 => file(13, 14),                                  // already exists
        5 => 15,                                                         // EIO: hardware fault
        39 => 16,                                                        // ENOTEMPTY
        25 => 17,                                                        // ENOTTY
        104 | 43 | 100 | 102 | 67 | 32 => 18,                            // resource vanished
        71 | 93 | 91 => 19,                                              // protocol error
        62 | 110 => 20,                                                  // time expired
        98 | 16 | 35 | 26 => 21,                                         // resource busy
        99 | 97 | 19 | 92 | 38 | 95 | 34 | 29 | 18 => 22,                // unsupported operation
        _ => 0,                                                          // other error
    }
}

pub fn is_open(h: &LHandle) -> bool {
    fh(h).fd >= 0
}
