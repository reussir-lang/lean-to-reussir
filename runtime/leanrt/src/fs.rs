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
    fname: Option<Vec<u8>>,
    details: Option<Vec<u8>>,
}

static LAST: Global<LastError> = Global(UnsafeCell::new(LastError { errno: 0, fname: None, details: None }));

fn last() -> &'static mut LastError {
    unsafe { &mut *LAST.0.get() }
}

fn set_ok() {
    let l = last();
    l.errno = 0;
    l.fname = None;
    l.details = None;
}

fn set_err(errno: i32, fname: Option<&[u8]>) {
    let l = last();
    l.errno = errno;
    l.fname = fname.map(|f| f.to_vec());
    l.details = None;
}

extern "C" {
    fn open(path: *const std::ffi::c_char, flags: i32, ...) -> i32;
    fn close(fd: i32) -> i32;
    fn read(fd: i32, buf: *mut c_void, n: usize) -> isize;
    fn write(fd: i32, buf: *const c_void, n: usize) -> isize;
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
        let l = last();
        l.errno = EINVAL;
        l.fname = Some(p.to_vec());
        l.details = Some(b"string contains NUL bytes".to_vec());
        return None;
    }
    let mut v = p.to_vec();
    v.push(0);
    Some(v)
}

pub struct FileHandle {
    fd: i32,
    rbuf: Vec<u8>,
    rpos: usize,
    wbuf: Vec<u8>,
}

const BUF: usize = 1 << 16;

impl FileHandle {
    fn flush(&mut self) -> Result<(), i32> {
        let mut data = &self.wbuf[..];
        while !data.is_empty() {
            let n = unsafe { write(self.fd, data.as_ptr() as *const c_void, data.len()) };
            if n < 0 {
                let e = errno_now();
                if e == 4 {
                    continue;
                }
                self.wbuf.clear();
                return Err(e);
            }
            data = &data[n as usize..];
        }
        self.wbuf.clear();
        Ok(())
    }

    fn write_bytes(&mut self, b: &[u8]) -> Result<(), i32> {
        if !self.rbuf.is_empty() {
            // C stdio needs a seek between reading and writing; drop the
            // read-ahead and position the file where the reader was.
            let back = (self.rbuf.len() - self.rpos) as i64;
            unsafe { lseek(self.fd, -back, 1) };
            self.rbuf.clear();
            self.rpos = 0;
        }
        self.wbuf.extend_from_slice(b);
        if self.wbuf.len() >= BUF {
            self.flush()?;
        }
        Ok(())
    }

    /// Fill the read buffer; `Ok(false)` at end of file.
    fn fill(&mut self) -> Result<bool, i32> {
        if !self.wbuf.is_empty() {
            self.flush()?;
        }
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
                return Err(e);
            }
            self.rbuf.truncate(n as usize);
            return Ok(n > 0);
        }
    }
}

impl Drop for FileHandle {
    fn drop(&mut self) {
        if self.fd >= 0 {
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

fn mk(fd: i32) -> LHandle {
    Rc::new(Box::new(UnsafeCell::new(FileHandle { fd, rbuf: Vec::new(), rpos: 0, wbuf: Vec::new() })) as Box<dyn Any>)
}

/// `IO.FS.Handle.mk path mode` (`read`, `write`, `writeNew`, `readWrite`,
/// `append` = 0..4). On failure the result is a closed handle.
pub fn open_file(path: &[u8], mode: u8) -> LHandle {
    let Some(c) = c_path(path) else { return mk(-1) };
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
    mk(fd)
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

/// `Handle.read n`: up to `n` bytes (fewer only at end of file).
pub fn read_bytes(h: &LHandle, n: u64) -> Vec<u8> {
    let f = fh(h);
    let n = n as usize;
    let mut out = Vec::with_capacity(n.min(BUF));
    while out.len() < n {
        if f.rpos >= f.rbuf.len() {
            match f.fill() {
                Ok(true) => {}
                Ok(false) => break,
                Err(e) => {
                    set_err(e, None);
                    return Vec::new();
                }
            }
        }
        let k = (f.rbuf.len() - f.rpos).min(n - out.len());
        out.extend_from_slice(&f.rbuf[f.rpos..f.rpos + k]);
        f.rpos += k;
    }
    set_ok();
    out
}

/// `Handle.getLine`: up to and including `\n`, or to end of file.
pub fn get_line(h: &LHandle) -> LStr {
    let f = fh(h);
    let mut line = Vec::new();
    loop {
        if f.rpos >= f.rbuf.len() {
            match f.fill() {
                Ok(true) => {}
                Ok(false) => break,
                Err(e) => {
                    set_err(e, None);
                    return from_bytes(b"");
                }
            }
        }
        let avail = &f.rbuf[f.rpos..];
        if let Some(k) = avail.iter().position(|&b| b == b'\n') {
            line.extend_from_slice(&avail[..=k]);
            f.rpos += k + 1;
            set_ok();
            return from_bytes_lossy(&line);
        }
        line.extend_from_slice(avail);
        f.rpos = f.rbuf.len();
    }
    set_ok();
    from_bytes_lossy(&line)
}

pub fn is_tty(h: &LHandle) -> bool {
    unsafe { isatty(fh(h).fd) == 1 }
}

pub fn rewind(h: &LHandle) {
    let f = fh(h);
    if let Err(e) = f.flush() {
        return set_err(e, None);
    }
    f.rbuf.clear();
    f.rpos = 0;
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

pub fn remove_file(p: &[u8]) {
    path_op(p, |c| unsafe { unlink(c) })
}

pub fn create_dir(p: &[u8]) {
    path_op(p, |c| unsafe { mkdir(c, 0o777) })
}

pub fn remove_dir(p: &[u8]) {
    path_op(p, |c| unsafe { rmdir(c) })
}

pub fn set_access_rights(p: &[u8], mode: u32) {
    path_op(p, |c| unsafe { chmod(c, mode) })
}

/// `IO.FS.rename`; the error names both files as Lean does.
pub fn rename_file(from: &[u8], to: &[u8]) {
    let (Some(a), Some(b)) = (c_path(from), c_path(to)) else { return };
    if unsafe { rename(a.as_ptr() as *const std::ffi::c_char, b.as_ptr() as *const std::ffi::c_char) } != 0 {
        let mut both = from.to_vec();
        both.extend_from_slice(b" and/or ");
        both.extend_from_slice(to);
        set_err(errno_now(), Some(&both));
    } else {
        set_ok()
    }
}

pub fn hard_link(from: &[u8], to: &[u8]) {
    let (Some(a), Some(b)) = (c_path(from), c_path(to)) else { return };
    if unsafe { link(a.as_ptr() as *const std::ffi::c_char, b.as_ptr() as *const std::ffi::c_char) } != 0 {
        set_err(errno_now(), Some(from))
    } else {
        set_ok()
    }
}

/// `IO.FS.realPath`.
pub fn real_path(p: &[u8]) -> LStr {
    let s = String::from_utf8_lossy(p).into_owned();
    match std::fs::canonicalize(&s) {
        Ok(r) => {
            set_ok();
            from_bytes_lossy(std::os::unix::ffi::OsStrExt::as_bytes(r.as_os_str()))
        }
        Err(e) => {
            set_err(e.raw_os_error().unwrap_or(0), Some(p));
            from_bytes(p)
        }
    }
}

/// Entry names of a directory in `readdir` order, without `.` and `..`.
pub fn read_dir(p: &[u8]) -> Vec<LStr> {
    let s = String::from_utf8_lossy(p).into_owned();
    match std::fs::read_dir(&s) {
        Ok(it) => {
            set_ok();
            it.filter_map(|e| e.ok())
                .map(|e| from_bytes_lossy(std::os::unix::ffi::OsStrExt::as_bytes(e.file_name().as_os_str())))
                .collect()
        }
        Err(e) => {
            set_err(e.raw_os_error().unwrap_or(0), Some(p));
            Vec::new()
        }
    }
}

/// `System.FilePath.metadata` fields: accessed (sec, nsec), modified (sec,
/// nsec), byte size, file type (0 dir, 1 file, 2 symlink, 3 other).
pub fn metadata(p: &[u8], follow: bool) -> [u64; 6] {
    use std::os::unix::fs::MetadataExt;
    let s = String::from_utf8_lossy(p).into_owned();
    let m = if follow { std::fs::metadata(&s) } else { std::fs::symlink_metadata(&s) };
    match m {
        Ok(m) => {
            set_ok();
            let ft = m.file_type();
            let t = if ft.is_dir() { 0 } else if ft.is_file() { 1 } else if ft.is_symlink() { 2 } else { 3 };
            [m.atime() as u64, m.atime_nsec() as u64, m.mtime() as u64, m.mtime_nsec() as u64, m.size(), t]
        }
        Err(e) => {
            set_err(e.raw_os_error().unwrap_or(0), Some(p));
            [0; 6]
        }
    }
}

// ---- error decoding (`decode_io_error` in io.cpp) ----

pub fn ok() -> bool {
    last().errno == 0
}

pub fn errno() -> u32 {
    last().errno as u32
}

pub fn error_fname() -> LStr {
    from_bytes(last().fname.as_deref().unwrap_or(b""))
}

pub fn error_details() -> LStr {
    let l = last();
    match &l.details {
        Some(d) => from_bytes(d),
        None => {
            let p = unsafe { strerror(l.errno) };
            let c = unsafe { std::ffi::CStr::from_ptr(p) };
            from_bytes_lossy(c.to_bytes())
        }
    }
}

/// Which `lean_mk_io_error_*` constructor Lean's `decode_io_error` uses for
/// the last error (see the table in runtime/README.md).
pub fn error_kind() -> u32 {
    let l = last();
    decode_kind(l.errno, l.fname.is_some())
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
