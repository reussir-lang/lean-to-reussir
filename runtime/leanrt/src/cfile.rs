//! A model of glibc's `FILE` (libio, glibc 2.3x), which native Lean uses for
//! the standard streams and `IO.FS.Handle`s.
//!
//! Lean programs observe stdio through what reaches file descriptors and
//! when (other readers of a file, `2>&1` interleaving, pipes), through
//! file positions (`rewind`, `truncate`, stdin left for the next process)
//! and through the sticky end-of-file and error indicators. So this module
//! follows libio's algorithms closely — one buffer shared by reading and
//! writing, the get/put areas, the cached file offset — issuing the same
//! system calls (hence the same `errno`s) in the same order. Function names
//! are libio's (`fileops.c`, `genops.c`): `xsputn`, `overflow`,
//! `new_do_write`, `underflow`, `uflow`, `xsgetn`, `sync`, `seekoff`,
//! `do_ftell`, `doallocate`. The Lean-level operations (`put`, `read`,
//! `get_line`, `flush`, `rewind`, `truncate`) are those of
//! `lean_io_prim_handle_*` in Lean's `io.cpp`.
//!
//! One deliberate difference: a large read right after output writes the
//! pending output first (`xsgetn`), where glibc drops it (lean-runtime's
//! docs/lean-bugs.md, LB-02).
//!
//! Buffer "pointers" are indices into `buf`; `has_buf` is false while the
//! buffer is NULL. Wide orientation, backup areas and markers are not used
//! by Lean and are not modelled.

use std::ffi::c_void;

extern "C" {
    fn read(fd: i32, buf: *mut c_void, n: usize) -> isize;
    fn write(fd: i32, buf: *const c_void, n: usize) -> isize;
    fn lseek(fd: i32, off: i64, whence: i32) -> i64;
    fn isatty(fd: i32) -> i32;
    fn close(fd: i32) -> i32;
    fn ftruncate(fd: i32, len: i64) -> i32;
    fn __errno_location() -> *mut i32;
}

pub(crate) fn errno_now() -> i32 {
    unsafe { *__errno_location() }
}

pub(crate) fn set_errno(e: i32) {
    unsafe { *__errno_location() = e }
}

pub const UNBUFFERED: u32 = 0x2;
pub const NO_READS: u32 = 0x4;
pub const NO_WRITES: u32 = 0x8;
const EOF_SEEN: u32 = 0x10;
const ERR_SEEN: u32 = 0x20;
const LINE_BUF: u32 = 0x200;
const CURRENTLY_PUTTING: u32 = 0x800;
pub const IS_APPENDING: u32 = 0x1000;

const EOF: i32 = -1;
const POS_BAD: i64 = -1;
const SEEK_SET: i32 = 0;
const SEEK_CUR: i32 = 1;
const SEEK_END: i32 = 2;
const EBADF: i32 = 9;
const EINVAL: i32 = 22;
const ESPIPE: i32 = 29;
/// glibc's `BUFSIZ`.
const BUFSIZ: usize = 8192;

pub struct CFile {
    pub fd: i32,
    flags: u32,
    buf: Vec<u8>,
    has_buf: bool,
    rb: usize,
    rp: usize,
    re: usize,
    wb: usize,
    wp: usize,
    we: usize,
    /// The cached file offset (`_offset`), `POS_BAD` when unknown.
    offset: i64,
    /// The stream has been used (`_mode != 0`).
    used: bool,
    /// The last `new_do_write` returned at its seek back over read-ahead
    /// (`ESPIPE` on a FIFO opened `readWrite`), writing nothing and setting
    /// no error indicator (not glibc state: for the LB-02 path of `xsgetn`).
    seek_failed: bool,
}

impl CFile {
    pub const fn new(fd: i32, flags: u32) -> CFile {
        CFile {
            fd,
            flags,
            buf: Vec::new(),
            has_buf: false,
            rb: 0,
            rp: 0,
            re: 0,
            wb: 0,
            wp: 0,
            we: 0,
            offset: POS_BAD,
            used: false,
            seek_failed: false,
        }
    }

    #[inline(always)]
    fn bufsize(&self) -> usize {
        self.buf.len()
    }

    #[inline(always)]
    fn setg(&mut self, b: usize, p: usize, e: usize) {
        self.rb = b;
        self.rp = p;
        self.re = e;
    }

    #[inline(always)]
    fn setp(&mut self, p: usize, e: usize) {
        self.wb = p;
        self.wp = p;
        self.we = e;
    }

    #[inline(always)]
    fn in_put_mode(&self) -> bool {
        self.flags & CURRENTLY_PUTTING != 0
    }

    pub fn is_eof(&self) -> bool {
        self.flags & EOF_SEEN != 0
    }

    pub fn is_line_buffered(&self) -> bool {
        self.flags & LINE_BUF != 0
    }

    fn clearerr(&mut self) {
        self.flags &= !(EOF_SEEN | ERR_SEEN);
    }

    // ---- allocation ----

    /// `_IO_file_doallocate`: `st_blksize` bytes (at most `BUFSIZ`), line
    /// buffered on a terminal (`DEV_TTY_P` or `isatty`).
    fn doallocate(&mut self) {
        use std::os::unix::fs::{FileTypeExt, MetadataExt};
        use std::os::unix::io::FromRawFd;
        let mut size = BUFSIZ;
        if self.fd >= 0 {
            let f = std::mem::ManuallyDrop::new(unsafe { std::fs::File::from_raw_fd(self.fd) });
            if let Ok(m) = f.metadata() {
                if m.file_type().is_char_device() {
                    let rdev = m.rdev();
                    let major = ((rdev >> 8) & 0xfff) | ((rdev >> 32) & !0xfff);
                    if (136..=143).contains(&major) || unsafe { isatty(self.fd) } == 1 {
                        self.flags |= LINE_BUF;
                    }
                }
                let b = m.blksize() as usize;
                if b > 0 && b < BUFSIZ {
                    size = b;
                }
            }
        }
        self.buf = crate::alloc::vec_with_capacity(size);
        self.buf.resize(size, 0);
        self.has_buf = true;
    }

    /// `_IO_doallocbuf`: unbuffered streams get a one-byte buffer.
    fn doallocbuf(&mut self) {
        if self.has_buf {
            return;
        }
        crate::io::flush_at_exit_registered();
        if self.flags & UNBUFFERED == 0 {
            self.doallocate();
        } else {
            self.buf = vec![0u8; 1];
            self.has_buf = true;
        }
        self.setg(0, 0, 0);
        self.setp(0, 0);
    }

    // ---- system calls ----

    /// `_IO_new_file_write`: write all of `data`; a failure sets the error
    /// indicator. Returns the number of bytes written.
    fn syswrite(&mut self, data: &[u8]) -> usize {
        let mut done = 0;
        while done < data.len() {
            let n = unsafe { write(self.fd, data[done..].as_ptr() as *const c_void, data.len() - done) };
            if n < 0 {
                self.flags |= ERR_SEEN;
                break;
            }
            done += n as usize;
        }
        if self.offset >= 0 {
            self.offset += done as i64;
        }
        done
    }

    fn sysseek(&self, off: i64, whence: i32) -> i64 {
        unsafe { lseek(self.fd, off, whence) }
    }

    /// `read(2)` into the buffer at `at`, at most `n` bytes.
    fn sysread_buf(&mut self, at: usize, n: usize) -> isize {
        unsafe { read(self.fd, self.buf[at..].as_mut_ptr() as *mut c_void, n) }
    }

    // ---- writing ----

    /// `new_do_write`: write `to_do` bytes, from the buffer at `from` (or
    /// from `user` when given), after moving the descriptor back over
    /// read-ahead; then empty the buffer. A failed seek returns before the
    /// reset, so the bytes stay buffered (and no error indicator is set);
    /// `seek_failed` records it.
    fn new_do_write(&mut self, from: usize, user: Option<&[u8]>, to_do: usize) -> usize {
        self.seek_failed = false;
        if self.flags & IS_APPENDING != 0 {
            self.offset = POS_BAD;
        } else if self.re != self.wb {
            let np = self.sysseek(self.wb as i64 - self.re as i64, SEEK_CUR);
            if np == POS_BAD {
                self.seek_failed = true;
                return 0;
            }
            self.offset = np;
        }
        let count = match user {
            Some(d) => self.syswrite(&d[..to_do]),
            None => {
                let b = std::mem::take(&mut self.buf);
                let c = self.syswrite(&b[from..from + to_do]);
                self.buf = b;
                c
            }
        };
        self.setg(0, 0, 0);
        self.wb = 0;
        self.wp = 0;
        self.we = if self.flags & (LINE_BUF | UNBUFFERED) != 0 { 0 } else { self.bufsize() };
        count
    }

    /// `_IO_do_write` of the pending output.
    fn do_flush(&mut self) -> i32 {
        let to_do = self.wp - self.wb;
        if to_do == 0 || self.new_do_write(self.wb, None, to_do) == to_do {
            0
        } else {
            EOF
        }
    }

    /// `_IO_new_file_overflow(f, ch)`; `ch = None` is `EOF` (flush).
    fn overflow(&mut self, ch: Option<u8>) -> i32 {
        if self.flags & NO_WRITES != 0 {
            self.flags |= ERR_SEEN;
            set_errno(EBADF);
            return EOF;
        }
        if !self.in_put_mode() || !self.has_buf {
            if !self.has_buf {
                self.doallocbuf();
                self.setg(0, 0, 0);
            }
            if self.rp == self.bufsize() {
                self.re = 0;
                self.rp = 0;
            }
            self.wp = self.rp;
            self.wb = self.wp;
            self.we = self.bufsize();
            self.rb = self.re;
            self.rp = self.re;
            self.flags |= CURRENTLY_PUTTING;
            if self.flags & (LINE_BUF | UNBUFFERED) != 0 {
                self.we = self.wp;
            }
        }
        let Some(c) = ch else { return self.do_flush() };
        if self.wp == self.bufsize() && self.do_flush() == EOF {
            return EOF;
        }
        self.buf[self.wp] = c;
        self.wp += 1;
        if (self.flags & UNBUFFERED != 0 || (self.flags & LINE_BUF != 0 && c == b'\n')) && self.do_flush() == EOF {
            return EOF;
        }
        c as i32
    }

    /// `_IO_default_xsputn`: copy into the free space, overflowing one
    /// character at a time.
    fn default_xsputn(&mut self, data: &[u8]) -> usize {
        let mut i = 0;
        loop {
            if self.wp < self.we {
                let count = (self.we - self.wp).min(data.len() - i);
                self.buf[self.wp..self.wp + count].copy_from_slice(&data[i..i + count]);
                self.wp += count;
                i += count;
            }
            if i == data.len() || self.overflow(Some(data[i])) == EOF {
                break;
            }
            i += 1;
        }
        i
    }

    /// `_IO_new_file_xsputn`: the bytes written, or `None` for glibc's
    /// `EOF` (everything was buffered but a flush failed).
    fn xsputn(&mut self, data: &[u8]) -> Option<usize> {
        let n = data.len();
        if n == 0 {
            return Some(0);
        }
        let mut to_do = n;
        let mut s = 0;
        let mut must_flush = false;
        let mut count = 0;
        if self.flags & LINE_BUF != 0 && self.in_put_mode() {
            count = self.bufsize() - self.wp;
            if count >= n {
                if let Some(p) = data.iter().rposition(|&c| c == b'\n') {
                    count = p + 1;
                    must_flush = true;
                }
            }
        } else if self.we > self.wp {
            count = self.we - self.wp;
        }
        if count > 0 {
            let c = count.min(to_do);
            self.buf[self.wp..self.wp + c].copy_from_slice(&data[..c]);
            self.wp += c;
            s = c;
            to_do -= c;
        }
        if to_do > 0 || must_flush {
            if self.overflow(None) == EOF {
                return if to_do == 0 { None } else { Some(n - to_do) };
            }
            let block = self.bufsize();
            let do_write = to_do - if block >= 128 { to_do % block } else { 0 };
            if do_write > 0 {
                let c = self.new_do_write(0, Some(&data[s..]), do_write);
                to_do -= c;
                if c < do_write {
                    return Some(n - to_do);
                }
            }
            if to_do > 0 {
                to_do -= self.default_xsputn(&data[s + do_write..]);
            }
        }
        Some(n - to_do)
    }

    // ---- reading ----

    /// `_IO_switch_to_get_mode`.
    fn switch_to_get_mode(&mut self) -> i32 {
        if self.wp > self.wb && self.overflow(None) == EOF {
            return EOF;
        }
        self.rb = 0;
        if self.wp > self.re {
            self.re = self.wp;
        }
        self.rp = self.wp;
        self.wb = self.wp;
        self.we = self.wp;
        self.flags &= !CURRENTLY_PUTTING;
        0
    }

    /// `_IO_new_file_underflow`: refill the buffer (reading a terminal or
    /// unbuffered stream first flushes a line-buffered stdout).
    fn underflow(&mut self) -> i32 {
        if self.flags & EOF_SEEN != 0 {
            return EOF;
        }
        if self.flags & NO_READS != 0 {
            self.flags |= ERR_SEEN;
            set_errno(EBADF);
            return EOF;
        }
        if self.rp < self.re {
            return self.buf[self.rp] as i32;
        }
        if !self.has_buf {
            self.doallocbuf();
        }
        if self.flags & (LINE_BUF | UNBUFFERED) != 0 {
            crate::io::flush_line_buffered_stdout();
        }
        let _ = self.switch_to_get_mode();
        self.setg(0, 0, 0);
        self.setp(0, 0);
        self.we = 0;
        let size = self.bufsize();
        let mut count = self.sysread_buf(0, size);
        if count <= 0 {
            if count == 0 {
                self.flags |= EOF_SEEN;
            } else {
                self.flags |= ERR_SEEN;
                count = 0;
            }
        }
        self.re += count as usize;
        if count == 0 {
            self.offset = POS_BAD;
            return EOF;
        }
        if self.offset != POS_BAD {
            self.offset += count as i64;
        }
        self.buf[self.rp] as i32
    }

    /// `__underflow`: leave put mode first.
    fn underflow_generic(&mut self) -> i32 {
        self.used = true;
        if self.in_put_mode() && self.switch_to_get_mode() == EOF {
            return EOF;
        }
        if self.rp < self.re {
            return self.buf[self.rp] as i32;
        }
        self.underflow()
    }

    /// `__uflow` (`getc` on an empty get area): the next byte, or `EOF`
    /// (end of file or error).
    fn uflow(&mut self) -> i32 {
        self.used = true;
        if self.in_put_mode() && self.switch_to_get_mode() == EOF {
            return EOF;
        }
        if self.rp < self.re {
            let c = self.buf[self.rp];
            self.rp += 1;
            return c as i32;
        }
        if self.underflow() == EOF {
            return EOF;
        }
        let c = self.buf[self.rp];
        self.rp += 1;
        c as i32
    }

    /// `_IO_file_xsgetn`: up to `n` bytes written to `out` (room for `n`),
    /// their number returned. Requests of at least a buffer are read
    /// directly into `out`, in whole blocks, discarding the (empty) buffer
    /// state, after writing any pending output (where glibc drops it:
    /// LB-02).
    ///
    /// # Safety
    /// `out` must be valid for writes of `n` bytes.
    unsafe fn xsgetn(&mut self, out: *mut u8, n: usize) -> usize {
        let mut want = n;
        if !self.has_buf {
            self.doallocbuf();
        }
        while want > 0 {
            let have = self.re - self.rp;
            if want <= have {
                std::ptr::copy_nonoverlapping(self.buf[self.rp..].as_ptr(), out.add(n - want), want);
                self.rp += want;
                want = 0;
            } else {
                if have > 0 {
                    std::ptr::copy_nonoverlapping(self.buf[self.rp..].as_ptr(), out.add(n - want), have);
                    want -= have;
                    self.rp += have;
                }
                if self.has_buf && want < self.bufsize() {
                    if self.underflow_generic() == EOF {
                        break;
                    }
                    continue;
                }
                // Not glibc (LB-02 in lean-runtime's docs/lean-bugs.md):
                // glibc resets the put area here, so output written just
                // before is dropped (C11 leaves output directly followed by
                // input undefined). The pending bytes are written first, as
                // `fflush` does (a small read writes them too, through
                // `underflow_generic`); if that write fails, so does the
                // read. A failed seek back over read-ahead (`ESPIPE`: a FIFO
                // opened `readWrite`, `new_do_write` returning before it
                // writes) is no failed write: the bytes are dropped below
                // with the read-ahead and the read goes on, as glibc's direct
                // read does (review RXT-01; lean-runtime io-1 af6ecf2); the
                // failed seek's ESPIPE is then forgotten (`errno` as before),
                // since native's direct read makes no seek, and a later error
                // report that reads `errno` (`getLine` on a handle with its
                // error indicator set) must see native's (review RXT-06).
                // Then the read starts at the cursor (and fails with EBADF on
                // a write-only stream, as natively).
                if self.wp > self.wb {
                    let saved = errno_now();
                    if self.do_flush() == EOF {
                        if !self.seek_failed {
                            break;
                        }
                        set_errno(saved);
                    }
                }
                self.setg(0, 0, 0);
                self.setp(0, 0);
                let mut count = want;
                let block = self.bufsize();
                if block >= 128 {
                    count -= want % block;
                }
                debug_assert!(count <= want);
                let r = read(self.fd, out.add(n - want) as *mut c_void, count);
                if r <= 0 {
                    if r == 0 {
                        self.flags |= EOF_SEEN;
                    } else {
                        self.flags |= ERR_SEEN;
                    }
                    break;
                }
                want -= r as usize;
                if self.offset != POS_BAD {
                    self.offset += r as i64;
                }
            }
        }
        n - want
    }

    // ---- positioning ----

    /// `_IO_new_file_sync` (`fflush`): write pending output, give back
    /// read-ahead (seeking back; ignored on pipes).
    fn sync(&mut self) -> i32 {
        let mut retval = 0;
        if self.wp > self.wb && self.do_flush() != 0 {
            return EOF;
        }
        let delta = self.rp as i64 - self.re as i64;
        if delta != 0 {
            let np = self.sysseek(delta, SEEK_CUR);
            if np != POS_BAD {
                self.re = self.rp;
            } else if errno_now() != ESPIPE {
                retval = EOF;
            }
        }
        if retval != EOF {
            self.offset = POS_BAD;
        }
        retval
    }

    /// `_IO_new_file_seekoff(fp, offset, dir, _IOS_INPUT|_IOS_OUTPUT)`.
    fn seekoff(&mut self, mut offset: i64, mut dir: i32) -> i64 {
        let must_be_exact = self.rb == self.re && self.wb == self.wp;
        let was_writing = self.wp > self.wb || self.in_put_mode();
        if was_writing && self.switch_to_get_mode() != 0 {
            return EOF as i64;
        }
        if !self.has_buf {
            self.doallocbuf();
            self.setp(0, 0);
            self.setg(0, 0, 0);
        }
        let mut dumb = false;
        match dir {
            SEEK_CUR => {
                offset -= self.re as i64 - self.rp as i64;
                if self.offset == POS_BAD {
                    dumb = true;
                } else {
                    offset += self.offset;
                    if offset < 0 {
                        set_errno(EINVAL);
                        return EOF as i64;
                    }
                    dir = SEEK_SET;
                }
            }
            SEEK_END => {
                use std::os::unix::io::FromRawFd;
                let f = std::mem::ManuallyDrop::new(unsafe { std::fs::File::from_raw_fd(self.fd) });
                match f.metadata() {
                    Ok(m) if m.is_file() => {
                        offset += m.len() as i64;
                        dir = SEEK_SET;
                    }
                    _ => dumb = true,
                }
            }
            _ => {}
        }
        if !dumb {
            if self.offset != POS_BAD && self.has_buf {
                let start = self.offset - self.re as i64;
                if offset >= start && offset < self.offset {
                    let (re, p) = (self.re, (offset - start) as usize);
                    self.setg(0, p, re);
                    self.setp(0, 0);
                    self.flags &= !EOF_SEEN;
                    if self.offset >= 0 {
                        self.sysseek(self.offset, SEEK_SET);
                    }
                    return offset;
                }
            }
            if self.flags & NO_READS == 0 {
                let bs = self.bufsize() as i64;
                let mut new_offset = offset & !(bs - 1);
                let mut delta = offset - new_offset;
                if delta > bs {
                    new_offset = offset;
                    delta = 0;
                }
                let result = self.sysseek(new_offset, SEEK_SET);
                if result < 0 {
                    return EOF as i64;
                }
                let mut count: i64 = 0;
                let mut short = false;
                if delta != 0 {
                    let want = if must_be_exact { delta as usize } else { bs as usize };
                    count = self.sysread_buf(0, want) as i64;
                    if count < delta {
                        offset = if count == EOF as i64 { delta } else { delta - count };
                        dir = SEEK_CUR;
                        short = true;
                    }
                }
                if !short {
                    self.setg(0, delta as usize, count as usize);
                    self.setp(0, 0);
                    self.offset = result + count;
                    self.flags &= !EOF_SEEN;
                    return offset;
                }
            }
        }
        // dumb:
        let result = self.sysseek(offset, dir);
        if result != EOF as i64 {
            self.flags &= !EOF_SEEN;
            self.offset = result;
            self.setg(0, 0, 0);
            self.setp(0, 0);
        }
        result
    }

    /// `do_ftell` (`ftello`).
    fn do_ftell(&mut self) -> i64 {
        let mut adj: i64 = 0;
        if self.has_buf {
            let unflushed = self.wp > self.wb;
            if unflushed && self.flags & IS_APPENDING != 0 {
                let r = self.sysseek(0, SEEK_END);
                if r == POS_BAD {
                    return EOF as i64;
                }
                self.offset = r;
            }
            if !unflushed {
                adj -= self.re as i64 - self.rp as i64;
            } else {
                adj += self.wp as i64 - self.re as i64;
            }
        }
        let r = if self.offset != POS_BAD { self.offset } else { self.sysseek(0, SEEK_CUR) };
        if r == EOF as i64 {
            return r;
        }
        let r = r + adj;
        if r < 0 {
            set_errno(EINVAL);
            return EOF as i64;
        }
        r
    }

    // ---- Lean's operations (`lean_io_prim_handle_*`) ----

    /// `Handle.putStr` / `Handle.write`: `fwrite`; `Err(errno)` unless all
    /// bytes were taken.
    pub fn put(&mut self, data: &[u8]) -> Result<(), i32> {
        if data.is_empty() {
            return Ok(());
        }
        self.used = true;
        match self.xsputn(data) {
            None => Ok(()),
            Some(m) if m == data.len() => Ok(()),
            Some(_) => Err(errno_now()),
        }
    }

    /// `Handle.flush`: `fflush`.
    pub fn flush(&mut self) -> Result<(), i32> {
        if self.sync() == 0 { Ok(()) } else { Err(errno_now()) }
    }

    /// `Handle.read n`: `fread` into an array of `n` bytes (allocated at
    /// once, as Lean's); any bytes read are a success; with none, end of
    /// file clears the indicators (`clearerr`), otherwise it is an error.
    pub fn read(&mut self, n: usize) -> Result<Vec<u8>, i32> {
        let mut out: Vec<u8> = crate::alloc::vec_with_capacity(n);
        let got = unsafe { self.read_into(out.as_mut_ptr(), n)? };
        unsafe { out.set_len(got) };
        Ok(out)
    }

    /// `read` into `out` (room for `n` bytes, the caller's: a byte array's
    /// block, so that the bytes are not copied again): how many were read.
    ///
    /// # Safety
    /// `out` must be valid for writes of `n` bytes.
    pub unsafe fn read_into(&mut self, out: *mut u8, n: usize) -> Result<usize, i32> {
        if n == 0 {
            return Ok(0);
        }
        self.used = true;
        let got = self.xsgetn(out, n);
        if got > 0 {
            Ok(got)
        } else if self.is_eof() {
            self.clearerr();
            Ok(0)
        } else {
            Err(errno_now())
        }
    }

    /// What one `read(1024)`-sized step of `readToEnd` gets without blocking
    /// twice: the buffered bytes, or one refill (one `read(2)`). `Ok` empty
    /// at end of file (clearing the indicators, as `read` at end of file
    /// does); `Err(errno)` on a read error. For `IO.Process.output`'s
    /// polling of two pipes.
    pub(crate) fn read_some(&mut self) -> Result<Vec<u8>, i32> {
        self.used = true;
        if self.rp >= self.re && self.underflow_generic() == EOF {
            if self.flags & ERR_SEEN != 0 {
                return Err(errno_now());
            }
            self.clearerr();
            return Ok(Vec::new());
        }
        let v = self.buf[self.rp..self.re].to_vec();
        self.rp = self.re;
        Ok(v)
    }

    /// `Handle.getLine`: `getc` up to and including `\n` (or to end of file
    /// or error); then an error indicator (set now or by any earlier
    /// failure) is an error and the line is lost; otherwise end of file is
    /// cleared.
    pub fn get_line(&mut self) -> Result<Vec<u8>, i32> {
        let mut line = Vec::new();
        loop {
            // Fast path: a whole line in the buffer.
            if self.rp < self.re {
                let avail = &self.buf[self.rp..self.re];
                match avail.iter().position(|&b| b == b'\n') {
                    Some(k) => {
                        line.extend_from_slice(&avail[..=k]);
                        self.rp += k + 1;
                        break;
                    }
                    None => {
                        line.extend_from_slice(avail);
                        self.rp = self.re;
                    }
                }
            }
            let c = self.uflow();
            if c == EOF {
                break;
            }
            line.push(c as u8);
            if c == b'\n' as i32 {
                break;
            }
        }
        if self.flags & ERR_SEEN != 0 {
            return Err(errno_now());
        }
        if self.is_eof() {
            self.clearerr();
        }
        Ok(line)
    }

    /// `Handle.rewind`: `fseek(fp, 0, SEEK_SET)`.
    pub fn rewind(&mut self) -> Result<(), i32> {
        if self.seekoff(0, SEEK_SET) == EOF as i64 { Err(errno_now()) } else { Ok(()) }
    }

    /// `Handle.truncate`: `ftruncate(fileno(fp), ftello(fp))` (without
    /// flushing).
    pub fn truncate(&mut self) -> Result<(), i32> {
        let pos = self.do_ftell();
        if unsafe { ftruncate(self.fd, pos) } == 0 { Ok(()) } else { Err(errno_now()) }
    }

    /// `fclose`: flush pending output, close the descriptor.
    pub fn close(&mut self) {
        if self.fd < 0 {
            return;
        }
        if self.flags & NO_WRITES == 0 && self.in_put_mode() {
            let _ = self.do_flush();
        }
        unsafe { close(self.fd) };
        self.fd = -1;
        self.buf = Vec::new();
        self.has_buf = false;
    }

    /// `_IO_OVERFLOW(fp, EOF)`: write pending output (entering put mode).
    pub(crate) fn flush_pending(&mut self) -> i32 {
        self.overflow(None)
    }

    /// `_IO_flush_all` at exit: write pending output.
    pub(crate) fn exit_flush(&mut self) {
        if self.fd >= 0 && self.wp > self.wb {
            let _ = self.overflow(None);
        }
    }

    /// `_IO_unbuffer_all` at exit: `setbuf(fp, NULL)` of a used, buffered
    /// stream syncs it (giving back seekable read-ahead).
    pub(crate) fn exit_unbuffer(&mut self) {
        if self.fd >= 0 && self.flags & UNBUFFERED == 0 && self.used {
            let _ = self.sync();
        }
    }
}

#[cfg(test)]
#[path = "cfile_tests.rs"]
mod tests;
