//! Differential tests of the `FILE` model: random sequences of Lean's
//! handle operations run on a real glibc `FILE` and on a `CFile`, each on
//! its own copy of a file; after every step the results, `errno`s, `feof`,
//! and the bytes on disk must agree. Where the model deliberately differs
//! from glibc (LB-02: a direct read right after output writes the output
//! first), the glibc side gets an `fflush` first (`Glibc::read_lb02`), which
//! makes glibc's behaviour defined and the model's.

use super::*;
use std::ffi::{c_char, c_int, c_long, CString};

#[allow(non_camel_case_types)]
type FILE = c_void;

extern "C" {
    fn fdopen(fd: c_int, mode: *const c_char) -> *mut FILE;
    fn fclose(f: *mut FILE) -> c_int;
    fn fwrite(p: *const c_void, s: usize, n: usize, f: *mut FILE) -> usize;
    fn fread(p: *mut c_void, s: usize, n: usize, f: *mut FILE) -> usize;
    fn fflush(f: *mut FILE) -> c_int;
    fn fseek(f: *mut FILE, off: c_long, whence: c_int) -> c_int;
    fn ftello(f: *mut FILE) -> i64;
    fn getc(f: *mut FILE) -> c_int;
    fn feof(f: *mut FILE) -> c_int;
    fn ferror(f: *mut FILE) -> c_int;
    fn clearerr(f: *mut FILE);
    fn fileno(f: *mut FILE) -> c_int;
    fn __fpending(f: *mut FILE) -> usize;
    fn __fbufsize(f: *mut FILE) -> usize;
    fn open(path: *const c_char, flags: c_int, ...) -> c_int;
}

/// Lean's operations on a glibc `FILE` (`lean_io_prim_handle_*`).
struct Glibc(*mut FILE);

impl Glibc {
    fn put(&mut self, d: &[u8]) -> Result<(), i32> {
        let m = unsafe { fwrite(d.as_ptr() as *const c_void, 1, d.len(), self.0) };
        if m == d.len() { Ok(()) } else { Err(errno_now()) }
    }
    fn flush(&mut self) -> Result<(), i32> {
        if unsafe { fflush(self.0) } == 0 { Ok(()) } else { Err(errno_now()) }
    }
    fn read(&mut self, n: usize) -> Result<Vec<u8>, i32> {
        let mut v = vec![0u8; n];
        if n == 0 {
            return Ok(Vec::new());
        }
        let got = unsafe { fread(v.as_mut_ptr() as *mut c_void, 1, n, self.0) };
        if got > 0 {
            v.truncate(got);
            Ok(v)
        } else if unsafe { feof(self.0) } != 0 {
            unsafe { clearerr(self.0) };
            Ok(Vec::new())
        } else {
            Err(errno_now())
        }
    }
    /// `read` as the model does it where it deliberately differs from glibc
    /// (LB-02): a read that takes glibc's direct path (at least a buffer,
    /// `n >= __fbufsize`: in put mode nothing is read ahead) right after
    /// output writes the pending output first, as `fflush` does. A failed
    /// write ends the read with its error; a failed seek back over read-ahead
    /// (`ESPIPE`, a FIFO opened `readWrite`, which no write gives) does not:
    /// glibc's direct read then drops the bytes and reads on, and so does the
    /// model (review RXT-01). Other reads are glibc's own.
    fn read_lb02(&mut self, n: usize) -> Result<Vec<u8>, i32> {
        if n > 0 && unsafe { __fpending(self.0) } > 0 && n >= unsafe { __fbufsize(self.0) } {
            if unsafe { fflush(self.0) } != 0 && errno_now() != 29 {
                return Err(errno_now());
            }
        }
        self.read(n)
    }
    fn get_line(&mut self) -> Result<Vec<u8>, i32> {
        let mut l = Vec::new();
        loop {
            let c = unsafe { getc(self.0) };
            if c == -1 {
                break;
            }
            l.push(c as u8);
            if c == b'\n' as c_int {
                break;
            }
        }
        if unsafe { ferror(self.0) } != 0 {
            return Err(errno_now());
        }
        if unsafe { feof(self.0) } != 0 {
            unsafe { clearerr(self.0) };
        }
        Ok(l)
    }
    fn rewind(&mut self) -> Result<(), i32> {
        if unsafe { fseek(self.0, 0, 0) } == 0 { Ok(()) } else { Err(errno_now()) }
    }
    fn truncate(&mut self) -> Result<(), i32> {
        let pos = unsafe { ftello(self.0) };
        if unsafe { ftruncate(fileno(self.0), pos) } == 0 { Ok(()) } else { Err(errno_now()) }
    }
    fn is_eof(&self) -> bool {
        unsafe { feof(self.0) != 0 }
    }
}

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

fn file_bytes(p: &str) -> Vec<u8> {
    std::fs::read(p).unwrap()
}

/// Open `path` with Lean's flags for `mode` (0 read .. 4 append).
fn open_mode(path: &str, mode: u8) -> c_int {
    let flags = match mode {
        0 => 0,
        1 => 1 | 0o100 | 0o1000,
        3 => 2,
        _ => 1 | 0o100 | 0o2000,
    };
    let c = CString::new(path).unwrap();
    unsafe { open(c.as_ptr(), flags | 0o2000000, 0o666 as std::ffi::c_uint) }
}

fn run_case(seed: u64, mode: u8, steps: usize) {
    let dir = std::env::temp_dir();
    let pa = dir.join(format!("leanrt-cfile-{}-{}-a", std::process::id(), seed)).to_string_lossy().into_owned();
    let pb = dir.join(format!("leanrt-cfile-{}-{}-b", std::process::id(), seed)).to_string_lossy().into_owned();
    let mut rng = Rng(seed * 2654435761 + 12345);
    // Initial contents: lines of varied length, some large.
    let mut init = Vec::new();
    let nlines = rng.below(40);
    for i in 0..nlines {
        let len = if rng.below(8) == 0 { rng.below(9000) } else { rng.below(80) };
        for j in 0..len {
            init.push(b'a' + ((i + j) % 26) as u8);
        }
        init.push(b'\n');
    }
    std::fs::write(&pa, &init).unwrap();
    std::fs::write(&pb, &init).unwrap();
    let fmode = match mode {
        0 => "r",
        1 => "w",
        3 => "r+",
        _ => "a",
    };
    let fa = open_mode(&pa, mode);
    let fb = open_mode(&pb, mode);
    assert!(fa >= 0 && fb >= 0);
    let cm = CString::new(fmode).unwrap();
    let mut g = Glibc(unsafe { fdopen(fa, cm.as_ptr()) });
    assert!(!g.0.is_null());
    let flags = match mode {
        0 => NO_WRITES,
        1 => NO_READS,
        3 => 0,
        _ => NO_READS | IS_APPENDING,
    };
    let mut m = CFile::new(fb, flags);
    for step in 0..steps {
        let op = rng.below(8);
        let (ra, rb): (Result<Vec<u8>, i32>, Result<Vec<u8>, i32>) = match op {
            7 => {
                // Another writer changes both files the same way: stale
                // buffered data must be reused (or not) as by glibc.
                let at = rng.below(file_bytes(&pa).len() as u64 + 1) as usize;
                let len = rng.below(300) as usize + 1;
                let d: Vec<u8> = (0..len).map(|k| b'0' + ((k + step) % 10) as u8).collect();
                for p in [&pa, &pb] {
                    let mut f = std::fs::OpenOptions::new().write(true).open(p).unwrap();
                    std::io::Seek::seek(&mut f, std::io::SeekFrom::Start(at as u64)).unwrap();
                    std::io::Write::write_all(&mut f, &d).unwrap();
                }
                (Ok(Vec::new()), Ok(Vec::new()))
            }
            0 => {
                let len = match rng.below(4) {
                    0 => rng.below(10),
                    1 => rng.below(200),
                    2 => rng.below(5000),
                    _ => rng.below(20000),
                } as usize;
                let mut d: Vec<u8> = (0..len).map(|k| b'A' + ((k + step) % 26) as u8).collect();
                if len > 0 && rng.below(2) == 0 {
                    let at = rng.below(len as u64) as usize;
                    d[at] = b'\n';
                }
                (g.put(&d).map(|_| Vec::new()), m.put(&d).map(|_| Vec::new()))
            }
            1 => {
                let n = match rng.below(3) {
                    0 => rng.below(20),
                    1 => rng.below(5000),
                    _ => rng.below(20000),
                } as usize;
                (g.read_lb02(n), m.read(n))
            }
            2 => (g.get_line(), m.get_line()),
            3 => (g.flush().map(|_| Vec::new()), m.flush().map(|_| Vec::new())),
            4 => (g.rewind().map(|_| Vec::new()), m.rewind().map(|_| Vec::new())),
            5 => (g.truncate().map(|_| Vec::new()), m.truncate().map(|_| Vec::new())),
            _ => {
                let a = unsafe { ftello(g.0) };
                let b = m.do_ftell();
                (Ok(a.to_le_bytes().to_vec()), Ok(b.to_le_bytes().to_vec()))
            }
        };
        let ctx = format!("seed {} mode {} step {} op {}", seed, mode, step, op);
        assert_eq!(ra, rb, "result differs: {}", ctx);
        assert_eq!(g.is_eof(), m.is_eof(), "feof differs: {}", ctx);
        assert_eq!(file_bytes(&pa), file_bytes(&pb), "file contents differ: {}", ctx);
    }
    unsafe { fclose(g.0) };
    m.close();
    assert_eq!(file_bytes(&pa), file_bytes(&pb), "file contents differ after close: seed {} mode {}", seed, mode);
    let _ = std::fs::remove_file(&pa);
    let _ = std::fs::remove_file(&pb);
}

extern "C" {
    fn pipe(fds: *mut c_int) -> c_int;
    fn fcntl(fd: c_int, cmd: c_int, ...) -> c_int;
}

/// Linux's `F_SETPIPE_SZ`.
const F_SETPIPE_SZ: c_int = 1031;

/// A read-only `FILE`'s descriptor on a pipe that a writer thread fills with
/// `data`, then closes: stdin from a pipe. A pipe's capacity is not to be
/// relied on: a user over `fs.pipe-user-pages-soft` gets pipes of one page,
/// and writing more than that before reading blocks forever. So the pipe is
/// shrunk to one page and written concurrently (never more than a page
/// without a concurrent reader). If the reader closes first, the writer's
/// `write` fails with `EPIPE` (Rust ignores SIGPIPE) and the thread ends.
fn pipe_with(data: &[u8]) -> c_int {
    let mut fds = [0 as c_int; 2];
    assert_eq!(unsafe { pipe(fds.as_mut_ptr()) }, 0);
    let _ = unsafe { fcntl(fds[1], F_SETPIPE_SZ, 4096 as c_int) };
    let (w, data) = (fds[1], data.to_vec());
    std::thread::spawn(move || {
        let mut done = 0;
        while done < data.len() {
            let n = unsafe { write(w, data[done..].as_ptr() as *const c_void, data.len() - done) };
            if n < 0 && errno_now() == 4 {
                continue; // EINTR
            }
            if n <= 0 {
                break;
            }
            done += n as usize;
        }
        unsafe { close(w) };
    });
    fds[0]
}

/// Runs `body` on a thread of its own and fails if it runs longer than
/// `secs` seconds, so that a pipe test that blocks (a write nobody reads)
/// fails instead of hanging.
fn with_deadline(secs: u64, body: impl FnOnce() + Send + 'static) {
    use std::sync::mpsc::RecvTimeoutError;
    let (tx, rx) = std::sync::mpsc::channel();
    let h = std::thread::spawn(move || {
        body();
        let _ = tx.send(());
    });
    match rx.recv_timeout(std::time::Duration::from_secs(secs)) {
        Ok(()) => h.join().unwrap(),
        Err(RecvTimeoutError::Disconnected) => std::panic::resume_unwind(h.join().unwrap_err()),
        Err(RecvTimeoutError::Timeout) => {
            panic!("blocked for more than {secs} s: a pipe write that nobody reads?")
        }
    }
}

/// The deadline of the pipe test (it takes well under a second).
const PIPE_DEADLINE: u64 = 120;

fn run_pipe_case(seed: u64, steps: usize) {
    let mut rng = Rng(seed * 40503 + 977);
    let len = rng.below(60000) as usize;
    let data: Vec<u8> = (0..len).map(|k| if rng.below(30) == 0 { b'\n' } else { b'a' + (k % 26) as u8 }).collect();
    let cm = CString::new("r").unwrap();
    let mut g = Glibc(unsafe { fdopen(pipe_with(&data), cm.as_ptr()) });
    let mut m = CFile::new(pipe_with(&data), NO_WRITES);
    for step in 0..steps {
        let op = rng.below(7);
        let (ra, rb): (Result<Vec<u8>, i32>, Result<Vec<u8>, i32>) = match op {
            0 => (g.put(b"x").map(|_| Vec::new()), m.put(b"x").map(|_| Vec::new())),
            1 => {
                let n = match rng.below(3) {
                    0 => rng.below(20),
                    1 => rng.below(5000),
                    _ => rng.below(20000),
                } as usize;
                (g.read(n), m.read(n))
            }
            2 | 3 => (g.get_line(), m.get_line()),
            4 => (g.flush().map(|_| Vec::new()), m.flush().map(|_| Vec::new())),
            5 => (g.rewind().map(|_| Vec::new()), m.rewind().map(|_| Vec::new())),
            _ => (g.truncate().map(|_| Vec::new()), m.truncate().map(|_| Vec::new())),
        };
        let ctx = format!("pipe seed {} step {} op {}", seed, step, op);
        assert_eq!(ra, rb, "result differs: {}", ctx);
        assert_eq!(g.is_eof(), m.is_eof(), "feof differs: {}", ctx);
    }
    unsafe { fclose(g.0) };
    m.close();
}

#[test]
fn differential_against_glibc_pipes() {
    with_deadline(PIPE_DEADLINE, || {
        for seed in 1..=300u64 {
            run_pipe_case(seed, 60);
        }
    });
}

extern "C" {
    fn mkfifo(path: *const c_char, mode: std::ffi::c_uint) -> c_int;
}

/// `write` of all of `d` to `fd`.
fn write_all(fd: c_int, d: &[u8]) {
    let mut done = 0;
    while done < d.len() {
        let n = unsafe { write(fd, d[done..].as_ptr() as *const c_void, d.len() - done) };
        assert!(n > 0, "write to a FIFO");
        done += n as usize;
    }
}

/// An unseekable file opened `readWrite` (review RXT-01, RXT-04): a FIFO
/// read ahead by `getLine`, then output, then a direct read. Seeking back over
/// the read-ahead fails (`ESPIPE`), so neither glibc nor the model can write
/// the output: glibc's direct read drops it with the read-ahead and reads on,
/// and so does the model (it is no failed write: the read must not fail).
/// Then a small read, a flush, and output that a small read writes into the
/// FIFO and reads back. The FIFOs are fed by this thread only while empty,
/// at most one page at a time, so no write blocks; every read asks for no
/// more than is in the FIFO. Expected values: native Lean's
/// (the review's FIFO repro, RXT-01).
fn fifo_case() {
    let dir = std::env::temp_dir().join(format!("leanrt-cfile-fifo-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir(&dir).unwrap();
    let mk = |name: &str| {
        let p = dir.join(name).to_string_lossy().into_owned();
        let c = CString::new(p.clone()).unwrap();
        assert_eq!(unsafe { mkfifo(c.as_ptr(), 0o600) }, 0);
        p
    };
    let (pa, pb) = (mk("a"), mk("b"));
    // Lean's `readWrite` (an `O_RDWR` open does not wait for a writer).
    let fa = open_mode(&pa, 3);
    let fb = open_mode(&pb, 3);
    assert!(fa >= 0 && fb >= 0);
    let wa = open_mode(&pa, 1);
    let wb = open_mode(&pb, 1);
    assert!(wa >= 0 && wb >= 0);
    let feed = |d: &[u8]| {
        write_all(wa, d);
        write_all(wb, d);
    };
    let cm = CString::new("r+").unwrap();
    let mut g = Glibc(unsafe { fdopen(fa, cm.as_ptr()) });
    assert!(!g.0.is_null());
    let mut m = CFile::new(fb, 0);
    let check = |what: &str, ra: Result<Vec<u8>, i32>, rb: Result<Vec<u8>, i32>, g: &Glibc, m: &CFile| {
        assert_eq!(ra, rb, "result differs: fifo {}", what);
        assert_eq!(g.is_eof(), m.is_eof(), "feof differs: fifo {}", what);
        rb
    };
    let unit = |r: Result<(), i32>| r.map(|_| Vec::new());
    feed(b"abc\ndef\n");
    let r = check("getLine", g.get_line(), m.get_line(), &g, &m);
    assert_eq!(r, Ok(b"abc\n".to_vec()));
    let mut page = b"jkl\n".to_vec();
    page.resize(4096, b'x');
    feed(&page);
    let r = check("putStr", unit(g.put(b"ghi\n")), unit(m.put(b"ghi\n")), &g, &m);
    assert_eq!(r, Ok(Vec::new()));
    let r = check("read 4096", g.read_lb02(4096), m.read(4096), &g, &m);
    assert_eq!(r, Ok(page.clone()), "read 4096: the pending output and the read-ahead dropped");
    feed(b"mnop");
    let r = check("read 4", g.read_lb02(4), m.read(4), &g, &m);
    assert_eq!(r, Ok(b"mnop".to_vec()));
    let r = check("flush", unit(g.flush()), unit(m.flush()), &g, &m);
    assert_eq!(r, Ok(Vec::new()));
    let r = check("putStr q", unit(g.put(b"q")), unit(m.put(b"q")), &g, &m);
    assert_eq!(r, Ok(Vec::new()));
    let r = check("read 1", g.read_lb02(1), m.read(1), &g, &m);
    assert_eq!(r, Ok(b"q".to_vec()), "read 1: the output written into the FIFO and read back");
    unsafe {
        fclose(g.0);
        close(wa);
        close(wb);
    }
    m.close();
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn differential_against_glibc_fifo_read_write() {
    with_deadline(PIPE_DEADLINE, fifo_case);
}

#[test]
fn differential_against_glibc() {
    for seed in 1..=300u64 {
        for mode in [0u8, 1, 3, 4] {
            run_case(seed, mode, 60);
        }
    }
}
