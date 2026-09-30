//! Differential tests of the `FILE` model: random sequences of Lean's
//! handle operations run on a real glibc `FILE` and on a `CFile`, each on
//! its own copy of a file; after every step the results, `errno`s, `feof`,
//! and the bytes on disk must agree.

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
                (g.read(n), m.read(n))
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
}

/// A read-only `FILE` on a pipe holding `data` (at most 64 KiB, so the
/// writes cannot block), write end closed: stdin from a pipe.
fn pipe_with(data: &[u8]) -> c_int {
    let mut fds = [0 as c_int; 2];
    assert_eq!(unsafe { pipe(fds.as_mut_ptr()) }, 0);
    let mut done = 0;
    while done < data.len() {
        let n = unsafe { write(fds[1], data[done..].as_ptr() as *const c_void, data.len() - done) };
        assert!(n > 0);
        done += n as usize;
    }
    unsafe { close(fds[1]) };
    fds[0]
}

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
    for seed in 1..=300u64 {
        run_pipe_case(seed, 60);
    }
}

#[test]
fn differential_against_glibc() {
    for seed in 1..=300u64 {
        for mode in [0u8, 1, 3, 4] {
            run_case(seed, mode, 60);
        }
    }
}
