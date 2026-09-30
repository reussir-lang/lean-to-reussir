//! Child processes (`IO.Process.spawn` & co.), following the POSIX part of
//! Lean's `src/runtime/process.cpp`: `fork` + `execvp`, pipes created with
//! `O_CLOEXEC`, the parent's ends wrapped as handles (`fdopen` "w" for the
//! child's stdin, "r" for its stdout/stderr), `waitpid` with bash's
//! `128 + signal` convention, `kill`/`killpg` with `SIGKILL`.
//!
//! Errors are recorded in the last-error slot as `decode_io_error(errno,
//! nullptr)` (no file name).

use crate::cfile::{errno_now, NO_READS, NO_WRITES};
use crate::fs::{handle_from_fd, set_err, set_ok, LHandle};
use std::cell::UnsafeCell;
use std::ffi::{c_char, c_int};

extern "C" {
    fn pipe2(fds: *mut c_int, flags: c_int) -> c_int;
    fn fork() -> c_int;
    fn execvp(file: *const c_char, argv: *const *const c_char) -> c_int;
    fn dup2(old: c_int, new: c_int) -> c_int;
    fn close(fd: c_int) -> c_int;
    fn open(path: *const c_char, flags: c_int, ...) -> c_int;
    fn chdir(path: *const c_char) -> c_int;
    fn setsid() -> c_int;
    fn clearenv() -> c_int;
    fn setenv(name: *const c_char, value: *const c_char, overwrite: c_int) -> c_int;
    fn unsetenv(name: *const c_char) -> c_int;
    fn write(fd: c_int, buf: *const std::ffi::c_void, n: usize) -> isize;
    fn _exit(code: c_int) -> !;
    fn waitpid(pid: c_int, status: *mut c_int, options: c_int) -> c_int;
    fn kill(pid: c_int, sig: c_int) -> c_int;
    fn killpg(pgrp: c_int, sig: c_int) -> c_int;
    fn abort() -> !;
}

const O_CLOEXEC: c_int = 0o2000000;
const WNOHANG: c_int = 1;
const SIGKILL: c_int = 9;

/// `IO.Process.Stdio` constructor indices.
const PIPED: u8 = 0;
const NUL: u8 = 2;

struct Global<T>(UnsafeCell<T>);
unsafe impl<T> Sync for Global<T> {}

/// The parent's ends of the last spawned child's piped streams.
static ENDS: Global<[Option<LHandle>; 3]> = Global(UnsafeCell::new([None, None, None]));

/// A C string of the bytes up to the first NUL (as `string_cstr` is read).
fn cstr(s: &[u8]) -> Vec<u8> {
    let n = s.iter().position(|&b| b == 0).unwrap_or(s.len());
    let mut v = s[..n].to_vec();
    v.push(0);
    v
}

/// What the child process writes to stderr on a failure before `exec`
/// (`std::cerr << ... << std::endl`), then `_exit(-1)`. `std::cerr` is tied
/// to `std::cout`, so the first `<<` flushes C `stdout` first: the parent's
/// pending stdout bytes, inherited by `fork`, go to the child's descriptor 1
/// (a pipe that `IO.Process.output` captures, or the parent's own stdout,
/// where the parent writes them again later).
fn child_fail(parts: &[&[u8]]) -> ! {
    crate::io::flush_stdout();
    for p in parts {
        unsafe { write(2, p.as_ptr() as *const std::ffi::c_void, p.len()) };
    }
    unsafe { _exit(-1) }
}

/// `IO.Process.spawn`: start `cmd args` with the stdio modes
/// (`modes` = stdin | stdout << 8 | stderr << 16, `IO.Process.Stdio`
/// indices), working directory `cwd` (if `has_cwd`), the environment
/// changes `env` (name, `Some` value to set or `None` to unset; applied in
/// order after clearing the environment unless `inherit_env`), in a new
/// session if `new_session`. Returns the pid (0 on failure, with the error
/// recorded); the parent's pipe ends are then `take_end(0..3)`.
pub fn spawn(
    cmd: &[u8],
    args: &[&[u8]],
    cwd: Option<&[u8]>,
    env: &[(&[u8], Option<&[u8]>)],
    modes: u32,
    inherit_env: bool,
    new_session: bool,
) -> u32 {
    let mode = [(modes & 0xff) as u8, ((modes >> 8) & 0xff) as u8, ((modes >> 16) & 0xff) as u8];
    // `lean_io_process_spawn`: `std::cout.flush()` before a child inherits stdin.
    if mode[0] == 1 {
        crate::io::flush_stdout();
    }
    let ends = unsafe { &mut *ENDS.0.get() };
    *ends = [None, None, None];
    // Pipes, in order, before anything else (`setup_stdio`).
    let mut pipes: [Option<[c_int; 2]>; 3] = [None, None, None];
    for i in 0..3 {
        if mode[i] == PIPED {
            let mut fds = [0 as c_int; 2];
            if unsafe { pipe2(fds.as_mut_ptr(), O_CLOEXEC) } == -1 {
                // Native leaks the pipes already made; so do we.
                set_err(errno_now(), None);
                return 0;
            }
            pipes[i] = Some(fds);
        }
    }
    // Everything the child needs, allocated before `fork`.
    let cmd_c = cstr(cmd);
    let args_c: Vec<Vec<u8>> = args.iter().map(|a| cstr(a)).collect();
    let mut argv: Vec<*const c_char> = vec![cmd_c.as_ptr() as *const c_char];
    argv.extend(args_c.iter().map(|a| a.as_ptr() as *const c_char));
    argv.push(std::ptr::null());
    let env_c: Vec<(Vec<u8>, Option<Vec<u8>>)> = env.iter().map(|(k, v)| (cstr(k), v.map(cstr))).collect();
    let cwd_c = cwd.map(cstr);
    let dev_null = b"/dev/null\0";
    let pid = unsafe { fork() };
    if pid == 0 {
        unsafe {
            if !inherit_env {
                clearenv();
            }
            for (k, v) in &env_c {
                match v {
                    Some(v) => setenv(k.as_ptr() as *const c_char, v.as_ptr() as *const c_char, 1),
                    None => unsetenv(k.as_ptr() as *const c_char),
                };
            }
            for i in 0..3 {
                let target = i as c_int;
                if let Some([r, w]) = pipes[i] {
                    if i == 0 {
                        dup2(r, target);
                        close(w);
                    } else {
                        dup2(w, target);
                        close(r);
                    }
                } else if mode[i] == NUL {
                    let fd = open(dev_null.as_ptr() as *const c_char, if i == 0 { 0 } else { 1 });
                    dup2(fd, target);
                }
            }
            if let Some(d) = &cwd_c {
                if chdir(d.as_ptr() as *const c_char) < 0 {
                    child_fail(&[b"could not change directory to ", &d[..d.len() - 1], b"\n"]);
                }
            }
            if new_session && setsid() < 0 {
                abort();
            }
            execvp(argv[0], argv.as_ptr());
            child_fail(&[b"could not execute external process '", &cmd_c[..cmd_c.len() - 1], b"'\n"]);
        }
    } else if pid == -1 {
        set_err(errno_now(), None);
        return 0;
    }
    for i in 0..3 {
        if let Some([r, w]) = pipes[i] {
            let (keep, other, flags) = if i == 0 { (w, r, NO_READS) } else { (r, w, NO_WRITES) };
            unsafe { close(other) };
            ends[i] = Some(handle_from_fd(keep, flags));
        }
    }
    set_ok();
    pid as u32
}

/// The parent's end of stream `i` (0 stdin, 1 stdout, 2 stderr) of the last
/// spawned child, or a closed handle when that stream was not piped.
pub fn take_end(i: u64) -> LHandle {
    let ends = unsafe { &mut *ENDS.0.get() };
    ends.get_mut(i as usize).and_then(|e| e.take()).unwrap_or_else(|| handle_from_fd(-1, 0))
}

/// stderr's bytes from the last `drain`.
static DRAINED_ERR: Global<Vec<u8>> = Global(UnsafeCell::new(Vec::new()));

#[repr(C)]
struct PollFd {
    fd: c_int,
    events: i16,
    revents: i16,
}

extern "C" {
    fn poll(fds: *mut PollFd, n: u64, timeout: c_int) -> c_int;
}

const POLLIN: i16 = 1;
const EINTR: i32 = 4;

/// `IO.Process.output`'s reads of a child's piped stdout and stderr to end
/// of file. Natively stdout is read by a dedicated task while the main
/// thread reads stderr, so a child writing much to either never blocks;
/// here both are read in turn as data arrives (`poll`). Returns stdout's
/// bytes; stderr's are then `take_drained_err()`. A read error is recorded
/// (the first one; natively stderr's is raised before the child is waited
/// for, stdout's after), and reading stops.
pub fn drain(out: &LHandle, err: &LHandle) -> Vec<u8> {
    let (mut o, mut e) = (Vec::new(), Vec::new());
    let mut done = [false, false];
    let mut failure: Option<i32> = None;
    let files = [crate::fs::fh(out) as *mut crate::cfile::CFile, crate::fs::fh(err) as *mut crate::cfile::CFile];
    // Closed handles (streams that were not piped) have nothing to read.
    for i in 0..2 {
        if unsafe { (*files[i]).fd } < 0 {
            done[i] = true;
        }
    }
    while failure.is_none() && !(done[0] && done[1]) {
        let mut fds: Vec<PollFd> = Vec::new();
        let mut which = Vec::new();
        for i in 0..2 {
            if !done[i] {
                fds.push(PollFd { fd: unsafe { (*files[i]).fd }, events: POLLIN, revents: 0 });
                which.push(i);
            }
        }
        let r = unsafe { poll(fds.as_mut_ptr(), fds.len() as u64, -1) };
        if r < 0 {
            if errno_now() == EINTR {
                continue;
            }
            failure = Some(errno_now());
            break;
        }
        for (k, pfd) in fds.iter().enumerate() {
            if pfd.revents == 0 {
                continue;
            }
            let i = which[k];
            match unsafe { (*files[i]).read_some() } {
                Ok(bytes) if bytes.is_empty() => done[i] = true,
                Ok(bytes) => (if i == 0 { &mut o } else { &mut e }).extend_from_slice(&bytes),
                Err(errno) => {
                    failure = Some(errno);
                    break;
                }
            }
        }
    }
    unsafe { *DRAINED_ERR.0.get() = e };
    match failure {
        Some(errno) => set_err(errno, None),
        None => set_ok(),
    }
    o
}

/// stderr's bytes from the last `drain`.
pub fn take_drained_err() -> Vec<u8> {
    std::mem::take(unsafe { &mut *DRAINED_ERR.0.get() })
}

fn decode_status(status: c_int) -> u32 {
    if status & 0x7f == 0 {
        ((status >> 8) & 0xff) as u32
    } else {
        128 + (status & 0x7f) as u32
    }
}

/// `Child.wait`: the exit code (`128 + signal` if killed).
pub fn wait(pid: u32) -> u32 {
    let mut status: c_int = 0;
    if unsafe { waitpid(pid as c_int, &mut status, 0) } == -1 {
        set_err(errno_now(), None);
        return 0;
    }
    set_ok();
    decode_status(status)
}

/// `Child.tryWait`: `(1 << 32) | code` once the child has exited, 0 while it
/// runs.
pub fn try_wait(pid: u32) -> u64 {
    let mut status: c_int = 0;
    let r = unsafe { waitpid(pid as c_int, &mut status, WNOHANG) };
    if r == -1 {
        set_err(errno_now(), None);
        return 0;
    }
    set_ok();
    if r == 0 { 0 } else { (1u64 << 32) | decode_status(status) as u64 }
}

/// `Child.kill`: `SIGKILL` to the child (to its process group if it was
/// spawned with `setsid`).
pub fn kill_child(pid: u32, new_session: bool) {
    let r = unsafe { if new_session { killpg(pid as c_int, SIGKILL) } else { kill(pid as c_int, SIGKILL) } };
    if r == -1 { set_err(errno_now(), None) } else { set_ok() }
}
