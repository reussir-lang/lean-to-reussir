//! Process-level runtime: running `main` on a large stack, and Lean's stack
//! overflow report.
//!
//! Lean's runtime (`src/runtime/stack_overflow.cpp`) installs a SIGSEGV /
//! SIGBUS handler on an alternate signal stack; a fault inside the guard
//! page just below the faulting thread's stack prints
//! `\nStack overflow detected. Aborting.\n` to stderr and calls `abort()`
//! (exit status 134, buffered stdout is *not* flushed). Any other fault
//! resets the handler to the default, so the fault is re-raised on return.

use std::ffi::c_void;

#[repr(C)]
struct SigAction {
    sa_sigaction: usize,
    sa_mask: [u64; 16],
    sa_flags: i32,
    sa_restorer: usize,
}

#[repr(C)]
struct StackT {
    ss_sp: *mut c_void,
    ss_flags: i32,
    ss_size: usize,
}

#[repr(C)]
struct SigInfo {
    si_signo: i32,
    si_errno: i32,
    si_code: i32,
    _pad: i32,
    si_addr: *mut c_void,
}

const SIGBUS: i32 = 7;
const SIGSEGV: i32 = 11;
const SA_SIGINFO: i32 = 4;
const SA_ONSTACK: i32 = 0x0800_0000;
const SC_PAGESIZE: i32 = 30;
const ALTSTACK_SIZE: usize = 1 << 16;
const PROT_NONE: i32 = 0;
const PROT_READ: i32 = 1;
const PROT_WRITE: i32 = 2;
const MAP_PRIVATE: i32 = 0x02;
const MAP_ANONYMOUS: i32 = 0x20;

extern "C" {
    fn sigaction(sig: i32, act: *const SigAction, old: *mut SigAction) -> i32;
    fn sigaltstack(ss: *const StackT, old: *mut StackT) -> i32;
    fn pthread_self() -> usize;
    fn pthread_getattr_np(th: usize, attr: *mut [u64; 16]) -> i32;
    fn pthread_attr_getstack(attr: *const [u64; 16], addr: *mut *mut c_void, size: *mut usize) -> i32;
    fn pthread_attr_destroy(attr: *mut [u64; 16]) -> i32;
    fn sysconf(name: i32) -> i64;
    fn mmap(addr: *mut c_void, len: usize, prot: i32, flags: i32, fd: i32, off: i64) -> *mut c_void;
    fn mprotect(addr: *mut c_void, len: usize, prot: i32) -> i32;
    fn abort() -> !;
    fn write(fd: i32, buf: *const c_void, n: usize) -> isize;
}

/// The guard page just below the Lean thread's stack, `[lo, hi)`, computed
/// when the handler is installed (`pthread_getattr_np` is not
/// async-signal-safe; there is one Lean thread).
struct Guard(std::cell::UnsafeCell<(usize, usize)>);
unsafe impl Sync for Guard {}
static GUARD: Guard = Guard(std::cell::UnsafeCell::new((0, 0)));

/// `is_within_stack_guard` of `stack_overflow.cpp`, for the current thread.
unsafe fn current_stack_guard() -> (usize, usize) {
    let mut attr = [0u64; 16];
    if unsafe { pthread_getattr_np(pthread_self(), &mut attr) } != 0 {
        return (0, 0);
    }
    let mut stackaddr: *mut c_void = std::ptr::null_mut();
    let mut size = 0usize;
    unsafe {
        pthread_attr_getstack(&attr, &mut stackaddr, &mut size);
        pthread_attr_destroy(&mut attr);
    }
    let page = unsafe { sysconf(SC_PAGESIZE) } as usize;
    let lo = stackaddr as usize;
    (lo.wrapping_sub(page), lo)
}

extern "C" fn segv_handler(signum: i32, info: *mut SigInfo, _ctx: *mut c_void) {
    unsafe {
        let (lo, hi) = *GUARD.0.get();
        let addr = (*info).si_addr as usize;
        if lo <= addr && addr < hi {
            let msg = b"\nStack overflow detected. Aborting.\n";
            write(2, msg.as_ptr() as *const c_void, msg.len());
            abort();
        }
        // Not a stack overflow: restore the default action; returning
        // re-executes the faulting instruction.
        let dfl = SigAction { sa_sigaction: 0, sa_mask: [0; 16], sa_flags: 0, sa_restorer: 0 };
        sigaction(signum, &dfl, std::ptr::null_mut());
    }
}

/// Give the current thread an alternate signal stack and install the
/// stack-overflow handler (process-wide, replacing Rust's own report).
pub fn install_stack_overflow_handler() {
    unsafe {
        *GUARD.0.get() = current_stack_guard();
        // The alternate stack gets its own guard page (as Rust's std does),
        // so overflowing it faults instead of corrupting memory.
        let page = sysconf(SC_PAGESIZE) as usize;
        let base = mmap(std::ptr::null_mut(), page + ALTSTACK_SIZE, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
        if base as isize != -1 {
            mprotect(base, page, PROT_NONE);
            let ss = StackT { ss_sp: (base as usize + page) as *mut c_void, ss_flags: 0, ss_size: ALTSTACK_SIZE };
            sigaltstack(&ss, std::ptr::null_mut());
        }
        for sig in [SIGSEGV, SIGBUS] {
            let act = SigAction {
                sa_sigaction: segv_handler as extern "C" fn(i32, *mut SigInfo, *mut c_void) as usize,
                sa_mask: [0; 16],
                sa_flags: SA_SIGINFO | SA_ONSTACK,
                sa_restorer: 0,
            };
            sigaction(sig, &act, std::ptr::null_mut());
        }
    }
}

/// The stack size of Lean's main thread (`lean_run_main`): 1 GiB on 64-bit
/// targets, or `LEAN_STACK_SIZE_KB` (rounded down to 4 KiB) plus a
/// 128 KiB buffer.
fn main_stack_size() -> usize {
    if let Some(v) = std::env::var_os("LEAN_STACK_SIZE_KB") {
        let kb = strtoull10(std::os::unix::ffi::OsStrExt::as_bytes(v.as_os_str()));
        let sz = (kb / 4 * 4).wrapping_mul(1024) as usize;
        if sz > 0 {
            return sz.saturating_add(128 * 1024);
        }
    }
    1 << 30
}

/// C's `strtoull(s, nullptr, 10)`: leading white space, an optional sign
/// (`-` negates modulo 2^64), then decimal digits up to the first other
/// character; saturates at 2^64 - 1.
fn strtoull10(s: &[u8]) -> u64 {
    let mut i = 0;
    while i < s.len() && matches!(s[i], b' ' | b'\t' | b'\n' | b'\x0b' | b'\x0c' | b'\r') {
        i += 1;
    }
    let neg = i < s.len() && s[i] == b'-';
    if i < s.len() && (s[i] == b'-' || s[i] == b'+') {
        i += 1;
    }
    let mut v: u64 = 0;
    let mut overflow = false;
    while i < s.len() && s[i].is_ascii_digit() {
        match v.checked_mul(10).and_then(|x| x.checked_add((s[i] - b'0') as u64)) {
            Some(x) => v = x,
            None => overflow = true,
        }
        i += 1;
    }
    if overflow {
        return u64::MAX;
    }
    if neg { v.wrapping_neg() } else { v }
}

extern "C" {
    fn fcntl(fd: i32, cmd: i32, ...) -> i32;
    fn epoll_create1(flags: i32) -> i32;
    fn dup2(old: i32, new: i32) -> i32;
    fn close(fd: i32) -> i32;
}

/// Whether `fd` is the `/dev/null` Rust's runtime opens (read-write) in
/// place of a standard descriptor that was closed at startup
/// (`sanitize_standard_fds`, run before any Rust `main`).
fn is_rust_dev_null(fd: i32) -> bool {
    use std::os::unix::fs::{FileTypeExt, MetadataExt};
    use std::os::unix::io::FromRawFd;
    const F_GETFL: i32 = 3;
    const O_ACCMODE: i32 = 3;
    const O_RDWR: i32 = 2;
    const DEV_NULL: u64 = (1 << 8) | 3; // makedev(1, 3)
    let f = std::mem::ManuallyDrop::new(unsafe { std::fs::File::from_raw_fd(fd) });
    let Ok(m) = f.metadata() else { return false };
    m.file_type().is_char_device() && m.rdev() == DEV_NULL && unsafe { fcntl(fd, F_GETFL) } & O_ACCMODE == O_RDWR
}

/// Native Lean's runtime opens several descriptors at startup (libuv's
/// epoll/eventfd/pipes); when stdin, stdout or stderr is closed, the lowest
/// of them takes its place, and reading or writing that stream then fails
/// with `EINVAL` (not `EBADF`). Put epoll descriptors in the place of
/// closed standard descriptors (still closed, or already replaced by Rust's
/// runtime with `/dev/null`) so the same errors arise here. (A standard
/// descriptor redirected by the user to `/dev/null` read-write, `<>`, is
/// taken for a closed one.)
pub fn occupy_closed_std_fds() {
    const F_GETFD: i32 = 1;
    const EPOLL_CLOEXEC: i32 = 0o2000000;
    for fd in 0..3 {
        if unsafe { fcntl(fd, F_GETFD) } < 0 || is_rust_dev_null(fd) {
            let e = unsafe { epoll_create1(EPOLL_CLOEXEC) };
            if e >= 0 && e != fd {
                unsafe {
                    dup2(e, fd);
                    close(e);
                }
            }
        }
    }
}

/// `IO.initializing` (`lean_io_initializing`): true while module
/// initializers run. lean2rr's entry sets it around them.
static INITIALIZING: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

pub fn set_initializing(b: bool) {
    INITIALIZING.store(b, std::sync::atomic::Ordering::Relaxed)
}

pub fn initializing() -> bool {
    INITIALIZING.load(std::sync::atomic::Ordering::Relaxed)
}

/// Run the program's main body as Lean does (`lean_run_main`): on a thread
/// with Lean's main stack size (unless `LEAN_MAIN_USE_THREAD=0`), with
/// Lean's stack-overflow report, and wait for it.
pub fn run_main<F: FnOnce() + Send + 'static>(body: F) {
    occupy_closed_std_fds();
    run_body(body)
}

/// Run a program as Lean's generated C `main` does: `init` (the module
/// initializers) on the calling thread (the process's main thread, with its
/// usual stack, so deep initializers overflow as natively), then `body` as
/// `run_main` does (`lean_run_main`: Lean's big main stack). Both have
/// Lean's stack-overflow report. `init` decides itself whether to continue
/// (an initializer's uncaught error exits); `IO.initializing` is the
/// caller's business (`set_initializing`).
pub fn run_main2<I: FnOnce(), F: FnOnce() + Send + 'static>(init: I, body: F) {
    occupy_closed_std_fds();
    install_stack_overflow_handler();
    init();
    run_body(body)
}

fn run_body<F: FnOnce() + Send + 'static>(body: F) {
    if std::env::var("LEAN_MAIN_USE_THREAD").map(|v| v == "0").unwrap_or(false) {
        install_stack_overflow_handler();
        body();
        return;
    }
    let t = std::thread::Builder::new()
        .name("main".into())
        .stack_size(main_stack_size())
        .spawn(move || {
            install_stack_overflow_handler();
            body()
        })
        .expect("leanrt: cannot spawn the main thread");
    if t.join().is_err() {
        crate::io::flush_stdout();
        std::process::exit(101);
    }
}
