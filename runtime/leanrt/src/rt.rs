//! Process-level runtime: running `main` on a large stack, and Lean's stack
//! overflow report.
//!
//! Lean's runtime (`src/runtime/stack_overflow.cpp`) installs a SIGSEGV /
//! SIGBUS handler on an alternate signal stack, in every thread; a fault
//! inside the guard page just below the faulting thread's stack prints
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

thread_local! {
    /// The guard page just below the current thread's stack, `[lo, hi)`,
    /// computed when the thread installs the handler
    /// (`pthread_getattr_np` is not async-signal-safe). A constant-
    /// initialized `Copy` cell: reading it is a plain thread-local load, safe
    /// in a signal handler. Every thread that runs Lean code installs it
    /// (`install_stack_overflow_handler`).
    static GUARD: std::cell::Cell<(usize, usize)> = const { std::cell::Cell::new((0, 0)) };
}

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

/// The stack pointer of the interrupted code, from the signal context
/// (`uc_mcontext.sp` on aarch64, `gregs[REG_RSP]` on x86-64).
unsafe fn interrupted_sp(ctx: *mut c_void) -> Option<usize> {
    if ctx.is_null() {
        return None;
    }
    #[cfg(all(target_os = "linux", target_arch = "aarch64"))]
    return Some(unsafe { *((ctx as *const u8).add(432) as *const usize) });
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    return Some(unsafe { *((ctx as *const u8).add(160) as *const usize) });
    #[allow(unreachable_code)]
    None
}

/// How far below its stack a thread's stack pointer can be after a frame
/// was allocated past the stack's end.
const OVERFLOW_SP_REACH: usize = 256 << 20;

extern "C" fn segv_handler(signum: i32, info: *mut SigInfo, ctx: *mut c_void) {
    unsafe {
        let (lo, hi) = GUARD.with(|g| g.get());
        let addr = (*info).si_addr as usize;
        // Lean's rule: a fault in the guard page (of this thread's stack, or
        // of a scheduler context's, `coro`). Also a fault below the stack
        // while the stack pointer is below it: a frame bigger than the guard
        // page without stack probes (GMP's scratch space; Reussir's and
        // Rust's code probe) skips the guard page and faults further down.
        let in_guard = (lo <= addr && addr < hi) || crate::coro::in_guard(addr);
        let sp = interrupted_sp(ctx);
        let past_end = sp.is_some_and(|sp| {
            !crate::coro::within_stack(sp)
                && ((hi != 0 && addr < hi && sp < hi && hi - sp <= OVERFLOW_SP_REACH)
                    || crate::coro::past_end(addr, sp, OVERFLOW_SP_REACH))
        });
        if in_guard || past_end {
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

/// Give the current thread an alternate signal stack and its guard record,
/// and install the stack-overflow handler (process-wide, replacing Rust's
/// own report). Every thread that runs Lean code calls it when it starts:
/// the process's main thread (initializers), `main`'s thread, and any other
/// thread the runtime starts.
pub fn install_stack_overflow_handler() {
    unsafe {
        GUARD.with(|g| g.set(current_stack_guard()));
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

/// The stack size of Lean's worker threads (`lthread`): the same as the
/// main thread's (1 GiB, or `LEAN_STACK_SIZE_KB` plus a buffer). The
/// scheduler's contexts get stacks of this size (`sched`).
pub fn thread_stack_size() -> usize {
    main_stack_size()
}

/// Creating a thread failed: native Lean throws `lean::exception("failed
/// to create thread")`, which nothing catches: libc++ reports it and
/// aborts (nothing is flushed).
pub fn thread_create_failed() -> ! {
    let msg = b"libc++abi: terminating due to uncaught exception of type lean::exception: failed to create thread\n";
    unsafe {
        write(2, msg.as_ptr() as *const c_void, msg.len());
        abort()
    }
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
    fn close(fd: i32) -> i32;
    fn pipe2(fds: *mut i32, flags: i32) -> i32;
    fn eventfd(initval: u32, flags: i32) -> i32;
    fn syscall(num: i64, ...) -> i64;
    fn uname(buf: *mut [u8; 6 * 65]) -> i32;
    fn getenv(name: *const u8) -> *const u8;
    fn atoi(s: *const u8) -> i32;
}

/// The release of the running kernel as `major * 65536 + minor * 256 +
/// patch`, read as libuv's `uv__kernel_version` does (Debian's kernels give
/// it in `version`); 0 if unknown.
fn kernel_version() -> u32 {
    let mut u = [0u8; 6 * 65];
    if unsafe { uname(&mut u) } != 0 {
        return 0;
    }
    let field = |i: usize| -> &[u8] {
        let f = &u[i * 65..(i + 1) * 65];
        &f[..f.iter().position(|&b| b == 0).unwrap_or(65)]
    };
    let (release, version) = (field(2), field(3));
    let text = match version.strip_prefix(b"#1 SMP Debian ") {
        Some(rest) => rest,
        None => release,
    };
    let mut parts = [0u32; 3];
    let mut i = 0;
    for (k, part) in parts.iter_mut().enumerate() {
        let start = i;
        while i < text.len() && text[i].is_ascii_digit() {
            *part = part.saturating_mul(10).saturating_add((text[i] - b'0') as u32);
            i += 1;
        }
        if i == start {
            return 0;
        }
        if k < 2 {
            if i >= text.len() || text[i] != b'.' {
                return 0;
            }
            i += 1;
        }
    }
    parts[0] * 65536 + parts[1] * 256 + parts[2]
}

/// One of libuv's io_uring rings (`uv__iou_init`): `io_uring_setup`, kept
/// only if the kernel has the features libuv requires (else libuv closes it).
fn libuv_ring(entries: u32, flags: u32) {
    const SYS_IO_URING_SETUP: i64 = 425; // the same on every architecture
    const IORING_SETUP_SQPOLL: u32 = 2;
    const FEAT_SINGLE_MMAP: u32 = 1 << 0;
    const FEAT_NODROP: u32 = 1 << 1;
    const FEAT_RSRC_TAGS: u32 = 1 << 10;
    // `struct io_uring_params`: sq_entries, cq_entries, flags, sq_thread_cpu,
    // sq_thread_idle, features, ... (120 bytes).
    let mut params = [0u32; 30];
    params[2] = flags;
    if flags & IORING_SETUP_SQPOLL != 0 {
        params[4] = 10; // milliseconds
    }
    let fd = unsafe { syscall(SYS_IO_URING_SETUP, entries as i64, params.as_mut_ptr()) } as i32;
    if fd < 0 {
        return;
    }
    let need = FEAT_SINGLE_MMAP | FEAT_NODROP | FEAT_RSRC_TAGS;
    if params[5] & need != need {
        unsafe { close(fd) };
    }
}

/// The descriptors native Lean has open before any Lean code runs: its
/// runtime starts libuv's event loop at startup, which opens (all
/// close-on-exec, at the lowest free numbers, in this order) an epoll
/// descriptor, an io_uring ring polled by a kernel thread (64 entries, on
/// kernels from 5.10.186, or as `UV_USE_IO_URING` says) and one for epoll
/// control (256 entries), when the kernel supports them, the blocking pipe
/// that locks signal handling, the loop's non-blocking signal pipe, and an
/// eventfd for wake-ups: 8 descriptors here, numbers 3 to 10 when the
/// standard ones are open. lean2rr opens the same ones in the same order, so
/// that `/proc/self/fd`, the numbers of descriptors the program opens and
/// the point where opening fails with `EMFILE` are native's. A standard
/// descriptor closed at startup is taken by the first of them, as natively:
/// reading or writing that stream then fails as natively (`EINVAL` on the
/// epoll descriptor), and a child process sees it closed. They stay open,
/// unused.
fn reserve_libuv_descriptors() {
    const CLOEXEC: i32 = 0o2000000; // O_CLOEXEC, EPOLL_CLOEXEC, EFD_CLOEXEC
    const NONBLOCK: i32 = 0o4000; // O_NONBLOCK, EFD_NONBLOCK
    unsafe {
        if epoll_create1(CLOEXEC) < 0 {
            return;
        }
        let env = getenv(b"UV_USE_IO_URING\0".as_ptr());
        let sqpoll = if env.is_null() { kernel_version() >= 0x050ABA } else { atoi(env) != 0 };
        if sqpoll {
            libuv_ring(64, 2);
        }
        libuv_ring(256, 0);
        let mut p = [0i32; 2];
        pipe2(p.as_mut_ptr(), CLOEXEC);
        pipe2(p.as_mut_ptr(), CLOEXEC | NONBLOCK);
        eventfd(0, CLOEXEC | NONBLOCK);
    }
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

/// Whether `startup_descriptors` ran.
static DESCRIPTORS_RESERVED: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

/// An ELF constructor: it runs before `main`, and so before Rust's runtime
/// puts `/dev/null` in the place of closed standard descriptors
/// (`sanitize_standard_fds`), which could not be told apart afterwards from
/// a `/dev/null` the program was given (Python's `subprocess.DEVNULL`,
/// `<>/dev/null`). It opens libuv's descriptors
/// (`reserve_libuv_descriptors`), which take the places of closed standard
/// descriptors, as natively.
extern "C" fn startup_descriptors() {
    reserve_libuv_descriptors();
    DESCRIPTORS_RESERVED.store(true, std::sync::atomic::Ordering::Relaxed);
}

#[used]
#[link_section = ".init_array"]
static STARTUP_DESCRIPTORS: extern "C" fn() = startup_descriptors;

/// Open native Lean's startup descriptors (`reserve_libuv_descriptors`),
/// if the constructor has not. Without it, Rust's runtime has already put a
/// read-write `/dev/null` in the place of each closed standard descriptor:
/// those are closed again first, so that libuv's descriptors take their
/// places (a standard descriptor that is `/dev/null` opened read-write is
/// then taken for a closed one).
pub fn reserve_native_descriptors() {
    // Refer to the constructor, so that the linker keeps the object that
    // holds it.
    let _ = unsafe { std::ptr::read_volatile(&STARTUP_DESCRIPTORS) };
    if DESCRIPTORS_RESERVED.swap(true, std::sync::atomic::Ordering::Relaxed) {
        return;
    }
    for fd in 0..3 {
        if is_rust_dev_null(fd) {
            unsafe { close(fd) };
        }
    }
    reserve_libuv_descriptors();
}

/// The command line (`argv`), read once.
pub fn args() -> &'static [Vec<u8>] {
    static ARGS: std::sync::OnceLock<Vec<Vec<u8>>> = std::sync::OnceLock::new();
    ARGS.get_or_init(|| std::env::args_os().map(std::os::unix::ffi::OsStringExt::into_vec).collect())
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
    reserve_native_descriptors();
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
    reserve_native_descriptors();
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
    let t = match std::thread::Builder::new()
        .name("main".into())
        .stack_size(main_stack_size())
        .spawn(move || {
            install_stack_overflow_handler();
            body()
        }) {
        Ok(t) => t,
        Err(_) => {
            // Native `lean_run_main` throws `lean::exception("failed to
            // create thread")`, which nothing catches: libc++ reports it
            // and aborts (nothing is flushed).
            extern "C" {
                fn write(fd: i32, buf: *const u8, n: usize) -> isize;
                fn abort() -> !;
            }
            let msg = b"libc++abi: terminating due to uncaught exception of type lean::exception: failed to create thread\n";
            unsafe {
                write(2, msg.as_ptr(), msg.len());
                abort()
            }
        }
    };
    if t.join().is_err() {
        crate::io::flush_stdout();
        std::process::exit(101);
    }
}
