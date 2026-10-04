//! Process-level runtime: running `main` on a large stack, Lean's stack
//! overflow report, and the startup glue lean-runtime's io asks of a
//! translator (`io::startup`): the ELF constructor that opens native Lean's
//! startup descriptors, and `IO.initializing`'s end.
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
            // `segv_handler`'s text (lean-runtime's), a static: no
            // allocation in the handler.
            let msg = lean_runtime::semantics::panic::STACK_OVERFLOW_MESSAGE.as_bytes();
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
    fn close(fd: i32) -> i32;
}

/// Whether native Lean's startup descriptors are open (`startup_descriptors`
/// or `reserve_native_descriptors` ran).
static DESCRIPTORS_RESERVED: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

/// lean-runtime's startup descriptors (`io::startup`): native Lean's runtime
/// starts libuv's event loop at startup, which opens (close-on-exec, at the
/// lowest free numbers) an epoll descriptor, two io_uring rings when the
/// kernel has them, the pipe that locks signal handling, the loop's signal
/// pipe and an eventfd: numbers 3 to 10 when the standard ones are open, so
/// that `/proc/self/fd`, the numbers of the descriptors the program opens and
/// the point where opening fails with `EMFILE` are native's, and a standard
/// descriptor closed at startup is taken by the first of them. When they
/// cannot be made, the program does not reach `main`: lean-runtime ends it
/// with `INTERNAL PANIC: Failed to initialize event loop: ...` and exit status
/// 1, where native crashes (LB-30) or aborts (LB-31).
fn open_startup_descriptors() {
    if let Err(f) = lean_runtime::io::startup::open_native_descriptors() {
        lean_runtime::io::startup::fail_as_native(f)
    }
}

/// An ELF constructor (lean-runtime's glue duty, `io::startup`): it runs
/// before `main`, and so before Rust's runtime puts `/dev/null` in the place
/// of closed standard descriptors (`sanitize_standard_fds`), which could not
/// be told apart afterwards from a `/dev/null` the program was given
/// (Python's `subprocess.DEVNULL`, `<>/dev/null`). It opens native Lean's
/// startup descriptors, which take the places of closed standard
/// descriptors, as natively.
extern "C" fn startup_descriptors() {
    open_startup_descriptors();
    DESCRIPTORS_RESERVED.store(true, std::sync::atomic::Ordering::Relaxed);
}

#[used]
#[link_section = ".init_array"]
static STARTUP_DESCRIPTORS: extern "C" fn() = startup_descriptors;

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

/// Open native Lean's startup descriptors if the constructor has not.
/// Without it, Rust's runtime has already put a read-write `/dev/null` in the
/// place of each closed standard descriptor: those are closed again first,
/// so that the startup descriptors take their places (a standard descriptor
/// that is `/dev/null` opened read-write is then taken for a closed one).
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
    open_startup_descriptors();
}

/// The read and write ends of libuv's loop signal pipe, which lean-runtime
/// opened at startup (`io::startup`), for the signal watchers (`net`), as
/// libuv's loop uses it: so starting a watcher opens no descriptor, as
/// natively (test RtSignalFd). lean-runtime hands it to its first claimer
/// (`io::startup::claim_signal_pipe`, AR-17); leanrt's event loop claims it
/// once, at its first watcher, and keeps the claimer's duty: the numbers stay
/// the signal pipe for good (the loop never closes or `dup2`s over them) and
/// both ends stay non-blocking. `None` if there is none (the descriptors
/// could not be opened, or it was claimed already): the loop then makes a
/// pipe of its own.
pub fn signal_pipe() -> Option<[i32; 2]> {
    use std::os::fd::AsRawFd;
    lean_runtime::io::startup::claim_signal_pipe().map(|(r, w)| [r.as_raw_fd(), w.as_raw_fd()])
}

/// The command line (`argv`), read once.
pub fn args() -> &'static [Vec<u8>] {
    static ARGS: std::sync::OnceLock<Vec<Vec<u8>>> = std::sync::OnceLock::new();
    ARGS.get_or_init(|| std::env::args_os().map(std::os::unix::ffi::OsStringExt::into_vec).collect())
}

/// `IO.initializing` (`lean_io_initializing`), lean-runtime's flag: true from
/// the start of the process until the module initializers have run.
pub fn initializing() -> bool {
    lean_runtime::io::startup::initializing()
}

/// lean2rr's entry calls `set_initializing(true)` before the module
/// initializers (lean-runtime's flag is true from the start, so that does
/// nothing) and `set_initializing(false)` after them
/// (`lean_io_mark_end_initialization`, `io::startup::mark_end_initialization`).
pub fn set_initializing(b: bool) {
    if !b {
        #[cfg(leanrt_count_bigs)]
        crate::big::count_mark_main();
        lean_runtime::io::startup::mark_end_initialization()
    }
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

/// Whether `main` runs on a thread of its own (`run_body`), set before it
/// starts. With `LEAN_MAIN_USE_THREAD=0` it runs on the initializers'
/// thread and, as natively, keeps that thread's current standard streams
/// (lean2rr's entry starts a fresh stream context for `main` only when this
/// is true).
static MAIN_ON_THREAD: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

pub fn main_on_thread() -> bool {
    MAIN_ON_THREAD.load(std::sync::atomic::Ordering::Relaxed)
}

fn run_body<F: FnOnce() + Send + 'static>(body: F) {
    if std::env::var("LEAN_MAIN_USE_THREAD").map(|v| v == "0").unwrap_or(false) {
        install_stack_overflow_handler();
        body();
        return;
    }
    MAIN_ON_THREAD.store(true, std::sync::atomic::Ordering::Relaxed);
    let t = match std::thread::Builder::new()
        .name("main".into())
        .stack_size(main_stack_size())
        .spawn(move || {
            install_stack_overflow_handler();
            body()
        }) {
        Ok(t) => t,
        // Native `lean_run_main` throws `lean::exception("failed to create
        // thread")`, which nothing catches.
        Err(_) => thread_create_failed(),
    };
    if t.join().is_err() {
        // A Rust panic of `main`'s thread (a runtime bug): exit as a Rust
        // program does, with the streams written.
        crate::io::exit(101);
    }
}

/// `System.Platform.target` (`lean_system_platform_target`). Natively it is
/// `LEAN_PLATFORM_TARGET` (`version.h`), the target triple the Lean
/// toolchain was built for: `clang --print-target-triple` on Lean's CI, the
/// triple `lean --version` shows. Here, the triple the native toolchain for
/// leanrt's own target reports. leanrt builds only for Linux with glibc on
/// aarch64 and x86-64 (its signal structures, the glibc `FILE` model, the
/// stack switching in `coro`); the prelude's other platform answers
/// (Windows, macOS and Emscripten false, `numBits` 64) rely on that too.
#[cfg(all(target_os = "linux", target_env = "gnu", target_arch = "aarch64"))]
pub const PLATFORM_TARGET: &str = "aarch64-unknown-linux-gnu";
#[cfg(all(target_os = "linux", target_env = "gnu", target_arch = "x86_64"))]
pub const PLATFORM_TARGET: &str = "x86_64-unknown-linux-gnu";
#[cfg(not(all(target_os = "linux", target_env = "gnu", any(target_arch = "aarch64", target_arch = "x86_64"))))]
compile_error!(
    "leanrt supports Linux with glibc on aarch64 and x86-64 only: for another target, add the triple \
     the native Lean toolchain reports (`lean --version`) to `PLATFORM_TARGET` and review the \
     prelude's platform queries (`lean_system_platform_*`)"
);
