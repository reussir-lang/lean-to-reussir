//! Process-level runtime: running `main` on a large stack, Lean's stack
//! overflow report, and the startup glue lean-runtime's io asks of a
//! translator (`io::startup`): the ELF constructor that opens native Lean's
//! startup descriptors, and `IO.initializing`'s end.
//!
//! Lean's stack-overflow report (`src/runtime/stack_overflow.cpp`: a
//! SIGSEGV/SIGBUS handler on an alternate signal stack in every thread that
//! runs Lean code; a fault in the guard page below the faulting thread's
//! stack, or below the stack of the scheduler's context running on it,
//! prints `\nStack overflow detected. Aborting.\n` and aborts, status 134,
//! buffered stdout lost; any other fault takes the default action) is
//! lean-runtime's (`sched::install_stack_overflow_handler`, feature
//! `stack-overflow`, a native quirk written with `unsafe`: its UNSAFE.md and
//! docs/native-quirks.md). The glue's duty is the call, once per OS thread
//! that runs Lean code, at that thread's entry: the process's main thread
//! (the initializers) and `main`'s thread (`run_main2`, `run_body`); the
//! scheduler's contexts need nothing more. The program's `main` is Reussir's
//! launcher, a Rust `main`: std's runtime start installs Rust's handler
//! first, which lean-runtime's keeps as the previous action (a fault that is
//! no Lean stack overflow goes there).

/// Lean's stack-overflow report on the calling thread (lean-runtime's; see
/// the module comment).
pub fn install_stack_overflow_handler() {
    lean_runtime::sched::install_stack_overflow_handler()
}

/// The stack size of Lean's main thread (`lean_run_main`), the same as its
/// worker threads' (`lthread`): 1 GiB on 64-bit targets, or
/// `LEAN_STACK_SIZE_KB` (rounded down to 4 KiB) plus a 128 KiB buffer
/// (lean-runtime's `sched::thread_stack_size`, which also sizes the
/// scheduler's contexts).
fn main_stack_size() -> usize {
    lean_runtime::sched::thread_stack_size()
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
    crate::alloc::heap_on_huge_pages();
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
    crate::alloc::heap_on_huge_pages();
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
        // thread: " << strerror(err))`, which nothing catches: libc++
        // reports it and aborts (lean-runtime's text, as for its workers).
        Err(e) => lean_runtime::sched::thread_create_failed(&e),
    };
    if t.join().is_err() {
        // A Rust panic of `main`'s thread (a runtime bug): exit as a Rust
        // program does, with the streams written.
        crate::io::exit(101);
    }
}

// `System.Platform.target` and the other toolchain facts are lean-runtime's
// (`semantics::toolchain`). leanrt builds only for Linux with glibc on
// aarch64 and x86-64 (the glibc `FILE` model, lean-runtime's targets): the
// prelude's other platform answers (Windows, macOS and Emscripten false,
// `numBits` 64) rely on that.
#[cfg(not(all(target_os = "linux", target_env = "gnu", any(target_arch = "aarch64", target_arch = "x86_64"))))]
compile_error!(
    "leanrt supports Linux with glibc on aarch64 and x86-64 only: for another target, check \
     lean-runtime's `semantics::toolchain::PLATFORM_TARGET` against the triple the native Lean \
     toolchain reports (`lean --version`) and review the prelude's platform queries \
     (`lean_system_platform_*`)"
);
