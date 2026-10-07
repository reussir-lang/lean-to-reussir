//! Process-level runtime: the startup glue lean-runtime's io asks of a
//! translator (`io::startup`): native Lean's startup descriptors, `main` on
//! a thread of its own with Lean's stack (`lean_run_main`), Lean's
//! stack-overflow report on each thread that runs Lean code, and
//! `IO.initializing`'s end.
//!
//! The startup descriptors (libuv's loop: epoll, the io_uring rings, the
//! signal lock pipe, the signal pipe, the eventfd, numbers 3 to 10 when the
//! standard ones are open) are opened by lean-runtime's own ELF constructor
//! (feature `startup-fds`, `.init_array.00101`), before Rust's runtime puts
//! `/dev/null` in the place of a closed standard descriptor, so a closed
//! standard descriptor is taken by the first of them, as natively. The glue
//! calls `io::startup::ensure_native_descriptors` at the start of `main`
//! (`run_main2`), which keeps the constructor linked and, if it did not act
//! (no `/proc`, a launch through the dynamic loader), opens them where they
//! land. When they cannot be made, the program does not reach `main`:
//! lean-runtime ends it with `INTERNAL PANIC: Failed to initialize event
//! loop: ...` and exit status 1, where native crashes (LB-30) or aborts
//! (LB-31).
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
//! (the initializers) and `main`'s thread (the body `run_main2` gives
//! `io::startup::run_main`); the scheduler's contexts need nothing more. The
//! program's `main` is Reussir's launcher, a Rust `main`: std's runtime start
//! installs Rust's handler first, which lean-runtime's keeps as the previous
//! action (a fault that is no Lean stack overflow goes there).

/// Lean's stack-overflow report on the calling thread (lean-runtime's; see
/// the module comment).
pub fn install_stack_overflow_handler() {
    lean_runtime::sched::install_stack_overflow_handler()
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

/// Run a program as Lean's generated C `main` does: `init` (the module
/// initializers) on the calling thread (the process's main thread, with its
/// usual stack, so deep initializers overflow as natively), then `body` as
/// `lean_run_main` does, on a thread of its own with Lean's main stack size
/// (lean-runtime's `io::startup::run_main` with `sched::thread_stack_size`:
/// 1 GiB on 64-bit targets, or `LEAN_STACK_SIZE_KB` rounded down to 4 KiB
/// plus 128 KiB), or on the calling thread with `LEAN_MAIN_USE_THREAD=0`.
/// Both have Lean's stack-overflow report. `init` decides itself whether to
/// continue (an initializer's uncaught error exits); `IO.initializing` is
/// the caller's business (`set_initializing`). `body` holds the whole of
/// `main`'s life with tasks (the generated `l2r_main_body`:
/// `task::start`, the program's `main`, then `task::shutdown`), since the
/// scheduler's state is the thread's own.
pub fn run_main2<I: FnOnce(), F: FnOnce() + Send + 'static>(init: I, body: F) {
    // The program's releases of its boxed payloads, before any box is made
    // and before any other thread runs (`any::RELEASES`).
    crate::any::init_releases();
    lean_runtime::io::startup::ensure_native_descriptors();
    install_stack_overflow_handler();
    init();
    let ran = lean_runtime::io::startup::run_main(lean_runtime::sched::thread_stack_size(), move || {
        install_stack_overflow_handler();
        body()
    });
    if ran.is_err() {
        // A Rust panic (a runtime bug) that unwound out of the body: only
        // one raised in the glue's own frames (the closure above,
        // `install_stack_overflow_handler`) gets here; exit as a Rust program
        // does, with the streams written. A panic inside the generated code
        // (`l2r_main_body` and every frame below it, the runtime's textures
        // included) cannot unwind through it: Rust reports "panic in a
        // function that cannot unwind" and aborts (status 134, buffered
        // stdout lost), in both modes, as before switch step 7.
        crate::io::exit(101);
    }
}

/// Whether `main` runs on a thread of its own (lean-runtime's
/// `io::startup::main_on_thread`, set by `run_main2` before `body` starts).
/// With `LEAN_MAIN_USE_THREAD=0` it runs on the initializers' thread and, as
/// natively, keeps that thread's current standard streams (lean2rr's entry
/// starts a fresh stream context for `main` only when this is true).
pub fn main_on_thread() -> bool {
    lean_runtime::io::startup::main_on_thread()
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
