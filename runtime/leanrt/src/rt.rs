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

extern "C" {
    fn sigaction(sig: i32, act: *const SigAction, old: *mut SigAction) -> i32;
    fn sigaltstack(ss: *const StackT, old: *mut StackT) -> i32;
    fn pthread_self() -> usize;
    fn pthread_getattr_np(th: usize, attr: *mut [u64; 16]) -> i32;
    fn pthread_attr_getstack(attr: *const [u64; 16], addr: *mut *mut c_void, size: *mut usize) -> i32;
    fn pthread_attr_destroy(attr: *mut [u64; 16]) -> i32;
    fn sysconf(name: i32) -> i64;
    fn abort() -> !;
    fn write(fd: i32, buf: *const c_void, n: usize) -> isize;
}

/// `is_within_stack_guard`: the page just below the current thread's stack.
unsafe fn is_within_stack_guard(addr: usize) -> bool {
    let mut attr = [0u64; 16];
    if unsafe { pthread_getattr_np(pthread_self(), &mut attr) } != 0 {
        return false;
    }
    let mut stackaddr: *mut c_void = std::ptr::null_mut();
    let mut size = 0usize;
    unsafe {
        pthread_attr_getstack(&attr, &mut stackaddr, &mut size);
        pthread_attr_destroy(&mut attr);
    }
    let guard = unsafe { sysconf(SC_PAGESIZE) } as usize;
    let lo = stackaddr as usize;
    lo.wrapping_sub(guard) <= addr && addr < lo
}

extern "C" fn segv_handler(signum: i32, info: *mut SigInfo, _ctx: *mut c_void) {
    unsafe {
        if is_within_stack_guard((*info).si_addr as usize) {
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
        let sp = std::alloc::alloc(std::alloc::Layout::from_size_align(ALTSTACK_SIZE, 16).unwrap());
        if !sp.is_null() {
            let ss = StackT { ss_sp: sp as *mut c_void, ss_flags: 0, ss_size: ALTSTACK_SIZE };
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
    if let Some(kb) = std::env::var("LEAN_STACK_SIZE_KB").ok().and_then(|v| v.trim().parse::<u64>().ok()) {
        let sz = (kb / 4 * 4 * 1024) as usize;
        if sz > 0 {
            return sz + 128 * 1024;
        }
    }
    1 << 30
}

/// Run the program's main body as Lean does (`lean_run_main`): on a thread
/// with Lean's main stack size (unless `LEAN_MAIN_USE_THREAD=0`), with
/// Lean's stack-overflow report, and wait for it.
pub fn run_main<F: FnOnce() + Send + 'static>(body: F) {
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
