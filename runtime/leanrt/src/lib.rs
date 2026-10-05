//! `leanrt`: the Rust half of lean2rr's runtime.
//!
//! The Reussir prelude (`runtime/prelude.rr`) implements each Lean extern:
//! fast paths in Reussir, everything else through small `#[ffi(import)]`
//! textures that call into this crate. Keeping the code here (rather than in
//! the prelude's `extern "rust"` block, which is copied into every texture)
//! keeps texture compilation cheap and gives the runtime one copy of its
//! global state: the last-error slot, once-cells, and panic settings.
//! Lean's runtime behaviour itself is the shared crate lean-runtime's
//! (`lean_runtime`): its `semantics` (hashes, strings, floats, numbers,
//! panics), its `io` (files, streams, processes, the system, the exit), its
//! `sched` (tasks, promises, `Std.Sync`, the event loop, timers, signals,
//! the stack-overflow report) and its `net` (sockets, name resolution); the
//! modules here convert lean2rr's values to its views and back, and are the
//! glue its scheduler asks of a translator (`sched`, `task`).
//!
//! Small hot functions are `#[inline]` so they are instantiated into the
//! textures (and can be inlined into Reussir code); slow paths are
//! `#[inline(never)]`. The cold paths of hot textures are `extern "C"`
//! (they cannot unwind: runtime failures exit or abort), so calls to them
//! need no landing pads, which keeps the textures under LLVM's inlining
//! threshold.

#![allow(improper_ctypes_definitions)]
#![allow(incomplete_features)]
#![feature(linkage)]
#![feature(specialization)]

extern crate reussir_rt;

pub mod alloc;
pub mod array;
pub mod big;
pub mod drop;
pub mod float;
pub mod fs;
pub mod gmp;
pub mod io;
pub mod nat;
pub mod net;
pub mod once;
pub mod persist;
pub mod proc;
pub mod refs;
pub mod rt;
pub mod sched;
pub mod string;
pub mod sync;
pub mod sys;
pub mod tagvec;
pub mod task;

pub use big::LBig;
pub use nat::{LInt, LNat};
pub use string::LStr;

/// The Lean version whose runtime the shared crate `lean_runtime` mirrors
/// (lean-runtime, the submodule `third_party/lean-runtime`, which
/// `scripts/l2r.py` builds and links with leanrt). It must be the version
/// lean2rr is pinned to, which the prelude's `lean_version_get_*` give: the
/// test `tests::lean_runtime_version_is_the_preludes` checks it.
pub use lean_runtime::LEAN_VERSION;

static LAST_SHARED: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

/// `dbgTraceIfShared`'s check, recorded for the prelude to read back.
pub fn set_last_shared(b: bool) {
    LAST_SHARED.store(b, std::sync::atomic::Ordering::Relaxed)
}

pub fn last_shared() -> bool {
    LAST_SHARED.load(std::sync::atomic::Ordering::Relaxed)
}

/// A fresh "address" for `ptrAddrUnsafe` of a value whose handle is not one
/// word (`l2r_ptr_addr_obj`) and of a Reussir type lean2rr's `addrOf` does
/// not know (a `Nat` or `Int` answers its own word, as natively): never
/// repeated, even (so never a boxed scalar, whose "address" is odd) and in
/// `[2^62, 2^63)` (so never a real pointer).
pub fn fresh_addr() -> u64 {
    static NEXT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(1 << 62);
    NEXT.fetch_add(2, std::sync::atomic::Ordering::Relaxed)
}

/// Give up a handle a texture received by value but only borrowed (every
/// FFI call consumes its arguments). A shared handle is just decremented;
/// freeing the last reference is out of line, which keeps textures small
/// enough for LLVM to inline them into Reussir code.
#[inline(always)]
pub fn rc_release<R: Release>(r: R) {
    r.release()
}

/// A counted handle that `rc_release` gives up: Reussir's `Rc` and the
/// runtime's own one-block objects (`string::LStr`, `tagvec::TagVec`).
pub trait Release {
    fn release(self);
}

impl<T> Release for reussir_rt::rc::Rc<T> {
    #[inline(always)]
    fn release(self) {
        let c = self.count_ref().get();
        if c == 1 {
            rc_drop_last(self)
        } else {
            self.count_ref().set(c - 1);
            std::mem::forget(self);
        }
    }
}

#[cold]
#[inline(never)]
extern "C" fn rc_drop_last<T>(r: reussir_rt::rc::Rc<T>) {
    drop(r)
}

use lean_runtime::semantics::panic::{self as sem_panic, InternalPanic, PanicEnd, PanicSettings, PanicStream};

/// The settings Lean's panics read (`sem_panic::PanicSettings`): the
/// environment variables `LEAN_ABORT_ON_PANIC` and `LEAN_BACKTRACE`, read
/// at each panic as natively; exit-on-panic and panic messages keep their
/// defaults (lean2rr has no `Lean.Internal` setters).
pub fn panic_settings() -> PanicSettings {
    use std::os::unix::ffi::OsStrExt;
    let abort = std::env::var_os("LEAN_ABORT_ON_PANIC");
    let backtrace = std::env::var_os("LEAN_BACKTRACE");
    PanicSettings::from_env(abort.as_deref().map(|v| v.as_bytes()), backtrace.as_deref().map(|v| v.as_bytes()))
}

/// The lines `lean_panic_impl` prints for `msg` under `plan`
/// (`sem_panic::panic_fn_plan`): the message, then, with backtraces on,
/// `backtrace:` and the frames: none here, but the line of a runtime
/// without backtrace support (`sem_panic::NO_BACKTRACE`). Natively each
/// line is one `io_eprintln`; here they are one text.
fn panic_lines(msg: &[u8], plan: sem_panic::PanicPlan) -> Vec<u8> {
    let mut t = Vec::new();
    if plan.print {
        t.extend_from_slice(msg);
        t.push(b'\n');
        if plan.backtrace {
            t.extend_from_slice(sem_panic::BACKTRACE_HEADER.as_bytes());
            t.push(b'\n');
            t.extend_from_slice(sem_panic::NO_BACKTRACE.as_bytes());
            t.push(b'\n');
        }
    }
    t
}

/// How a panic whose plan ends the process ends it (after its lines).
fn panic_end(end: PanicEnd) -> ! {
    match end {
        PanicEnd::Abort => std::process::abort(),
        // `std::exit(1)`, which flushes C's streams.
        _ => io::exit(sem_panic::PANIC_EXIT_STATUS),
    }
}

/// `lean_panic_fn`'s output (Lean has already formatted the message as
/// `PANIC at ...`), by `sem_panic::panic_fn_plan`: when the process goes
/// on, the lines for Lean's current stderr stream (`IO.setStderr`), which
/// the prelude writes through the program's `l2r_stderr_put`; when the plan
/// ends the process (`LEAN_ABORT_ON_PANIC`), this does not return: the
/// lines go to the process's stderr, `std::cerr`, which is tied to
/// `std::cout`, so stdout is flushed first, and the process aborts.
/// `extern "C"` (it cannot unwind): the prelude's texture inlines into the
/// panicking Reussir code as a plain call, with no landing pad.
#[inline(never)]
pub extern "C" fn panic_text(msg: LStr) -> LStr {
    use string::Utf8;
    let plan = sem_panic::panic_fn_plan(panic_settings());
    let t = panic_lines(msg.utf8(), plan);
    if plan.stream == PanicStream::ProcessStderr {
        // An output: an effect point first (the prelude writes the other
        // stream's lines through the current stderr's `putStr`, one too).
        if plan.print {
            sched::effect();
        }
        io::flush_stdout();
        io::eprint(&t);
    }
    if plan.end != PanicEnd::Return {
        panic_end(plan.end)
    }
    rc_release(msg);
    string::from_bytes(&t)
}

/// `lean_internal_panic` (`sem_panic::InternalPanic`): `INTERNAL PANIC: `
/// and the message straight to stderr, then `exit(1)` (which flushes stdout
/// afterwards), or `abort()` without flushing under `LEAN_ABORT_ON_PANIC`
/// (`sem_panic::internal_panic_end`). `extern "C"`, as `panic_text`.
#[cold]
#[inline(never)]
pub extern "C" fn lean_internal_panic(p: InternalPanic) -> ! {
    internal_panic(p.message())
}

/// `lean_internal_panic` with a message of its own: Lean's
/// (`lean_internal_panic`) for a runtime invariant of lean2rr's that does
/// not hold.
#[cold]
#[inline(never)]
pub fn internal_panic(msg: &str) -> ! {
    let mut line = sem_panic::INTERNAL_PANIC_PREFIX.as_bytes().to_vec();
    line.extend_from_slice(msg.as_bytes());
    line.push(b'\n');
    io::eprint(&line);
    match sem_panic::internal_panic_end(panic_settings()) {
        PanicEnd::Abort => std::process::abort(),
        _ => io::exit(sem_panic::PANIC_EXIT_STATUS),
    }
}

/// An uncaught `IO` exception at the top level, of `main` or of an
/// initializer: as a native program's C `main`, the io layer's dedicated
/// tasks are waited for (`lean_finalize_task_manager`,
/// `io::exit::after_main`), then `lean_io_result_show_error` prints
/// `uncaught exception: ` and the error's text up to its first NUL
/// (`string_cstr`) with `std::cerr` (which flushes stdout first;
/// lean-runtime's `io::exit::show_error`), and the process exits with
/// status 1.
#[inline(never)]
pub fn uncaught_exception<M: string::Utf8 + ?Sized>(msg: &M) -> ! {
    lean_runtime::io::exit::after_main();
    lean_runtime::io::exit::show_error(msg.utf8());
    io::exit(sem_panic::PANIC_EXIT_STATUS)
}

/// A Lean panic of the runtime (`lean_panic(msg, force_stderr)`), by
/// lean-runtime's `lean_panic_plan`: an effect point, as for any output; the
/// lines on Lean's current stderr stream (`io_eprintln`, which
/// `IO.setStderr` redirects: the program's `l2r_stderr_put`), or, forced or
/// when the process is about to end, on the process's stderr (`std::cerr`:
/// C's `stdout` flushed first); then the abort or the exit the plan says;
/// otherwise it returns and the program goes on. Used for `Task.get` in a
/// `sync := true` task (lean-runtime's `GET_IN_SYNC_TASK`) and
/// `Promise.result!` of a dropped promise (`PROMISE_DROPPED`, forced).
#[inline(never)]
pub fn lean_panic(msg: &[u8], force_stderr: bool) {
    let plan = sem_panic::lean_panic_plan(panic_settings(), force_stderr);
    if plan.print {
        sched::effect();
        let t = panic_lines(msg, plan);
        match plan.stream {
            PanicStream::LeanStderr => io::diag_put(string::from_bytes(&t)),
            PanicStream::ProcessStderr => {
                io::flush_stdout();
                io::eprint(&t);
            }
        }
    }
    if plan.end != PanicEnd::Return {
        panic_end(plan.end)
    }
}

/// `Option.getOrBlock!` on `none` (`Promise.result!` of a dropped promise):
/// lean-runtime's `option_get_or_block`, which reports the forced panic
/// message (`lean_panic` above, `force_stderr`), wakes the waiters of the
/// walks in progress on this context (LB-32) and then blocks the running
/// context forever, as natively the calling thread sleeps forever (the
/// other tasks and `main` go on).
#[inline(never)]
pub fn promise_dropped() -> ! {
    let () = lean_runtime::sched::option_get_or_block(None, |msg| lean_panic(msg.as_bytes(), true));
    unreachable!("lean-runtime's option_get_or_block returned on none")
}

#[cfg(test)]
mod tests {
    /// lean-runtime mirrors the Lean version lean2rr is pinned to: the
    /// prelude's `lean_version_get_major`/`minor`/`patch` (`l2r_nat_small(N)`)
    /// spell `lean_runtime::LEAN_VERSION`. Fails when the submodule's pin and
    /// lean2rr's toolchain disagree.
    #[test]
    fn lean_runtime_version_is_the_preludes() {
        let prelude = include_str!("../../prelude.rr");
        let part = |name: &str| -> String {
            let head = format!("fn lean_version_get_{name}(");
            let line = prelude.lines().find(|l| l.starts_with(&head)).expect(&head);
            let n = line.split("l2r_nat_small(").nth(1).expect(line);
            n[..n.find(')').expect(line)].to_string()
        };
        let prelude_version = format!("{}.{}.{}", part("major"), part("minor"), part("patch"));
        assert_eq!(prelude_version, lean_runtime::LEAN_VERSION);
    }
}
