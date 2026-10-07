//! `leanrt`: the Rust half of lean2rr's runtime.
//!
//! The Reussir prelude (`runtime/prelude.rr`) implements each Lean extern:
//! fast paths in Reussir, everything else through small `#[ffi(import)]`
//! textures that call into this crate. Keeping the code here (rather than in
//! the prelude's `extern "rust"` block, which is copied into every texture)
//! keeps texture compilation cheap and gives the runtime one copy of its
//! global state: the last-error slot and once-cells.
//! Lean's runtime behaviour itself is the shared crate lean-runtime's
//! (`lean_runtime`): its `semantics` (hashes, strings, floats, numbers,
//! panics), its `io` (files, streams, processes, the system, the exit, the
//! panic and exit executor), its
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
#![feature(ptr_mask)]
#![feature(specialization)]

extern crate reussir_rt;

pub mod alloc;
pub mod any;
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

/// `dbgTraceIfShared`'s test (the prelude's `lean_dbg_trace_if_shared` and
/// `l2r_shared_check`): whether `a`, a value of the storage type `T` (the
/// textures' `[:T:]`), is a heap object that another reference also holds.
/// Natively `!lean_is_scalar(a) && !lean_is_exclusive(a)`. By `T`:
/// - a one-word box (`any::LAny`) answers for its payload; an immediate is
///   never shared;
/// - a `Nat` or `Int` (`nat::LNat`, `nat::LInt`): an even word is a big
///   number, whose block starts with its `u32` count; an odd word is a small
///   value, a scalar natively (review HL-01: the big numbers were never
///   reported);
/// - a one-word handle of Reussir (`reussir_rt::`: records, through
///   `Bridge`, and runtime objects) or of leanrt (`string::`, and `drop::`:
///   arrays, `ByteArray`, `FloatArray`, the cells of thunks and tasks): the
///   `u32` count at the pointer. A Reussir immediate (a nullary
///   constructor, a scalar natively) is not shared: its top byte is not zero
///   (the `tbi` encoding), or it points to a dummy box whose count is 2^31
///   or more (the `immortal` encoding);
/// - any other type (scalars, and the fresh wrappers lean2rr passes values
///   that cannot cross the boundary in) is never shared.
///
/// A task that one reference holds is not shared; natively a task that
/// `Task.spawn` made is multi-threaded, so never exclusive (a documented
/// difference).
#[inline]
pub fn is_shared<T>(a: &T) -> bool {
    let name = std::any::type_name::<T>();
    if name == "leanrt::any::LAny" {
        return !unsafe { &*(a as *const T as *const any::LAny) }.is_exclusive();
    }
    let counted = name.starts_with("reussir_rt::")
        || name.starts_with("leanrt::string::")
        || name.starts_with("leanrt::drop::")
        || name.starts_with("leanrt::nat::");
    if !counted || std::mem::size_of::<T>() != std::mem::size_of::<usize>() {
        return false;
    }
    let p = unsafe { *(a as *const T as *const usize) };
    if p & 1 != 0 || p >> 56 != 0 {
        return false;
    }
    let c = unsafe { *(p as *const u32) };
    c != 1 && c < drop::IMMORTAL
}

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
/// runtime's own one-block objects (`string::LStr`).
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

use lean_runtime::io::panic::{self as xpanic, Native, PanicGlue};
use lean_runtime::semantics::panic::{InternalPanic, PanicPlan, PanicStream};

/// lean2rr's glue for lean-runtime's panic executor (`io::panic`, which
/// carries out a panic's plan: the settings read at each panic, the effect
/// point, the stream, the flush of stdout, the abort or the exit). Two
/// choices of lean2rr's are kept (lean-runtime docs/panic.md, rows 3 and 4):
/// - Lean's current stderr stream (`IO.setStderr`) is lean2rr's own (its
///   stream cells, the program's `l2r_stderr_put`), so the lines of a panic
///   that goes on are collected here and written with one `putStr` by the
///   caller (natively one `putStr` per line; only a stream whose `putStr` is
///   not plain concatenation, with backtraces on, sees the difference);
/// - `panicCore`'s effect point (`panic_text`) is made only when the lines
///   go to the process's stderr: on Lean's stream, the default stream's
///   `putStr` makes one (a stream of `IO.setStderr` none).
///
/// Everything else is the executor's default (native's behaviour on
/// lean-runtime's streams): the process's stderr and stdout, the abort and
/// `exit(1)`.
struct Collect {
    lines: Vec<u8>,
    /// `panicCore` (`panic_text`): an effect point only on the process's
    /// stderr; on Lean's stream, the stream's own `putStr` has one.
    effect_only_on_process_stderr: bool,
}

impl PanicGlue for Collect {
    fn lean_eprintln(&mut self, line: &[u8]) {
        self.lines.extend_from_slice(line);
        self.lines.push(b'\n');
    }

    fn panic_effect(&mut self, plan: PanicPlan) {
        if !self.effect_only_on_process_stderr || plan.stream == PanicStream::ProcessStderr {
            sched::effect();
        }
    }
}

/// `lean_panic_fn`'s output (Lean has already formatted the message as
/// `PANIC at ...`), by lean-runtime's `io::panic::report` (`force_stderr`
/// off): when the process goes on, the lines for Lean's current stderr
/// stream (`IO.setStderr`), which the prelude writes through the program's
/// `l2r_stderr_put`; when the plan ends the process (`LEAN_ABORT_ON_PANIC`),
/// this does not return: an effect point, stdout flushed (`std::cerr` is
/// tied to `std::cout`), the lines on the process's stderr, the abort.
/// `extern "C"` (it cannot unwind): the prelude's texture inlines into the
/// panicking Reussir code as a plain call, with no landing pad.
#[inline(never)]
pub extern "C" fn panic_text(msg: LStr) -> LStr {
    use string::Utf8;
    let mut g = Collect { lines: Vec::new(), effect_only_on_process_stderr: true };
    xpanic::report(msg.utf8(), false, &mut g);
    rc_release(msg);
    string::from_bytes(&g.lines)
}

/// `lean_internal_panic` (`semantics::panic::InternalPanic`), by
/// lean-runtime's `io::panic::internal_panic`. `extern "C"`, as
/// `panic_text`.
#[cold]
#[inline(never)]
pub extern "C" fn lean_internal_panic(p: InternalPanic) -> ! {
    xpanic::internal_panic(p.message(), &mut Native)
}

/// `lean_internal_panic(Unreachable)`: the runtime's reads at a `Nat`
/// index or position that a proof keeps in bounds, when it is a big number
/// (`l2r_index_of_nat`'s panic; natively `lean_unbox` of it is garbage).
#[cold]
#[inline(never)]
pub extern "C" fn unreachable_code() -> ! {
    lean_internal_panic(InternalPanic::Unreachable)
}

/// The value of the word `x` of a `Nat` index or position that a proof
/// keeps in bounds; a big one is unreachable code (`unreachable_code`).
#[inline(always)]
pub fn index_word(x: u64) -> u64 {
    if (x & 1) == 1 {
        x >> 1
    } else {
        unreachable_code()
    }
}

/// `lean_internal_panic` with a message of its own: Lean's
/// (`lean_internal_panic`) for a runtime invariant of lean2rr's that does
/// not hold. lean-runtime's `io::panic::internal_panic`: `INTERNAL PANIC: `,
/// the message and a newline, built on the stack and written straight to
/// descriptor 2 (with no allocation; under lean-runtime's `stderr` lock
/// unless this thread holds it or the program has a task, a promise, a timer
/// or a watch), then `exit(1)` (which flushes stdout afterwards), or
/// `abort()` without flushing under `LEAN_ABORT_ON_PANIC`.
#[cold]
#[inline(never)]
pub fn internal_panic(msg: &str) -> ! {
    xpanic::internal_panic(msg, &mut Native)
}

/// An uncaught `IO` exception at the top level, of `main` or of an
/// initializer, by lean-runtime's `io::panic::uncaught`: as a native
/// program's C `main`, the io layer's dedicated tasks are waited for
/// (`lean_finalize_task_manager`, `io::exit::after_main`), then
/// `lean_io_result_show_error` prints `uncaught exception: ` and the error's
/// text up to its first NUL (`string_cstr`) with `std::cerr` (which flushes
/// stdout first), and the process exits with status 1.
#[inline(never)]
pub fn uncaught_exception<M: string::Utf8 + ?Sized>(msg: &M) -> ! {
    xpanic::uncaught(msg.utf8(), &mut Native)
}

/// A Lean panic of the runtime (`lean_panic(msg, force_stderr)`), by
/// lean-runtime's `io::panic::report`: an effect point, as for any output;
/// the lines on Lean's current stderr stream (`io_eprintln`, which
/// `IO.setStderr` redirects: the program's `l2r_stderr_put`, one `putStr`
/// here), or, forced or when the process is about to end, on the process's
/// stderr (`std::cerr`: C's `stdout` flushed first); then the abort or the
/// exit the plan says; otherwise it returns and the program goes on. Used
/// for `Task.get` in a `sync := true` task (lean-runtime's
/// `GET_IN_SYNC_TASK`) and `Promise.result!` of a dropped promise
/// (`PROMISE_DROPPED`, forced).
#[inline(never)]
pub fn lean_panic(msg: &[u8], force_stderr: bool) {
    let mut g = Collect { lines: Vec::new(), effect_only_on_process_stderr: false };
    xpanic::report(msg, force_stderr, &mut g);
    if !g.lines.is_empty() {
        io::diag_put(string::from_bytes(&g.lines))
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
    /// lean2rr's panic glue (`Collect`) keeps the lines of a panic that goes
    /// on for one `putStr` of Lean's current stderr stream (lean-runtime
    /// docs/panic.md, row 3): the message, then, with backtraces on,
    /// `backtrace:` and lean-runtime's stand-in for the frames, each with its
    /// newline, in one text; lean-runtime's executor writes nothing itself.
    #[test]
    fn panic_lines_are_collected_for_one_put() {
        use lean_runtime::io::panic as xpanic;
        if xpanic::abort_on_panic() {
            return; // the plan would end the test process
        }
        for effect_only_on_process_stderr in [true, false] {
            let mut g = super::Collect { lines: Vec::new(), effect_only_on_process_stderr };
            xpanic::report(b"PANIC at f", false, &mut g);
            let want: &[u8] = if xpanic::settings().backtrace {
                b"PANIC at f\nbacktrace:\n(stack trace unavailable)\n"
            } else {
                b"PANIC at f\n"
            };
            assert_eq!(g.lines, want);
        }
    }

    /// `is_shared` (`dbgTraceIfShared`): each storage type's own count; a
    /// small number, an immediate and a scalar are never shared.
    #[test]
    fn shared_by_storage_type() {
        use super::is_shared;
        use crate::any::{self, LAny};
        use crate::nat::{LInt, LNat};
        // Nat and Int: a small value is a scalar; a big one has a count.
        assert!(!is_shared(&LNat::of_u64(5)));
        let b = LNat::of_u64(u64::MAX);
        assert!(!is_shared(&b));
        let b2 = b.clone();
        assert!(is_shared(&b) && is_shared(&b2));
        drop(b2);
        assert!(!is_shared(&b));
        let i = LInt::of_i64(i64::MIN);
        let i2 = i.clone();
        assert!(is_shared(&i));
        drop(i2);
        assert!(!is_shared(&i));
        assert!(!is_shared(&LInt::of_i64(-3)));
        // Strings and arrays (`ByteArray` here).
        let s = crate::string::from_bytes(b"abc");
        assert!(!is_shared(&s));
        let s2 = s.clone();
        assert!(is_shared(&s));
        drop(s2);
        let v = crate::array::push(crate::array::empty::<u8>(), 7);
        assert!(!is_shared(&v));
        let v2 = v.clone();
        assert!(is_shared(&v));
        drop(v2);
        assert!(!is_shared(&v));
        // A box answers for its payload; an immediate is not shared.
        let a = any::of(crate::string::from_bytes(b"boxed"), any::NUM_STR);
        assert!(!is_shared(&a));
        let a2 = a.clone();
        assert!(is_shared(&a));
        drop(a2);
        assert!(!is_shared(&LAny::imm(3)));
        // Scalars.
        assert!(!is_shared(&7u64) && !is_shared(&1.5f64) && !is_shared(&true));
    }

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

    /// lean2rr numbers the `IO.Error` builders as lean-runtime does
    /// (`IoError::builder_index`, `IO_ERROR_BUILDERS`): the error paths of
    /// the generated code (`ioErrorBuilderSyms`, Mono.lean) and the shim's
    /// `ioErrorOf` (L2RShim.lean) build the error the index names.
    #[test]
    fn io_error_builders_are_lean_runtimes() {
        use lean_runtime::io::error::IO_ERROR_BUILDERS;
        let mono = include_str!("../../../lean2rr/LeanToReussir/Mono.lean");
        let start = mono.find("def ioErrorBuilderSyms : Array String := #[").expect("ioErrorBuilderSyms");
        let list = &mono[start..start + mono[start..].find(']').expect("ioErrorBuilderSyms's end")];
        let syms: Vec<&str> = list.split('"').skip(1).step_by(2).collect();
        assert_eq!(syms, IO_ERROR_BUILDERS);
        // `| k => .mkSomeThing ...`: `mk` and the builder's words after
        // `lean_mk_io_error_`, capitalized (index 0, `other_error`, is the
        // match's default; 23 is `userError`).
        let shim = include_str!("../../../lean2rr/L2RShim.lean");
        for (k, sym) in IO_ERROR_BUILDERS.iter().enumerate().skip(1) {
            let ctor = match sym.strip_prefix("lean_mk_io_error_") {
                Some(words) => {
                    let camel: String = words
                        .split('_')
                        .map(|w| w[..1].to_uppercase() + &w[1..])
                        .collect();
                    format!(".mk{camel} ")
                }
                None => ".userError ".to_string(),
            };
            let arm = format!("  | {k} => {ctor}");
            assert!(shim.contains(&arm), "L2RShim.ioErrorOf lacks `{arm}` for {sym}");
        }
    }
}
