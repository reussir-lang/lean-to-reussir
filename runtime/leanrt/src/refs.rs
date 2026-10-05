//! `ST.Ref` in a program that creates tasks: lean-runtime's glue items 5
//! and 7, with Lean 4.35's rule (lean-runtime's `docs/lean-bugs.md`, LB-01
//! and LB-18).
//!
//! lean2rr decides at translation time whether a program creates tasks (an
//! extern that makes a task or a promise is reachable:
//! `programCreatesTasks`; every other context comes from those). Only then
//! do its reference operations call the points below, before the cell
//! operation itself (prelude `l2r_ref_*_point`, `l2r_ref_wait`,
//! `l2r_ref_take_mark`). A program without tasks has one context, so its
//! reference operations stay plain cell operations and call nothing here.
//!
//! - A read (`get`, `swap`, `take`) is a polling point: lean-runtime's
//!   `ref_read`, every 1000th read on the thread, once the first task has
//!   turned it on (`task::ensure_started`). So a loop that polls a
//!   reference another task sets ends, as natively.
//! - A write (`set`, `swap`, `take`) first calls `before_publish`: the
//!   streams the context handed off are written before another context can
//!   see the write.
//! - `ST.Ref.modify` is `take`, then `set` (`ST.Prim.Ref.modifyUnsafe`).
//!   `take` empties the reference (its cell gets a placeholder) and records
//!   it here as taken by the running thread. Until that thread stores into it
//!   again (modify's own `set` or `swap`), the other threads' `get`, `take`,
//!   `set` and `swap` wait: the context blocks and is woken by that store.
//!   A thread is a context and, on it, the thread number of the task
//!   running there (lean-runtime's `thread_number`: a task run on the stack
//!   of the context that waits for it is natively another worker thread).
//! - The taking thread's own operations do not wait: its `get` and `take`
//!   read the placeholder, its store fills the reference, as before. A
//!   program reaches them while its `modify` holds the reference only
//!   through code that runs inside modify's pure function: unsafe code, or
//!   the `sync` dependent of a promise whose last reference the function
//!   drops (it runs there and then, on this thread). Natively such a
//!   dependent's `get` waits for modify's store, which never comes: the
//!   program hangs; here it reads the placeholder and goes on (review
//!   RS4-01; a known difference, plan §10).
//!
//! The cost, as in Lean 4.35: a `modify` whose function waits for a task
//! that uses the same reference deadlocks. Without a taken reference, a
//! `get` costs `ref_read`'s load and countdown and one load here, a `set`
//! `before_publish`'s load and one load here; a `take` records the
//! reference (a call and a push), and modify's `set` then takes the slow
//! path (a search and a removal).

use lean_runtime::sched::{self as ls, CtxId};
use std::cell::UnsafeCell;

/// A reference `take` emptied: the address of its record, the thread that
/// took it, the contexts waiting for that thread's store.
struct Taken {
    addr: usize,
    owner: (CtxId, u64),
    waiters: Vec<CtxId>,
}

struct TakenRefs(UnsafeCell<Vec<Taken>>);
unsafe impl Sync for TakenRefs {}

/// The references taken now (usually none or one: a `modify` in progress
/// whose function blocked).
static TAKEN: TakenRefs = TakenRefs(UnsafeCell::new(Vec::new()));

#[inline]
fn any_taken() -> bool {
    unsafe { !(*TAKEN.0.get()).is_empty() }
}

/// The running thread (see the module comment): `main`'s before
/// lean-runtime's scheduler starts, without building the scheduler's state
/// for it (review RS4-02).
fn me() -> (CtxId, u64) {
    if !crate::task::sched_started() {
        return (ls::MAIN, 0);
    }
    (ls::current_context(), ls::thread_number())
}

/// Before `get`: a polling point; whether some reference is taken (then
/// the caller calls `wait`).
#[inline]
pub fn read_point() -> bool {
    ls::ref_read();
    any_taken()
}

/// Before `set`: a publication; whether some reference is taken.
#[inline]
pub fn write_point() -> bool {
    ls::before_publish();
    any_taken()
}

/// Before `swap`: both.
#[inline]
pub fn swap_point() -> bool {
    ls::before_publish();
    ls::ref_read();
    any_taken()
}

/// Before an operation on the reference whose record is at `addr`, while
/// some reference is taken: if another thread took this one, wait for its
/// store. A store (`store`: `set`, `swap`) of the thread that took it is
/// that store: the reference is no longer taken, and its waiters wake.
/// (`extern "C"`: it cannot unwind, so its callers need no landing pad.)
#[inline(never)]
pub extern "C" fn wait(addr: usize, store: bool) {
    let me = me();
    loop {
        // No borrow of `TAKEN` across `block_sync`: other contexts run there.
        let woken = {
            let t = unsafe { &mut *TAKEN.0.get() };
            let Some(k) = t.iter().position(|e| e.addr == addr) else {
                return;
            };
            if t[k].owner == me {
                if !store {
                    return;
                }
                Some(t.remove(k).waiters)
            } else {
                t[k].waiters.push(me.0);
                None
            }
        };
        match woken {
            Some(ws) => {
                for c in ws {
                    ls::wake(c);
                }
                return;
            }
            None => ls::block_sync(),
        }
    }
}

/// `take` of the reference whose record is at `addr` (before the cell
/// operation): a publication and a polling point; if another thread took
/// it, wait for its store; then it is taken by the running thread (already
/// by itself: a nested `take`, which reads the placeholder).
#[inline(never)]
pub extern "C" fn take(addr: usize) {
    ls::before_publish();
    ls::ref_read();
    let me = me();
    loop {
        {
            let t = unsafe { &mut *TAKEN.0.get() };
            match t.iter().position(|e| e.addr == addr) {
                None => {
                    t.push(Taken { addr, owner: me, waiters: Vec::new() });
                    return;
                }
                Some(k) if t[k].owner == me => return,
                Some(k) => t[k].waiters.push(me.0),
            }
        }
        ls::block_sync();
    }
}
