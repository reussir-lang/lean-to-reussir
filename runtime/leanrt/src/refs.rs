//! `ST.Ref` in a program that creates tasks: lean-runtime's keyed form of
//! its reference rule (its wait cores, core 3.2, `sched::ref_keyed`), which
//! is Lean 4.35's rule (lean-runtime's `docs/lean-bugs.md`, LB-01 and
//! LB-18).
//!
//! lean2rr decides at translation time whether a program creates tasks (an
//! extern that makes a task or a promise is reachable:
//! `programCreatesTasks`; every other context comes from those). Only then
//! do its reference operations call the points below, before the cell
//! operation itself (prelude `l2r_ref_*_point`, `l2r_ref_wait`,
//! `l2r_ref_take_mark`, with the reference's record address as the key). A
//! program without tasks has one context, so its reference operations stay
//! plain cell operations and call nothing here.
//!
//! - A read (`get`, `swap`, `take`) is a polling point (`ref_read`), a
//!   write (`set`, `swap`, `take`) a publication (`before_publish`); the
//!   points then answer whether some reference is taken, one thread-local
//!   load.
//! - `ST.Ref.modify` is `take`, then `set` (`ST.Prim.Ref.modifyUnsafe`).
//!   `take` empties the reference (its cell gets a placeholder) and records
//!   the running frame as its taker. Until the closing store, every other
//!   `get`, `take`, `set` and `swap` of it waits, the taker's own `get` and
//!   `take` included: natively the reference is multi-threaded there (a
//!   task's closure captured it) and its `get` spins until modify's store,
//!   which never comes, so the program hangs (review RS4-01, test
//!   `RtRefOwnGetDuringModify`).
//! - The closing store is found at run time (lean2rr's option B of the
//!   design): a `set` or `swap` in the frame that took the reference, which
//!   is modify's own store. A store from code nested inside modify's
//!   function (the `sync` dependent of a promise the function drops, a task
//!   run on the taker's stack) begins at a deeper frame, so it waits, as in
//!   Lean 4.35 (natively 4.34 stores into the empty slot and modify's store
//!   then overwrites it, LB-01). lean2rr never calls `ref_keyed::put`.
//!
//! The cost, as in Lean 4.35: a `modify` whose function waits for a task
//! that uses the same reference deadlocks.

use lean_runtime::sched::ref_keyed as rk;

pub use rk::{read_point, swap_point, write_point};

/// Before an operation on the reference whose record is at `addr`, while
/// some reference is taken (the point answered true): a `get` (`store`
/// false) waits while it is taken; a `set` or `swap` (`store` true) is the
/// closing store in the frame that took it, and waits otherwise.
#[inline]
pub fn wait(addr: usize, store: bool) {
    crate::drop::assert_not_in_free("a reference's wait");
    if store {
        rk::store(addr)
    } else {
        rk::wait(addr)
    }
}

/// `take` of the reference whose record is at `addr`, before the cell's
/// move: both points, a wait while it is taken (by anyone), then it is
/// taken by the running frame.
#[inline]
pub fn take(addr: usize) {
    crate::drop::assert_not_in_free("a reference's take");
    rk::take(addr)
}
