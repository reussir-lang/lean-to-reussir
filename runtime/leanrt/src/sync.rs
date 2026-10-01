//! `Std.Sync`'s primitives (`src/runtime/mutex.cpp`): `BaseMutex`
//! (`std::mutex`), `Condvar` (`std::condition_variable`),
//! `BaseRecursiveMutex` (`std::recursive_mutex`) and `BaseSharedMutex`
//! (libc++'s `std::shared_mutex`), over the scheduler's contexts (`sched`).
//!
//! A context that must wait (the mutex is held by another thread, a
//! condition variable before it is notified) blocks, and other contexts and
//! queued tasks run meanwhile, as other threads would. The owner of a lock
//! is a thread: a context, and on it the thread of the innermost running
//! task (a task needed by another runs on a worker thread natively, so it
//! is another thread than its caller; a `sync` dependent runs on its
//! source's). As natively (glibc), locking a `BaseMutex` that the same
//! thread holds waits forever, and unlocking one that is not locked by the
//! caller just unlocks it. A released mutex is handed to the thread that has
//! waited longest.
//!
//! The objects are runtime handles (`LHandle`, `lcAny` in mono code), freed
//! with their last reference.

use crate::fs::LHandle;
use crate::sched::{self, CtxId, Wait};
use std::cell::UnsafeCell;
use std::collections::VecDeque;

/// The thread that runs now (see the module comment). Module
/// initializers run on the process's main thread, `main` on another.
fn me() -> u64 {
    ((sched::cur() as u64) << 32)
        | crate::task::thread_now() as u64
        | if crate::task::deferring() { 1 << 63 } else { 0 }
}

fn new_handle<T: 'static>(v: T) -> LHandle {
    reussir_rt::rc::Rc::new(Box::new(v) as Box<dyn std::any::Any>)
}

fn get<T: 'static>(h: &LHandle) -> (&'static mut T, usize) {
    let c = h.downcast_ref::<UnsafeCell<T>>().expect("leanrt: not a synchronization object");
    // The object lives as long as the handle, which the caller holds
    // across the operation.
    (unsafe { &mut *c.get() }, c as *const UnsafeCell<T> as usize)
}

/// Block the running context on synchronization object `addr`.
fn wait_on(addr: usize) {
    sched::block(Wait::Sync(addr));
}

// ---------------------------------------------------------------------------
// BaseMutex

#[derive(Default)]
struct Mutex {
    owner: Option<u64>,
    waiters: VecDeque<(CtxId, u64)>,
}

pub fn mutex_new() -> LHandle {
    new_handle(UnsafeCell::new(Mutex::default()))
}

fn lock_core(m: &mut Mutex, addr: usize, who: u64) {
    if m.owner.is_none() {
        m.owner = Some(who);
        return;
    }
    // Held, by another thread or (a deadlock, as natively) by this one.
    m.waiters.push_back((sched::cur(), who));
    wait_on(addr);
    // `unlock_core` handed it over.
}

fn unlock_core(m: &mut Mutex) {
    match m.waiters.pop_front() {
        Some((c, who)) => {
            m.owner = Some(who);
            sched::wake(c);
        }
        None => m.owner = None,
    }
}

pub fn mutex_lock(h: &LHandle) {
    let (m, a) = get::<Mutex>(h);
    lock_core(m, a, me());
}

pub fn mutex_try_lock(h: &LHandle) -> bool {
    let (m, _) = get::<Mutex>(h);
    if m.owner.is_none() {
        m.owner = Some(me());
        true
    } else {
        false
    }
}

pub fn mutex_unlock(h: &LHandle) {
    let (m, _) = get::<Mutex>(h);
    unlock_core(m);
}

// ---------------------------------------------------------------------------
// Condvar

#[derive(Default)]
struct Condvar {
    waiters: VecDeque<CtxId>,
}

pub fn condvar_new() -> LHandle {
    new_handle(UnsafeCell::new(Condvar::default()))
}

/// `wait`: release the mutex, wait to be notified, then take the mutex
/// again (natively `condition_variable::wait` on the adopted lock).
pub fn condvar_wait(cv: &LHandle, mh: &LHandle) {
    let who = me();
    let (c, ca) = get::<Condvar>(cv);
    let (m, ma) = get::<Mutex>(mh);
    unlock_core(m);
    c.waiters.push_back(sched::cur());
    wait_on(ca);
    lock_core(m, ma, who);
}

pub fn condvar_notify_one(cv: &LHandle) {
    let (c, _) = get::<Condvar>(cv);
    if let Some(w) = c.waiters.pop_front() {
        sched::wake(w);
    }
}

pub fn condvar_notify_all(cv: &LHandle) {
    let (c, _) = get::<Condvar>(cv);
    for w in std::mem::take(&mut c.waiters) {
        sched::wake(w);
    }
}

// ---------------------------------------------------------------------------
// BaseRecursiveMutex

#[derive(Default)]
struct RecMutex {
    owner: Option<u64>,
    count: u32,
    waiters: VecDeque<(CtxId, u64)>,
}

pub fn recmutex_new() -> LHandle {
    new_handle(UnsafeCell::new(RecMutex::default()))
}

pub fn recmutex_lock(h: &LHandle) {
    let who = me();
    let (m, a) = get::<RecMutex>(h);
    match m.owner {
        None => {
            m.owner = Some(who);
            m.count = 1;
        }
        Some(o) if o == who => m.count += 1,
        Some(_) => {
            m.waiters.push_back((sched::cur(), who));
            wait_on(a);
        }
    }
}

pub fn recmutex_try_lock(h: &LHandle) -> bool {
    let who = me();
    let (m, _) = get::<RecMutex>(h);
    match m.owner {
        None => {
            m.owner = Some(who);
            m.count = 1;
            true
        }
        Some(o) if o == who => {
            m.count += 1;
            true
        }
        Some(_) => false,
    }
}

pub fn recmutex_unlock(h: &LHandle) {
    let (m, _) = get::<RecMutex>(h);
    if m.count > 1 {
        m.count -= 1;
        return;
    }
    match m.waiters.pop_front() {
        Some((c, who)) => {
            m.owner = Some(who);
            m.count = 1;
            sched::wake(c);
        }
        None => {
            m.owner = None;
            m.count = 0;
        }
    }
}

// ---------------------------------------------------------------------------
// BaseSharedMutex: libc++'s `__shared_mutex_base` (Lean's runtime is built
// with libc++): a writer that has entered (`write_entered`) keeps new
// readers out and waits for the readers inside to leave.

#[derive(Default)]
struct SharedMutex {
    write_entered: bool,
    readers: u32,
    /// Waiting to enter (writers and readers): libc++'s `gate1_`.
    gate1: VecDeque<CtxId>,
    /// The writer that has entered, waiting for the readers to leave:
    /// `gate2_`.
    gate2: Option<CtxId>,
}

pub fn sharedmutex_new() -> LHandle {
    new_handle(UnsafeCell::new(SharedMutex::default()))
}

/// Wait on `gate1` (its address: the object's; `gate2`'s is one more).
fn gate1_wait(m: &mut SharedMutex, a: usize) {
    m.gate1.push_back(sched::cur());
    wait_on(a);
}

fn gate1_notify_all(m: &mut SharedMutex) {
    for w in std::mem::take(&mut m.gate1) {
        sched::wake(w);
    }
}

fn gate1_notify_one(m: &mut SharedMutex) {
    if let Some(w) = m.gate1.pop_front() {
        sched::wake(w);
    }
}

pub fn sharedmutex_write(h: &LHandle) {
    let (m, a) = get::<SharedMutex>(h);
    while m.write_entered {
        gate1_wait(m, a);
    }
    m.write_entered = true;
    while m.readers > 0 {
        m.gate2 = Some(sched::cur());
        wait_on(a + 1);
    }
}

pub fn sharedmutex_try_write(h: &LHandle) -> bool {
    let (m, _) = get::<SharedMutex>(h);
    if !m.write_entered && m.readers == 0 {
        m.write_entered = true;
        true
    } else {
        false
    }
}

pub fn sharedmutex_unlock_write(h: &LHandle) {
    let (m, _) = get::<SharedMutex>(h);
    m.write_entered = false;
    m.readers = 0;
    gate1_notify_all(m);
}

pub fn sharedmutex_read(h: &LHandle) {
    let (m, a) = get::<SharedMutex>(h);
    while m.write_entered || m.readers == u32::MAX {
        gate1_wait(m, a);
    }
    m.readers += 1;
}

pub fn sharedmutex_try_read(h: &LHandle) -> bool {
    let (m, _) = get::<SharedMutex>(h);
    if !m.write_entered && m.readers != u32::MAX {
        m.readers += 1;
        true
    } else {
        false
    }
}

pub fn sharedmutex_unlock_read(h: &LHandle) {
    let (m, _) = get::<SharedMutex>(h);
    m.readers = m.readers.saturating_sub(1);
    if m.write_entered {
        if m.readers == 0 {
            if let Some(w) = m.gate2.take() {
                sched::wake(w);
            }
        }
    } else if m.readers == u32::MAX - 1 {
        gate1_notify_one(m);
    }
}
