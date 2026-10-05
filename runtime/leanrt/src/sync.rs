//! `Std.Sync`'s primitives over lean-runtime's (`lean_runtime::sched::sync`):
//! `BaseMutex`, `Condvar`, `BaseRecursiveMutex` and `BaseSharedMutex`. The
//! rules (owners are threads, glibc's and libc++'s behaviour, waits that let
//! the other contexts run) are lean-runtime's; each object lives in a runtime
//! handle (`LHandle`, `lcAny` in mono code), freed with its last reference.
//!
//! Each of lean-runtime's methods (the constructors included) first starts
//! the scheduler if `task::start`'s lazy start is waiting for it
//! (lean-runtime's `ensure_started`). A lock's owner is a thread, which
//! lean-runtime tells apart from an initializer's by its scheduler having
//! started (`sched::sync`'s owner): so every operation in `main` sees it
//! started, and an object an initializer made, locked by `main` before its
//! first task and again (nested) after it, has one owner (review RS4-05,
//! test `RtRecMutexLazyStart`).

use crate::fs::LHandle;
use lean_runtime::sched::sync::{Condvar, Mutex, RecursiveMutex, SharedMutex};

fn new_handle<T: 'static>(v: T) -> LHandle {
    reussir_rt::rc::Rc::new(Box::new(v) as Box<dyn std::any::Any>)
}

/// The object in `h` (the caller holds the handle across the operation).
fn get<T: 'static>(h: &LHandle) -> &T {
    h.downcast_ref::<T>().expect("leanrt: not a synchronization object")
}

pub fn mutex_new() -> LHandle {
    new_handle(Mutex::new())
}

pub fn mutex_lock(h: &LHandle) {
    get::<Mutex>(h).lock()
}

pub fn mutex_try_lock(h: &LHandle) -> bool {
    get::<Mutex>(h).try_lock()
}

pub fn mutex_unlock(h: &LHandle) {
    get::<Mutex>(h).unlock()
}

pub fn condvar_new() -> LHandle {
    new_handle(Condvar::new())
}

pub fn condvar_wait(cv: &LHandle, m: &LHandle) {
    get::<Condvar>(cv).wait(get::<Mutex>(m))
}

pub fn condvar_notify_one(cv: &LHandle) {
    get::<Condvar>(cv).notify_one()
}

pub fn condvar_notify_all(cv: &LHandle) {
    get::<Condvar>(cv).notify_all()
}

pub fn recmutex_new() -> LHandle {
    new_handle(RecursiveMutex::new())
}

pub fn recmutex_lock(h: &LHandle) {
    get::<RecursiveMutex>(h).lock()
}

pub fn recmutex_try_lock(h: &LHandle) -> bool {
    get::<RecursiveMutex>(h).try_lock()
}

pub fn recmutex_unlock(h: &LHandle) {
    get::<RecursiveMutex>(h).unlock()
}

pub fn sharedmutex_new() -> LHandle {
    new_handle(SharedMutex::new())
}

pub fn sharedmutex_write(h: &LHandle) {
    get::<SharedMutex>(h).write()
}

pub fn sharedmutex_try_write(h: &LHandle) -> bool {
    get::<SharedMutex>(h).try_write()
}

pub fn sharedmutex_unlock_write(h: &LHandle) {
    get::<SharedMutex>(h).unlock_write()
}

pub fn sharedmutex_read(h: &LHandle) {
    get::<SharedMutex>(h).read()
}

pub fn sharedmutex_try_read(h: &LHandle) -> bool {
    get::<SharedMutex>(h).try_read()
}

pub fn sharedmutex_unlock_read(h: &LHandle) {
    get::<SharedMutex>(h).unlock_read()
}
