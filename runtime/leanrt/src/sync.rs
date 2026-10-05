//! `Std.Sync`'s primitives over lean-runtime's (`lean_runtime::sched::sync`):
//! `BaseMutex`, `Condvar`, `BaseRecursiveMutex` and `BaseSharedMutex`. The
//! rules (owners are threads, glibc's and libc++'s behaviour, waits that let
//! the other contexts run) are lean-runtime's; each object lives in a runtime
//! handle (`LHandle`, `lcAny` in mono code), freed with its last reference.

use crate::fs::LHandle;
use lean_runtime::sched::sync::{Condvar, Mutex, RecursiveMutex, SharedMutex};

fn new_handle<T: 'static>(v: T) -> LHandle {
    reussir_rt::rc::Rc::new(Box::new(v) as Box<dyn std::any::Any>)
}

/// The object in `h` (the caller holds the handle across the operation).
fn get<T: 'static>(h: &LHandle) -> &T {
    h.downcast_ref::<T>().expect("leanrt: not a synchronization object")
}

/// Before every operation on an object (each primitive below calls this,
/// or `ensure_started` for a constructor), lean-runtime's scheduler is
/// started once `main` runs (`task::ensure_started`; nothing during the
/// initializers). A lock's owner is a thread, which lean-runtime tells apart
/// from an initializer's by its scheduler having started (`sched::sync`'s
/// owner): without this, an object an initializer made, locked by `main`
/// before its first task and again (nested) after it, would see two
/// different owners, and `main` would wait for itself forever (review
/// RS4-05, test `RtRecMutexLazyStart`).
#[inline]
fn settle() {
    crate::task::ensure_started();
}

pub fn mutex_new() -> LHandle {
    crate::task::ensure_started();
    new_handle(Mutex::new())
}

pub fn mutex_lock(h: &LHandle) {
    settle();
    get::<Mutex>(h).lock()
}

pub fn mutex_try_lock(h: &LHandle) -> bool {
    settle();
    get::<Mutex>(h).try_lock()
}

pub fn mutex_unlock(h: &LHandle) {
    settle();
    get::<Mutex>(h).unlock()
}

pub fn condvar_new() -> LHandle {
    crate::task::ensure_started();
    new_handle(Condvar::new())
}

pub fn condvar_wait(cv: &LHandle, m: &LHandle) {
    settle();
    get::<Condvar>(cv).wait(get::<Mutex>(m))
}

pub fn condvar_notify_one(cv: &LHandle) {
    settle();
    get::<Condvar>(cv).notify_one()
}

pub fn condvar_notify_all(cv: &LHandle) {
    settle();
    get::<Condvar>(cv).notify_all()
}

pub fn recmutex_new() -> LHandle {
    crate::task::ensure_started();
    new_handle(RecursiveMutex::new())
}

pub fn recmutex_lock(h: &LHandle) {
    settle();
    get::<RecursiveMutex>(h).lock()
}

pub fn recmutex_try_lock(h: &LHandle) -> bool {
    settle();
    get::<RecursiveMutex>(h).try_lock()
}

pub fn recmutex_unlock(h: &LHandle) {
    settle();
    get::<RecursiveMutex>(h).unlock()
}

pub fn sharedmutex_new() -> LHandle {
    crate::task::ensure_started();
    new_handle(SharedMutex::new())
}

pub fn sharedmutex_write(h: &LHandle) {
    settle();
    get::<SharedMutex>(h).write()
}

pub fn sharedmutex_try_write(h: &LHandle) -> bool {
    settle();
    get::<SharedMutex>(h).try_write()
}

pub fn sharedmutex_unlock_write(h: &LHandle) {
    settle();
    get::<SharedMutex>(h).unlock_write()
}

pub fn sharedmutex_read(h: &LHandle) {
    settle();
    get::<SharedMutex>(h).read()
}

pub fn sharedmutex_try_read(h: &LHandle) -> bool {
    settle();
    get::<SharedMutex>(h).try_read()
}

pub fn sharedmutex_unlock_read(h: &LHandle) {
    settle();
    get::<SharedMutex>(h).unlock_read()
}
