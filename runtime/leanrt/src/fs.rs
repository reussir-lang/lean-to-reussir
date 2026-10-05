//! Glue between lean2rr's values and lean-runtime's io (`lean_runtime::io`):
//! `IO.FS.Handle`s, the file system, temporary files, random bytes, and the
//! last-error slot through which lean2rr's generated code builds `IO.Error`s.
//!
//! The rules are lean-runtime's: glibc's `FILE` model (`io::cfile`) behind
//! every handle, the open-handle list and its exit sequence (`io::handle`,
//! `io::exit`), the file-system primitives (`io::fs`), `createTempFile` and
//! `createTempDir` (`io::temp`), `IO.getRandomBytes` (`io::env`) and the
//! decoding of `errno`s and libuv codes into `IO.Error` (`io::error`). This
//! module only converts: Lean strings to byte views and results to
//! lean2rr's `LStr`, `RVec` and `LHandle`, and it records each outcome.
//!
//! **Handles.** The Reussir-visible type is `Rc<Box<dyn Any>>` (spellable
//! with std and reussir_rt only); the box holds a [`FileHandle`], which holds
//! lean-runtime's `Handle` (`None`: a handle that is not open, the result of
//! a failed open or a child's stream that is not piped). The crate closes the
//! file (`fclose`) when the last clone of its `Handle` goes away, as Lean's
//! handle finalizer does; a handle released while a container is being freed
//! closes when the free reaches it, in Lean's order (`crate::drop`).
//!
//! **Errors.** Every fallible primitive records its outcome in a global
//! last-error slot: nothing, or lean-runtime's [`IoError`]. lean2rr's glue
//! checks [`ok`] after the call and otherwise builds the `IO.Error` from
//! [`error_kind`] (which `lean_mk_io_error_*` builder, numbered as in
//! runtime/README.md), [`errno`], [`error_fname`] and [`error_details`].
//!
//! **Sinks.** Results of unbounded size go into a `Vec<u8>`, infallible as
//! lean-runtime's contract asks (a failed allocation aborts, never exits:
//! `getLine` appends under the stream's lock), except a child's output,
//! which goes into a [`Sink`] that stops instead (`ByteSink::stopped`, see
//! "sinks" below).

use crate::string::{from_bytes, from_bytes_lossy, LStr};
use lean_runtime::io::{self as lio, ByteSink, FsMode, Handle, IoError};
use reussir_rt::rc::Rc;
use std::any::Any;
use std::cell::UnsafeCell;
use std::mem::MaybeUninit;

pub type LHandle = Rc<Box<dyn Any>>;

struct Global<T>(UnsafeCell<T>);
unsafe impl<T> Sync for Global<T> {}

// ---- the last-error slot ----

/// The outcome of the last fallible primitive: lean-runtime's `IoError`
/// taken apart into what lean2rr's glue reads. `failed` is read after every
/// IO primitive (`l2r_io_ok`, inline in the program), `errno` on every
/// error path (inline too), so both stay plain fields of the shape they had
/// before lean-runtime's io (the program's code is unchanged).
struct LastError {
    failed: bool,
    /// The error's code; `USER_ERROR` for a user error, which has none.
    errno: i32,
    /// The `lean_mk_io_error_*` builder (`kind_of`).
    kind: u8,
    fname: Option<Vec<u8>>,
    details: Option<Vec<u8>>,
}

/// The errno slot value of a user error (`io_result_mk_error(msg)`).
const USER_ERROR: i32 = -1;

static LAST: Global<LastError> =
    Global(UnsafeCell::new(LastError { failed: false, errno: 0, kind: 0, fname: None, details: None }));

#[inline(always)]
fn last() -> &'static mut LastError {
    unsafe { &mut *LAST.0.get() }
}

#[inline]
pub(crate) fn set_ok() {
    let l = last();
    l.failed = false;
    l.errno = 0;
    l.kind = 0;
    l.fname = None;
    l.details = None;
}

pub(crate) fn set_err(e: IoError) {
    use IoError::*;
    let l = last();
    l.failed = true;
    l.kind = kind_of(&e) as u8;
    l.errno = if matches!(e, UserError(_)) { USER_ERROR } else { error_code(&e) as i32 };
    let (fname, details) = error_parts(e);
    l.fname = fname.map(String::into_bytes);
    l.details = Some(details.into_bytes());
}

/// An error's file name (if its kind has one) and details.
fn error_parts(e: IoError) -> (Option<String>, String) {
    use IoError::*;
    match e {
        Interrupted(f, _, d) | NoFileOrDirectory(f, _, d) => (Some(f), d),
        AlreadyExists(f, _, d)
        | InvalidArgument(f, _, d)
        | PermissionDenied(f, _, d)
        | ResourceExhausted(f, _, d)
        | InappropriateType(f, _, d)
        | NoSuchThing(f, _, d) => (f, d),
        OtherError(_, d)
        | ResourceBusy(_, d)
        | ResourceVanished(_, d)
        | UnsupportedOperation(_, d)
        | HardwareFault(_, d)
        | UnsatisfiedConstraints(_, d)
        | IllegalOperation(_, d)
        | ProtocolError(_, d)
        | TimeExpired(_, d)
        | UserError(d) => (None, d),
        UnexpectedEof => (None, String::new()),
    }
}

/// An error's file name (empty where it has none) and details, as bytes
/// (for lean2rr's shim, which builds the `IO.Error` itself: `net`).
pub(crate) fn error_texts(e: IoError) -> (Vec<u8>, Vec<u8>) {
    let (f, d) = error_parts(e);
    (f.unwrap_or_default().into_bytes(), d.into_bytes())
}

/// Records `r`'s outcome; its value on success.
#[inline]
pub(crate) fn record<T>(r: Result<T, IoError>) -> Option<T> {
    match r {
        Ok(v) => {
            set_ok();
            Some(v)
        }
        Err(e) => {
            set_err(e);
            None
        }
    }
}

pub fn ok() -> bool {
    !last().failed
}

/// The last error's code (`osCode`); 0 for a user error, which has none.
pub fn errno() -> u32 {
    let l = last();
    if l.errno == USER_ERROR {
        0
    } else {
        l.errno as u32
    }
}

/// The last error's file name (`""` when it has none).
pub fn error_fname() -> LStr {
    from_bytes(last().fname.as_deref().unwrap_or(b""))
}

/// The last error's details (libuv's message, or Lean's own), or a user
/// error's message.
pub fn error_details() -> LStr {
    from_bytes(last().details.as_deref().unwrap_or(b""))
}

/// Which `lean_mk_io_error_*` builder makes the last error (lean2rr's
/// `ioErrorBuilderSyms`, runtime/README.md). Out of line, as before
/// lean-runtime's io (when it computed the kind): the error paths of the
/// program's IO calls keep their code.
#[inline(never)]
pub fn error_kind() -> u32 {
    last().kind as u32
}

/// The code an `IO.Error` holds (0 when its constructor has none).
pub(crate) fn error_code(e: &IoError) -> u32 {
    use IoError::*;
    match e {
        AlreadyExists(_, c, _)
        | Interrupted(_, c, _)
        | NoFileOrDirectory(_, c, _)
        | InvalidArgument(_, c, _)
        | PermissionDenied(_, c, _)
        | ResourceExhausted(_, c, _)
        | InappropriateType(_, c, _)
        | NoSuchThing(_, c, _)
        | OtherError(c, _)
        | ResourceBusy(c, _)
        | ResourceVanished(c, _)
        | UnsupportedOperation(c, _)
        | HardwareFault(c, _)
        | UnsatisfiedConstraints(c, _)
        | IllegalOperation(c, _)
        | ProtocolError(c, _)
        | TimeExpired(c, _) => *c,
        UnexpectedEof | UserError(_) => 0,
    }
}

/// The builder of an `IO.Error`: its constructor, and for the constructors
/// with an optional file name whether it has one.
pub(crate) fn kind_of(e: &IoError) -> u32 {
    use IoError::*;
    let file = |f: &Option<String>, no: u32| if f.is_some() { no + 1 } else { no };
    match e {
        OtherError(..) => 0,
        Interrupted(..) => 1,
        InvalidArgument(f, ..) => file(f, 2),
        NoFileOrDirectory(..) => 4,
        PermissionDenied(f, ..) => file(f, 5),
        ResourceExhausted(f, ..) => file(f, 7),
        InappropriateType(f, ..) => file(f, 9),
        NoSuchThing(f, ..) => file(f, 11),
        AlreadyExists(f, ..) => file(f, 13),
        HardwareFault(..) => 15,
        UnsatisfiedConstraints(..) => 16,
        IllegalOperation(..) => 17,
        ResourceVanished(..) => 18,
        ProtocolError(..) => 19,
        TimeExpired(..) => 20,
        ResourceBusy(..) => 21,
        UnsupportedOperation(..) => 22,
        UserError(..) => 23,
        // No io primitive of lean-runtime reports it, and Lean's runtime has
        // no builder for it.
        UnexpectedEof => crate::internal_panic("an IO primitive reported unexpectedEof (runtime invariant)"),
    }
}

// ---- sinks ----

/// The sinks lean2rr gives lean-runtime for its results of unbounded size.
///
/// A line, a path, a name, an environment value go into a plain `Vec<u8>`
/// (lean-runtime's `ByteSink` for `Vec`), infallible as lean-runtime's
/// contract asks of `getLine`'s sink: an allocation that fails aborts the
/// process (Rust's `memory allocation of N bytes failed`, status 134),
/// where native Lean's `std::bad_alloc` aborts it too (134). It never
/// returns into lean-runtime and never exits, so the exit cannot wait for
/// the stream lock `getLine` holds while it appends (review RST3-02: a
/// fallible sink there made a line without end spin forever, since
/// lean-runtime's `get_line` reads on).
///
/// A child's output (`IO.Process.output`, which reads another process
/// without bound) goes into a [`Sink`]: it grows with `try_reserve` (the
/// growth of `extend_from_slice`), and when that fails it drops the bytes
/// and says it has stopped (`ByteSink::stopped`), so that lean-runtime stops
/// reading at once; [`Sink::finish`], called once the crate has returned,
/// then ends the process as Lean's failed allocation of the growing
/// `ByteArray` does (`INTERNAL PANIC: out of memory`, exit 1; AR-5).
#[derive(Default)]
pub(crate) struct Sink {
    v: Vec<u8>,
    stopped: bool,
}

impl ByteSink for Sink {
    #[inline]
    fn extend_from_slice(&mut self, bytes: &[u8]) {
        if self.stopped {
            return;
        }
        if self.v.try_reserve(bytes.len()).is_err() {
            self.stopped = true;
            self.v = Vec::new();
            return;
        }
        self.v.extend_from_slice(bytes)
    }

    fn stopped(&self) -> bool {
        self.stopped
    }
}

impl Sink {
    /// The bytes, or the end of the process if the sink stopped.
    pub(crate) fn finish(self) -> Vec<u8> {
        if self.stopped {
            out_of_memory()
        }
        self.v
    }
}

#[cold]
#[inline(never)]
pub(crate) fn out_of_memory() -> ! {
    crate::lean_internal_panic(lean_runtime::semantics::panic::InternalPanic::OutOfMemory)
}

/// A path-like result as a Lean string (`mk_string`: lossy), its outcome
/// recorded; the empty string on failure.
fn sink_string(r: Result<(), IoError>, v: Vec<u8>) -> LStr {
    match record(r) {
        Some(()) => from_bytes_lossy(&v),
        None => from_bytes(b""),
    }
}

// ---- handles ----

/// A handle: lean-runtime's, or none (a handle that is not open).
pub struct FileHandle {
    h: Option<Handle>,
}

impl Drop for FileHandle {
    fn drop(&mut self) {
        if self.h.is_some() && crate::drop::active() {
            // Released while a container is freed: closed when the free
            // reaches it, in Lean's order (`crate::drop`).
            let moved = Box::new(self.h.take());
            crate::drop::defer(Box::into_raw(moved) as usize, close_deferred);
            return;
        }
        close(self.h.take());
    }
}

unsafe fn close_deferred(p: usize) -> bool {
    close(*Box::from_raw(p as *mut Option<Handle>));
    true
}

/// Drop a handle (the last clone closes its stream, `fclose`) in a
/// no-suspend scope of lean-runtime's scheduler (docs/sched.md, "The glue",
/// item 11): its flush never waits for a full pipe (the rest goes to a
/// writer thread), so no context is suspended inside a free or a drop.
fn close(h: Option<Handle>) {
    let _scope = lean_runtime::sched::no_suspend();
    drop(h);
}

#[inline(always)]
pub(crate) fn fh(h: &LHandle) -> &FileHandle {
    // Only this module creates handles, always holding a `FileHandle`.
    let b: &Box<dyn Any> = h;
    unsafe { &*(&**b as *const dyn Any as *const FileHandle) }
}

/// The open handle, or `EBADF` recorded (`fileno` of no file).
fn open_of(h: &LHandle) -> Option<&Handle> {
    let r = fh(h).h.as_ref();
    if r.is_none() {
        set_err(IoError::decode_io_error(lio::error::EBADF, None));
    }
    r
}

/// An `LHandle` over lean-runtime's handle (`None`: not open).
pub(crate) fn wrap(h: Option<Handle>) -> LHandle {
    Rc::new(Box::new(FileHandle { h }) as Box<dyn Any>)
}

/// `IO.FS.Handle.mk path mode` (`read`, `write`, `writeNew`, `readWrite`,
/// `append` = 0..4). On failure the result is a handle that is not open.
pub fn open_file(path: &[u8], mode: u8) -> LHandle {
    let mode = FsMode::from_index(mode).unwrap_or(FsMode::Append);
    wrap(record(Handle::open(path, mode)))
}

/// `Handle.putStr` / `Handle.write` (`fwrite`): output, an effect point.
pub fn put_str(h: &LHandle, s: &[u8]) {
    crate::sched::effect();
    if let Some(f) = open_of(h) {
        record(f.put_str(s));
    }
}

/// `Handle.flush` (`fflush`): output, an effect point.
pub fn flush(h: &LHandle) {
    crate::sched::effect();
    if let Some(f) = open_of(h) {
        record(f.flush());
    }
}

/// `lean_io_prim_handle_read` on `h`: a count whose byte array would
/// overflow is `ENOMEM`; the array allocation has Lean's checks; then
/// `fread` into the array's own block (Lean keeps the capacity asked for),
/// with no zero pass and no second copy. (The checks run before the stream
/// is locked: an out-of-memory panic exits, and the exit takes every
/// stream.)
pub(crate) fn lean_read(h: &Handle, n: u64) -> crate::array::RVec<u8> {
    let r = lio::handle::check_read_size(n as usize).and_then(|()| {
        crate::array::check_alloc(n, 1);
        crate::array::bytes_filled(n as usize, |p, room| {
            let out = unsafe { std::slice::from_raw_parts_mut(p as *mut MaybeUninit<u8>, room) };
            h.read_uninit(out)
        })
    });
    record(r).unwrap_or_else(crate::array::empty)
}

/// `Handle.read n`.
pub fn read_bytes(h: &LHandle, n: u64) -> crate::array::RVec<u8> {
    match open_of(h) {
        Some(f) => lean_read(f, n),
        None => crate::array::empty(),
    }
}

/// `Handle.isEof` (`feof`; cannot fail).
pub fn is_eof(h: &LHandle) -> bool {
    set_ok();
    fh(h).h.as_ref().is_some_and(Handle::is_eof)
}

/// `getLine` on `h` (`lean_io_prim_handle_get_line`): the line decoded as
/// `mk_string` does (lossily); the empty string on failure.
pub(crate) fn lean_get_line(h: &Handle) -> LStr {
    let mut s = Vec::new();
    let r = h.get_line(&mut s);
    sink_string(r, s)
}

/// `Handle.getLine`.
pub fn get_line(h: &LHandle) -> LStr {
    match open_of(h) {
        Some(f) => lean_get_line(f),
        None => from_bytes(b""),
    }
}

/// `Handle.isTty` (cannot fail; records success so a fallible-glue caller
/// sees no stale error).
pub fn is_tty(h: &LHandle) -> bool {
    set_ok();
    fh(h).h.as_ref().is_some_and(Handle::is_tty)
}

/// `Handle.rewind` (`fseek(fp, 0, SEEK_SET)`).
pub fn rewind(h: &LHandle) {
    if let Some(f) = open_of(h) {
        record(f.rewind());
    }
}

/// `Handle.truncate` (`ftruncate(fileno(fp), ftello(fp))`).
pub fn truncate(h: &LHandle) {
    if let Some(f) = open_of(h) {
        record(f.truncate());
    }
}

/// `Handle.lock` (`flock`).
pub fn lock(h: &LHandle, exclusive: bool) {
    if let Some(f) = open_of(h) {
        record(f.lock(exclusive));
    }
}

/// `Handle.tryLock`: `false` when the lock is held elsewhere.
pub fn try_lock(h: &LHandle, exclusive: bool) -> bool {
    match open_of(h) {
        Some(f) => record(f.try_lock(exclusive)).unwrap_or(false),
        None => false,
    }
}

/// `Handle.unlock`.
pub fn unlock(h: &LHandle) {
    if let Some(f) = open_of(h) {
        record(f.unlock());
    }
}

/// Handle operations taking their arguments by value, out of line. The
/// prelude's textures call these: an inlined texture that borrowed its
/// parameter (`&h`) left a stack slot whose address escapes in the calling
/// Lean function, and LLVM then kept that function's self tail calls as real
/// calls (an IO loop over `getLine` or `flush` ran out of stack).
pub mod owned {
    use super::*;
    use crate::drop::Vec as RVec;
    use crate::{array, rc_release};

    #[inline(never)]
    pub fn put_str(h: LHandle, s: LStr) { super::put_str(&h, crate::string::bytes(&s)); rc_release(s); rc_release(h); }
    #[inline(never)]
    pub fn write(h: LHandle, b: RVec<u8>) { super::put_str(&h, array::as_slice(&b)); array::release(b); rc_release(h); }
    #[inline(never)]
    pub fn flush(h: LHandle) { super::flush(&h); rc_release(h); }
    #[inline(never)]
    pub fn read(h: LHandle, n: u64) -> RVec<u8> { let v = read_bytes(&h, n); rc_release(h); v }
    #[inline(never)]
    pub fn get_line(h: LHandle) -> LStr { let s = super::get_line(&h); rc_release(h); s }
    #[inline(never)]
    pub fn is_tty(h: LHandle) -> bool { let r = super::is_tty(&h); rc_release(h); r }
    #[inline(never)]
    pub fn is_eof(h: LHandle) -> bool { let r = super::is_eof(&h); rc_release(h); r }
    #[inline(never)]
    pub fn rewind(h: LHandle) { super::rewind(&h); rc_release(h); }
    #[inline(never)]
    pub fn truncate(h: LHandle) { super::truncate(&h); rc_release(h); }
    #[inline(never)]
    pub fn lock(h: LHandle, exclusive: bool) { super::lock(&h, exclusive); rc_release(h); }
    #[inline(never)]
    pub fn try_lock(h: LHandle, exclusive: bool) -> bool { let r = super::try_lock(&h, exclusive); rc_release(h); r }
    #[inline(never)]
    pub fn unlock(h: LHandle) { super::unlock(&h); rc_release(h); }
}

// ---- the file system ----

/// `IO.FS.removeFile`.
pub fn remove_file(p: &[u8]) {
    record(lio::fs::remove_file(p));
}

/// `IO.FS.createDir`.
pub fn create_dir(p: &[u8]) {
    record(lio::fs::create_dir(p));
}

/// `IO.FS.removeDir`.
pub fn remove_dir(p: &[u8]) {
    record(lio::fs::remove_dir(p));
}

/// `IO.FS.rename`.
pub fn rename_file(from: &[u8], to: &[u8]) {
    record(lio::fs::rename(from, to));
}

/// `IO.FS.hardLink`.
pub fn hard_link(from: &[u8], to: &[u8]) {
    record(lio::fs::hard_link(from, to));
}

/// `IO.setAccessRights` (`lean_chmod`).
pub fn set_access_rights(p: &[u8], mode: u32) {
    record(lio::fs::set_access_rights(p, mode));
}

/// `IO.FS.realPath`.
pub fn real_path(p: &[u8]) -> LStr {
    let mut s = Vec::new();
    let r = lio::fs::real_path(p, &mut s);
    sink_string(r, s)
}

/// Entry names of a directory in `readdir` order, without `.` and `..`.
pub fn read_dir(p: &[u8]) -> Vec<LStr> {
    let mut names = Vec::new();
    let r = lio::fs::read_dir(p, |n| names.push(from_bytes_lossy(n)));
    match record(r) {
        Some(()) => names,
        None => Vec::new(),
    }
}

/// `System.FilePath.metadata` (`follow`) / `symlinkMetadata` fields:
/// accessed (sec as an i64 bit pattern, nsec), modified (sec, nsec), byte
/// size, file type (0 dir, 1 file, 2 symlink, 3 other), number of hard
/// links.
pub fn metadata(p: &[u8], follow: bool) -> [u64; 7] {
    let r = if follow { lio::fs::metadata(p) } else { lio::fs::symlink_metadata(p) };
    match record(r) {
        Some(m) => [
            m.accessed.sec as u64,
            m.accessed.nsec as u64,
            m.modified.sec as u64,
            m.modified.nsec as u64,
            m.byte_size,
            m.file_type as u64,
            m.num_links,
        ],
        None => [0; 7],
    }
}

/// `IO.currentDir` (a failure is Lean's user error).
pub fn current_dir() -> LStr {
    let mut s = Vec::new();
    let r = lio::fs::current_dir(&mut s);
    sink_string(r, s)
}

/// `IO.appPath` (a failure is Lean's user error).
pub fn app_path() -> LStr {
    let mut s = Vec::new();
    let r = lio::env::app_path(&mut s);
    sink_string(r, s)
}

/// `IO.Process.getCurrentDir`.
pub fn process_current_dir() -> LStr {
    let mut s = Vec::new();
    let r = lio::fs::process_current_dir(&mut s);
    sink_string(r, s)
}

/// `IO.Process.setCurrentDir`.
pub fn set_current_dir(p: &[u8]) {
    record(lio::fs::set_current_dir(p));
}

/// The path of the file the last `create_temp_file` created.
static TEMP_PATH: Global<Vec<u8>> = Global(UnsafeCell::new(Vec::new()));

/// `IO.FS.createTempFile`: the handle; its path is then `temp_file_path()`.
pub fn create_temp_file() -> LHandle {
    let mut s = Vec::new();
    let r = lio::temp::create_temp_file(&mut s);
    let path = s;
    let h = record(r);
    unsafe { *TEMP_PATH.0.get() = if h.is_some() { path } else { Vec::new() } };
    wrap(h)
}

/// (Lean's `mk_string`: a name that is not UTF-8 is decoded lossily.)
pub fn temp_file_path() -> LStr {
    from_bytes_lossy(unsafe { &*TEMP_PATH.0.get() })
}

/// `IO.FS.createTempDir`.
pub fn create_temp_dir() -> LStr {
    let mut s = Vec::new();
    let r = lio::temp::create_temp_dir(&mut s);
    sink_string(r, s)
}

/// A sink that keeps nothing (`IO.getEnv`'s test for a value).
struct Discard;

impl ByteSink for Discard {
    #[inline]
    fn extend_from_slice(&mut self, _: &[u8]) {}
}

/// `IO.getEnv name` (lean-runtime's `io::env::get_env`): whether `name` has
/// a value.
pub fn getenv_has(name: LStr) -> bool {
    lio::env::get_env(crate::string::bytes(&name), &mut Discard)
}

/// `IO.getEnv name`'s value (`mk_string`: lossy), `""` if it has none.
pub fn getenv_value(name: LStr) -> LStr {
    let mut s = Vec::new();
    lio::env::get_env(crate::string::bytes(&name), &mut s);
    from_bytes_lossy(&s)
}

/// `IO.getRandomBytes n` (`lean_io_get_random_bytes`): `/dev/urandom`
/// opened first, with Lean's checks (lean-runtime's `open_random`), then the
/// array allocated as Lean's and filled in its own block. No bytes need no
/// `/dev/urandom`.
pub fn get_random_bytes(n: u64) -> crate::array::RVec<u8> {
    if n == 0 {
        set_ok();
        return crate::array::empty();
    }
    let r = lio::env::open_random(n as usize).and_then(|src| {
        crate::array::check_alloc(n, 1);
        crate::array::bytes_filled(n as usize, |p, room| {
            let out = unsafe { std::slice::from_raw_parts_mut(p as *mut MaybeUninit<u8>, room) };
            src.fill_uninit(out).map(|()| room)
        })
    });
    record(r).unwrap_or_else(crate::array::empty)
}

#[cfg(test)]
#[path = "fs_tests.rs"]
mod tests;
