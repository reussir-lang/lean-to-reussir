//! Glue for child processes (`IO.Process.spawn`, the `Child` operations,
//! `IO.Process.output`) over lean-runtime's `io::process`, which spawns as
//! Lean's `process.cpp` does (through `posix_spawn`, with the forked child's
//! steps reproduced: see that module).
//!
//! lean2rr's `Child` is a structure of its three stream fields (an `LHandle`
//! for a piped stream) and two hidden fields, the pid and the `setsid` flag
//! (lean2rr/LeanToReussir/Lower/Process.lean). lean-runtime's process object
//! (`ChildProcess`: the pid, the flag, and the state of a child it models
//! when no stand-in process can be started) is kept here by pid, for
//! `wait`, `tryWait` and `kill`, until the child is reaped; a pid with no
//! entry (a reaped child's) gets the system call itself, as natively.
//!
//! Errors are recorded in the last-error slot (`fs::record`).

use crate::fs::{record, wrap, LHandle, Sink};
use crate::string::{from_bytes, LStr};
use lean_runtime::io::process::{self as lproc, ChildProcess, SpawnArgs, Stdio, StdioConfig};
use lean_runtime::io::Handle;
use std::cell::UnsafeCell;
use std::collections::HashMap;

struct Global<T>(UnsafeCell<T>);
unsafe impl<T> Sync for Global<T> {}

/// The parent's ends of the last spawned child's piped streams.
static ENDS: Global<[Option<Handle>; 3]> = Global(UnsafeCell::new([None, None, None]));

/// The spawned children's process objects, by pid.
static CHILDREN: Global<Option<HashMap<u32, ChildProcess>>> = Global(UnsafeCell::new(None));

fn children() -> &'static mut HashMap<u32, ChildProcess> {
    unsafe { (*CHILDREN.0.get()).get_or_insert_with(HashMap::new) }
}

/// `IO.Process.Stdio` of a constructor index.
fn stdio(i: u32) -> Stdio {
    Stdio::from_index(i as u8).unwrap_or(Stdio::Null)
}

/// `IO.Process.spawn`: start `args` with the stdio modes (`modes` = stdin |
/// stdout << 8 | stderr << 16, `IO.Process.Stdio` indices). Returns the pid
/// (0 on failure, with the error recorded); the parent's pipe ends are then
/// `take_end(0..3)`.
pub fn spawn(args: &SpawnArgs, modes: u32) -> u32 {
    // A child is an effect: what other threads would have done by now
    // (their output) comes first (`sched::effect`).
    crate::sched::effect();
    let ends = unsafe { &mut *ENDS.0.get() };
    *ends = [None, None, None];
    let cfg = StdioConfig { stdin: stdio(modes & 0xff), stdout: stdio((modes >> 8) & 0xff), stderr: stdio((modes >> 16) & 0xff) };
    match record(lproc::spawn(cfg, args)) {
        Some(c) => {
            *ends = [c.stdin, c.stdout, c.stderr];
            let pid = c.process.pid();
            children().insert(pid, c.process);
            pid
        }
        None => 0,
    }
}

/// The parent's end of stream `i` (0 stdin, 1 stdout, 2 stderr) of the last
/// spawned child, or a handle that is not open when that stream was not
/// piped.
pub fn take_end(i: u64) -> LHandle {
    let ends = unsafe { &mut *ENDS.0.get() };
    wrap(ends.get_mut(i as usize).and_then(|e| e.take()))
}

/// The process object of a child spawned here and not yet reaped (a clone:
/// the pid, the flag and a shared modelled state).
fn child(pid: u32) -> Option<ChildProcess> {
    children().get(&pid).cloned()
}

/// The child has been reaped: its entry goes (review RST3-04). Natively the
/// pid then names no child of the program, and a later `wait`, `tryWait` or
/// `kill` of it is a plain system call on the pid (`os_wait`, `os_kill`).
fn reaped(pid: u32) {
    children().remove(&pid);
}

extern "C" {
    fn waitpid(pid: i32, status: *mut i32, options: i32) -> i32;
    fn kill(pid: i32, sig: i32) -> i32;
    fn killpg(pgrp: i32, sig: i32) -> i32;
    fn __errno_location() -> *mut i32;
}

/// `decode_io_error(errno, nullptr)` of the system call that just failed,
/// with lean-runtime's model of `errno` set as the call set C's.
fn os_error() -> lean_runtime::io::IoError {
    let e = unsafe { *__errno_location() };
    lean_runtime::io::error::set_errno(e);
    lean_runtime::io::IoError::decode_io_error(e, None)
}

/// `lean_io_process_child_wait`/`try_wait` of a pid that names no child this
/// runtime holds (one already reaped): `waitpid` itself, as natively (it
/// fails with `ECHILD`). The status as Lean reports it (128 + signal when
/// killed), `None` while running.
fn os_wait(pid: u32, nohang: bool) -> Result<Option<u32>, lean_runtime::io::IoError> {
    let mut st = 0i32;
    match unsafe { waitpid(pid as i32, &mut st, if nohang { 1 } else { 0 }) } {
        -1 => Err(os_error()),
        0 => Ok(None),
        _ => Ok(Some(if st & 0x7f == 0 { ((st >> 8) & 0xff) as u32 } else { 128 + (st & 0x7f) as u32 })),
    }
}

/// `Child.wait`: the exit code (`128 + signal` if killed).
pub fn wait(pid: u32) -> u32 {
    let r = match child(pid) {
        Some(c) => c.wait(),
        None => os_wait(pid, false).map(|s| s.unwrap_or(0)),
    };
    if r.is_ok() {
        reaped(pid);
    }
    record(r).unwrap_or(0)
}

/// `Child.tryWait`: `(1 << 32) | code` once the child has exited, 0 while it
/// runs.
pub fn try_wait(pid: u32) -> u64 {
    let r = match child(pid) {
        Some(c) => c.try_wait(),
        None => os_wait(pid, true),
    };
    if let Ok(Some(_)) = r {
        reaped(pid);
    }
    match record(r) {
        Some(Some(code)) => (1u64 << 32) | code as u64,
        _ => 0,
    }
}

/// `Child.kill`: `SIGKILL` to the child (to its process group if it was
/// spawned with `setsid`, which lean2rr's `Child` keeps through `takeStdin`,
/// as lean-runtime does: LB-14). A reaped child's pid is signalled as
/// natively, `kill`/`killpg` itself (`ESRCH` unless the pid was reused).
pub fn kill_child(pid: u32, new_session: bool) {
    match child(pid) {
        Some(c) => {
            record(c.kill());
        }
        None => {
            const SIGKILL: i32 = 9;
            let r = unsafe { if new_session { killpg(pid as i32, SIGKILL) } else { kill(pid as i32, SIGKILL) } };
            record(if r == -1 { Err(os_error()) } else { Ok(()) });
        }
    }
}

/// The standard output and standard error of the last `output`.
static OUTPUT: Global<(Vec<u8>, Vec<u8>)> = Global(UnsafeCell::new((Vec::new(), Vec::new())));

/// `IO.Process.output args input?` (lean-runtime's `io::process::output`):
/// the exit code, its two outputs then `take_output(1)` and `(2)` (valid
/// UTF-8); failures recorded. A sink that could not grow ends the process
/// once lean-runtime has returned (`INTERNAL PANIC: out of memory`; AR-5).
pub fn output(args: &SpawnArgs, input: Option<&[u8]>) -> u32 {
    crate::sched::effect();
    let (mut o, mut e) = (Sink::default(), Sink::default());
    let r = lproc::output(args, input, &mut o, &mut e);
    let (o, e) = (o.finish(), e.finish());
    let code = record(r);
    unsafe { *OUTPUT.0.get() = if code.is_some() { (o, e) } else { (Vec::new(), Vec::new()) } };
    code.unwrap_or(0)
}

/// The last `output`'s standard output (1) or standard error (2).
pub fn take_output(which: u64) -> LStr {
    let out = unsafe { &mut *OUTPUT.0.get() };
    from_bytes(&std::mem::take(if which == 1 { &mut out.0 } else { &mut out.1 }))
}

/// The arguments of a spawn as lean-runtime's views of lean2rr's values,
/// for `f`: the command, the arguments, the working directory (if
/// `has_cwd`), the environment changes as parallel arrays (names, values,
/// whether the value is `some`: set, else unset), `inheritEnv` and
/// `setsid`.
#[allow(clippy::too_many_arguments)]
pub fn with_args<R>(
    cmd: &LStr,
    args: &crate::array::RVec<LStr>,
    cwd: &LStr,
    has_cwd: bool,
    env_names: &crate::array::RVec<LStr>,
    env_values: &crate::array::RVec<LStr>,
    env_set: &crate::array::RVec<bool>,
    inherit_env: bool,
    setsid: bool,
    f: impl FnOnce(&SpawnArgs) -> R,
) -> R {
    use crate::string::Utf8;
    let argv: Vec<&[u8]> = crate::array::as_slice(args).iter().map(|a| a.utf8()).collect();
    let names = crate::array::as_slice(env_names);
    let values = crate::array::as_slice(env_values);
    let set = crate::array::as_slice(env_set);
    let env: Vec<(&[u8], Option<&[u8]>)> = (0..names.len())
        .map(|i| (names[i].utf8(), if set.get(i).copied().unwrap_or(false) { values.get(i).map(|v| v.utf8()) } else { None }))
        .collect();
    f(&SpawnArgs { cmd: cmd.utf8(), args: &argv, cwd: if has_cwd { Some(cwd.utf8()) } else { None }, env: &env, inherit_env, setsid })
}
