//! Glue for `Std.Internal.UV.System` (`src/runtime/uv/system.cpp`, natively
//! over libuv 1.48) over lean-runtime's `io::uvsys`: the primitives of
//! lean2rr's shim (`lean2rr/L2RShim.lean`), on plain values. Results come as
//! an operation (`net::OpSt`): strings in `strs`, numbers as little-endian
//! 64-bit words in `bytes`, `code` 1 for a query's `none` (no such group, an
//! unset variable), and a failure as its start's error (`start_err`).
//!
//! The errors are lean-runtime's: `lean_decode_uv_error(code, fname)`
//! (`IoError::decode_uv_error`, with `chdir`'s path and `osGetGroup`'s
//! `"group"`), `mk_embedded_nul_error` for a string holding a NUL byte
//! (`IoError::embedded_nul`). The shim builds the `IO.Error` from the one
//! kept in the operation, as for the sockets (`L2RShim.checkStart`).

use crate::fs::LHandle;
use crate::net::{op, op_new, started};
use lean_runtime::io::uvsys;
use lean_runtime::io::IoError;

fn push_u64(v: &mut Vec<u8>, x: u64) {
    v.extend_from_slice(&x.to_le_bytes());
}

fn done_op() -> LHandle {
    let o = op_new();
    op(&o).done = true;
    o
}

/// An operation with one string: `f`'s bytes, or its error.
fn string_op(f: impl FnOnce(&mut Vec<u8>) -> Result<(), IoError>) -> LHandle {
    let o = done_op();
    let x = op(&o);
    let mut v = Vec::new();
    match f(&mut v) {
        Ok(()) => x.strs.push(v),
        Err(e) => x.start_err = Some(e),
    }
    o
}

/// `getProcessTitle` (`uv_get_process_title`).
pub fn title_get() -> LHandle {
    string_op(|s| uvsys::get_process_title(s))
}

/// `setProcessTitle` (`uv_set_process_title`). With lean-runtime's feature
/// `proc-title` (lean2rr enables it), the title is written into the
/// arguments' memory, as libuv does.
pub fn title_set(s: &[u8]) -> LHandle {
    started(uvsys::set_process_title(s))
}

/// `uptime` (`uv_uptime`): seconds.
pub fn uptime() -> LHandle {
    let o = done_op();
    let x = op(&o);
    match uvsys::uptime() {
        Ok(v) => push_u64(&mut x.bytes, v),
        Err(e) => x.start_err = Some(e),
    }
    o
}

/// `osGetPid` / `osGetPpid`.
pub fn pid(parent: bool) -> u64 {
    if parent { uvsys::os_getppid() } else { uvsys::os_getpid() }
}

/// `hrtime` (`uv_hrtime`).
pub fn hrtime() -> u64 {
    uvsys::hrtime()
}

/// `cwd` (`uv_cwd`).
pub fn cwd() -> LHandle {
    string_op(|s| uvsys::cwd(s))
}

/// `chdir` (`uv_chdir`; lean-runtime's error names the path).
pub fn chdir_to(p: &[u8]) -> LHandle {
    started(uvsys::chdir(p))
}

/// `osHomedir` (`uv_os_homedir`).
pub fn homedir() -> LHandle {
    string_op(|s| uvsys::os_homedir(s))
}

/// `osTmpdir` (`uv_os_tmpdir`).
pub fn tmpdir() -> LHandle {
    string_op(|s| uvsys::os_tmpdir(s))
}

/// `osGetPasswd` (`uv_os_get_passwd`): strings username, shell, homedir;
/// words uid, gid (lean-runtime gives them all on Linux).
pub fn passwd() -> LHandle {
    let o = done_op();
    let x = op(&o);
    match uvsys::os_get_passwd() {
        Ok(p) => {
            x.strs = vec![p.username, p.shell.unwrap_or_default(), p.homedir.unwrap_or_default()];
            push_u64(&mut x.bytes, p.uid.unwrap_or(0));
            push_u64(&mut x.bytes, p.gid.unwrap_or(0));
        }
        Err(e) => x.start_err = Some(e),
    }
    o
}

/// `osGetGroup gid` (`uv_os_get_group`): strings the name then the
/// members, word the gid; code 1 when there is no such group (the shim's
/// `none`); an error names `group` (lean-runtime's).
pub fn group(gid: u64) -> LHandle {
    let o = done_op();
    let x = op(&o);
    match uvsys::os_get_group(gid) {
        Ok(Some(g)) => {
            x.strs.push(g.groupname);
            x.strs.extend(g.members);
            push_u64(&mut x.bytes, g.gid);
        }
        Ok(None) => x.code = 1,
        Err(e) => x.start_err = Some(e),
    }
    o
}

/// `osEnviron` (`uv_os_environ`): names and values, alternating.
pub fn environ_all() -> LHandle {
    let o = done_op();
    let x = op(&o);
    uvsys::os_environ(|n, v| {
        x.strs.push(n.to_vec());
        x.strs.push(v.to_vec());
    });
    o
}

/// `osGetenv` (`uv_os_getenv`): the value (code 1 when unset, or when the
/// name holds a NUL byte: lean-runtime's `os_getenv`).
pub fn getenv(name: &[u8]) -> LHandle {
    let o = done_op();
    let x = op(&o);
    let mut v = Vec::new();
    if uvsys::os_getenv(name, &mut v) {
        x.strs.push(v);
    } else {
        x.code = 1;
    }
    o
}

/// `osSetenv`, `osUnsetenv`.
pub fn setenv_to(name: &[u8], value: Option<&[u8]>) -> LHandle {
    started(match value {
        Some(v) => uvsys::os_setenv(name, v),
        None => uvsys::os_unsetenv(name),
    })
}

/// `osGetHostname` (`uv_os_gethostname`).
pub fn hostname() -> LHandle {
    string_op(|s| uvsys::os_gethostname(s))
}

/// `osGetPriority` (`uv_os_getpriority`): the priority as a word (an `int`,
/// sign-extended).
pub fn get_priority(pid: u64) -> LHandle {
    let o = done_op();
    let x = op(&o);
    match uvsys::os_getpriority(pid) {
        Ok(p) => push_u64(&mut x.bytes, p as u64),
        Err(e) => x.start_err = Some(e),
    }
    o
}

/// `osSetPriority` (`uv_os_setpriority`; `prio` an `Int64`'s bits).
pub fn set_priority(pid: u64, prio: u64) -> LHandle {
    started(uvsys::os_setpriority(pid, prio as i64))
}

/// `osUname` (`uv_os_uname`): sysname, release, version, machine.
pub fn uname_all() -> LHandle {
    let o = done_op();
    let x = op(&o);
    match uvsys::os_uname() {
        Ok(u) => x.strs = vec![u.sysname, u.release, u.version, u.machine],
        Err(e) => x.start_err = Some(e),
    }
    o
}

/// `getrusage` (`uv_getrusage`): the times in milliseconds, then the
/// counters, in Lean's field order.
pub fn rusage() -> LHandle {
    let o = done_op();
    let x = op(&o);
    match uvsys::getrusage() {
        Ok(r) => {
            for w in [
                r.user_time,
                r.system_time,
                r.max_rss,
                r.ix_rss,
                r.id_rss,
                r.is_rss,
                r.min_flt,
                r.maj_flt,
                r.n_swap,
                r.in_block,
                r.out_block,
                r.msg_sent,
                r.msg_recv,
                r.signals,
                r.voluntary_cs,
                r.involuntary_cs,
            ] {
                push_u64(&mut x.bytes, w);
            }
        }
        Err(e) => x.start_err = Some(e),
    }
    o
}

/// `exePath` (`uv_exepath`).
pub fn exepath() -> LHandle {
    string_op(|s| uvsys::exepath(s))
}

/// `freeMemory` (0), `totalMemory` (1), `constrainedMemory` (2),
/// `availableMemory` (3).
pub fn memory(which: u8) -> u64 {
    match which {
        0 => uvsys::free_memory(),
        1 => uvsys::total_memory(),
        2 => uvsys::constrained_memory(),
        _ => uvsys::available_memory(),
    }
}

/// `cpuInfo` (`uv_cpu_info`): per processor its model (`strs`) and 6 words
/// (`bytes`): the speed in MHz, then the user, nice, sys, idle and irq times
/// in milliseconds.
pub fn cpu_info() -> LHandle {
    let o = done_op();
    let x = op(&o);
    match uvsys::cpu_info() {
        Ok(cpus) => {
            for c in cpus {
                x.strs.push(c.model);
                for w in [c.speed, c.times.user, c.times.nice, c.times.sys, c.times.idle, c.times.irq] {
                    push_u64(&mut x.bytes, w);
                }
            }
        }
        Err(e) => x.start_err = Some(e),
    }
    o
}

/// `random size` (`uv_random`), completing on lean-runtime's loop context
/// (`net::complete_on_loop`), as natively a libuv callback after its thread
/// pool's work. Lean allocates the array first; then
/// libuv refuses more than `0x7FFFFFFF` bytes at once (`UV_E2BIG`, the
/// start's error); the bytes are lean-runtime's `random_fill` (its error is
/// the completion's).
pub fn random(size: u64, r: crate::task::LPromise) -> LHandle {
    crate::array::check_alloc(size, 1);
    if let Err(e) = uvsys::random_check(size) {
        drop(r);
        return started(Err(e));
    }
    let o = op_new();
    let mut buf = vec![0u8; size as usize];
    let err = uvsys::random_fill(&mut buf).err();
    op(&o).bytes = buf;
    crate::net::complete_on_loop(&o, r, err);
    o
}

/// `Std.Time.Database.Windows.getNextTransition` off Windows: an operation
/// with lean-runtime's error (`io::time`).
pub fn windows_next_transition(id: &[u8], t: i64, default_time: bool) -> LHandle {
    started(Err(lean_runtime::io::time::windows_get_next_transition(id, t, default_time)))
}

/// `Std.Time.Database.Windows.getLocalTimeZoneIdentifierAt` off Windows:
/// an operation with lean-runtime's error (`io::time`).
pub fn windows_local_timezone_id_at(t: i64) -> LHandle {
    started(Err(lean_runtime::io::time::windows_local_timezone_id_at(t)))
}
