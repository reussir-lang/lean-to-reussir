//! Glue for `Std.Internal.UV.System` (`src/runtime/uv/system.cpp`, natively
//! over libuv 1.48) over lean-runtime's `io::uvsys`: the primitives of
//! lean2rr's shim (`lean2rr/L2RShim.lean`), on plain values. Results with
//! several parts come as an operation (`net::OpSt`): `code` a libuv error (or
//! 0), strings in `strs`, numbers as little-endian 64-bit words in `bytes`.
//!
//! lean-runtime reports a failure as `lean_decode_uv_error(code, fname)`
//! (`IoError::decode_uv_error`), which keeps `-code` as the error's code; the
//! shim builds the same `IO.Error` from `code` (`uvError`, and the file-name
//! variants of `chdir` and `osGetGroup`), so an error is passed on as
//! [`uv_code`]. The shim refuses strings holding NUL bytes itself, before
//! these primitives.

use crate::fs::{error_code, LHandle};
use crate::net::{op, op_new};
use lean_runtime::io::uvsys;
use lean_runtime::io::IoError;

/// The libuv code of a failure lean-runtime decoded with
/// `decode_uv_error(code, ...)`: `code` is the negated error code.
fn uv_code(e: &IoError) -> i32 {
    -(error_code(e) as i32)
}

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
        Err(e) => x.code = uv_code(&e),
    }
    o
}

/// `getProcessTitle` (`uv_get_process_title`).
pub fn title_get() -> LHandle {
    string_op(|s| uvsys::get_process_title(s))
}

/// `setProcessTitle` (`uv_set_process_title`): 0 or the libuv error. With
/// lean-runtime's feature `proc-title` (lean2rr enables it), the title is
/// written into the arguments' memory, as libuv does.
pub fn title_set(s: &[u8]) -> i32 {
    match uvsys::set_process_title(s) {
        Ok(()) => 0,
        Err(e) => uv_code(&e),
    }
}

/// `uptime` (`uv_uptime`): seconds.
pub fn uptime() -> LHandle {
    let o = done_op();
    let x = op(&o);
    match uvsys::uptime() {
        Ok(v) => push_u64(&mut x.bytes, v),
        Err(e) => x.code = uv_code(&e),
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

/// `chdir` (`uv_chdir`): 0 or the libuv error (the shim names the path).
pub fn chdir_to(p: &[u8]) -> i32 {
    match uvsys::chdir(p) {
        Ok(()) => 0,
        Err(e) => uv_code(&e),
    }
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
        Err(e) => x.code = uv_code(&e),
    }
    o
}

/// `osGetGroup gid` (`uv_os_get_group`): strings the name then the
/// members, word the gid; code `UV_ENOENT` (-2) when there is no such group
/// (the shim's `none`); another error is the one the shim names `group`.
pub fn group(gid: u64) -> LHandle {
    let o = done_op();
    let x = op(&o);
    match uvsys::os_get_group(gid) {
        Ok(Some(g)) => {
            x.strs.push(g.groupname);
            x.strs.extend(g.members);
            push_u64(&mut x.bytes, g.gid);
        }
        Ok(None) => x.code = -2,
        Err(e) => x.code = uv_code(&e),
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

/// `osGetenv` (`uv_os_getenv`): the value (code `UV_ENOENT` when unset).
pub fn getenv(name: &[u8]) -> LHandle {
    let o = done_op();
    let x = op(&o);
    let mut v = Vec::new();
    if uvsys::os_getenv(name, &mut v) {
        x.strs.push(v);
    } else {
        x.code = -2;
    }
    o
}

/// `osSetenv`, `osUnsetenv`: 0 or the libuv error.
pub fn setenv_to(name: &[u8], value: Option<&[u8]>) -> i32 {
    let r = match value {
        Some(v) => uvsys::os_setenv(name, v),
        None => uvsys::os_unsetenv(name),
    };
    match r {
        Ok(()) => 0,
        Err(e) => uv_code(&e),
    }
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
        Err(e) => x.code = uv_code(&e),
    }
    o
}

/// `osSetPriority` (`uv_os_setpriority`; `prio` an `Int64`'s bits): 0 or the
/// libuv error.
pub fn set_priority(pid: u64, prio: u64) -> i32 {
    match uvsys::os_setpriority(pid, prio as i64) {
        Ok(()) => 0,
        Err(e) => uv_code(&e),
    }
}

/// `osUname` (`uv_os_uname`): sysname, release, version, machine.
pub fn uname_all() -> LHandle {
    let o = done_op();
    let x = op(&o);
    match uvsys::os_uname() {
        Ok(u) => x.strs = vec![u.sysname, u.release, u.version, u.machine],
        Err(e) => x.code = uv_code(&e),
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
        Err(e) => x.code = uv_code(&e),
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
        Err(e) => x.code = uv_code(&e),
    }
    o
}

/// `random size` (`uv_random`), completing on lean-runtime's loop context
/// (`net::complete_on_loop`), as natively a libuv callback after its thread
/// pool's work. Lean allocates the array first; then
/// libuv refuses more than `0x7FFFFFFF` bytes at once (`UV_E2BIG`, a
/// `sync_err`); the bytes are lean-runtime's `random_fill`.
pub fn random(size: u64, r: crate::task::LPromise) -> LHandle {
    let o = op_new();
    crate::array::check_alloc(size, 1);
    if let Err(e) = uvsys::random_check(size) {
        op(&o).sync_err = uv_code(&e);
        drop(r);
        return o;
    }
    let mut buf = vec![0u8; size as usize];
    let code = match uvsys::random_fill(&mut buf) {
        Ok(()) => 0,
        Err(e) => uv_code(&e),
    };
    op(&o).bytes = buf;
    crate::net::complete_on_loop(&o, r, code);
    o
}
