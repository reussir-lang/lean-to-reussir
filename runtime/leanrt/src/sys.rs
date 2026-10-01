//! `Std.Internal.UV.System` (`src/runtime/uv/system.cpp`, natively over
//! libuv 1.48's `uv_get_process_title`, `uv_cpu_info`, `uv_os_*`, ...): the
//! primitives of lean2rr's shim (`lean2rr/L2RShim.lean`), on plain values.
//! Results with several parts come as an operation (`net::OpSt`): `code` a
//! libuv error (or 0), strings in `strs`, numbers as little-endian 64-bit
//! words in `bytes`. Each follows libuv's Unix (Linux) implementation.

use crate::fs::LHandle;
use crate::net::{op, op_new};
use std::ffi::{c_char, c_void, CStr};

extern "C" {
    fn getpid() -> i32;
    fn getppid() -> i32;
    fn getcwd(buf: *mut c_char, size: usize) -> *mut c_char;
    fn chdir(path: *const c_char) -> i32;
    fn geteuid() -> u32;
    fn getpwuid_r(uid: u32, pwd: *mut Passwd, buf: *mut c_char, len: usize, result: *mut *mut Passwd) -> i32;
    fn getgrgid_r(gid: u32, grp: *mut Group, buf: *mut c_char, len: usize, result: *mut *mut Group) -> i32;
    fn setenv(name: *const c_char, value: *const c_char, overwrite: i32) -> i32;
    fn unsetenv(name: *const c_char) -> i32;
    fn gethostname(name: *mut c_char, len: usize) -> i32;
    fn getpriority(which: i32, who: u32) -> i32;
    fn setpriority(which: i32, who: u32, prio: i32) -> i32;
    fn uname(buf: *mut UtsName) -> i32;
    fn clock_gettime(clk: i32, ts: *mut i64) -> i32;
    fn getrandom(buf: *mut c_void, len: usize, flags: u32) -> isize;
    fn getrusage(who: i32, usage: *mut [i64; 18]) -> i32;
    fn sysconf(name: i32) -> i64;
    static environ: *const *const c_char;
}

#[repr(C)]
struct Passwd {
    pw_name: *const c_char,
    pw_passwd: *const c_char,
    pw_uid: u32,
    pw_gid: u32,
    pw_gecos: *const c_char,
    pw_dir: *const c_char,
    pw_shell: *const c_char,
}

#[repr(C)]
struct Group {
    gr_name: *const c_char,
    gr_passwd: *const c_char,
    gr_gid: u32,
    gr_mem: *const *const c_char,
}

#[repr(C)]
struct UtsName {
    sysname: [c_char; 65],
    nodename: [c_char; 65],
    release: [c_char; 65],
    version: [c_char; 65],
    machine: [c_char; 65],
    domainname: [c_char; 65],
}

fn errno() -> i32 {
    crate::cfile::errno_now()
}

fn cstr(p: *const c_char) -> Vec<u8> {
    if p.is_null() {
        Vec::new()
    } else {
        unsafe { CStr::from_ptr(p) }.to_bytes().to_vec()
    }
}

fn cbuf(b: &[c_char]) -> Vec<u8> {
    unsafe { CStr::from_ptr(b.as_ptr()) }.to_bytes().to_vec()
}

fn zstr(s: &[u8]) -> Vec<u8> {
    let mut v = s.to_vec();
    v.push(0);
    v
}

fn push_u64(v: &mut Vec<u8>, x: u64) {
    v.extend_from_slice(&x.to_le_bytes());
}

fn done_op() -> LHandle {
    let o = op_new();
    op(&o).done = true;
    o
}

// ---- process title (`uv_setup_args`, `uv_get_process_title`,
// `uv_set_process_title`) ----

struct Title {
    title: Vec<u8>,
    cap: usize,
}

static TITLE: std::sync::Mutex<Option<Title>> = std::sync::Mutex::new(None);

fn with_title<R>(f: impl FnOnce(&mut Title) -> R) -> R {
    let mut g = TITLE.lock().unwrap();
    if g.is_none() {
        // The title is `argv[0]`; it can grow over the memory of all the
        // arguments (their lengths, with their NULs).
        let args: Vec<Vec<u8>> = std::env::args_os().map(|a| std::os::unix::ffi::OsStrExt::as_bytes(a.as_os_str()).to_vec()).collect();
        let title = args.first().cloned().unwrap_or_default();
        let cap = args.iter().map(|a| a.len() + 1).sum();
        *g = Some(Title { title, cap });
    }
    f(g.as_mut().unwrap())
}

/// `uv_get_process_title`.
pub fn title_get() -> Vec<u8> {
    with_title(|t| t.title.clone())
}

/// `uv_set_process_title`: truncated to the arguments' memory, and the
/// thread's name (`PR_SET_NAME`).
pub fn title_set(s: &[u8]) {
    with_title(|t| {
        let mut len = s.len();
        if len >= t.cap {
            len = t.cap.saturating_sub(1);
        }
        t.title = s[..len].to_vec();
        extern "C" {
            fn prctl(op: i32, arg: *const c_char, a3: u64, a4: u64, a5: u64) -> i32;
        }
        let z = zstr(&t.title);
        unsafe { prctl(15, z.as_ptr() as *const c_char, 0, 0, 0) };
    })
}

// ---- simple values ----

/// `uv_uptime`: seconds (from `/proc/uptime`), truncated.
pub fn uptime() -> LHandle {
    let o = done_op();
    let x = op(&o);
    match std::fs::read_to_string("/proc/uptime") {
        Ok(s) => {
            let v: f64 = s.split_whitespace().next().and_then(|w| w.parse().ok()).unwrap_or(0.0);
            push_u64(&mut x.bytes, v as u64);
        }
        Err(e) => x.code = -e.raw_os_error().unwrap_or(5),
    }
    o
}

pub fn pid(parent: bool) -> u64 {
    (unsafe { if parent { getppid() } else { getpid() } }) as u64
}

/// `uv_hrtime`: `CLOCK_MONOTONIC` in nanoseconds.
pub fn hrtime() -> u64 {
    let mut ts = [0i64; 2];
    unsafe { clock_gettime(1, ts.as_mut_ptr()) };
    (ts[0] as u64).wrapping_mul(1_000_000_000).wrapping_add(ts[1] as u64)
}

/// `uv_cwd` (a trailing slash dropped, except for `/`).
pub fn cwd() -> LHandle {
    let o = done_op();
    let x = op(&o);
    let mut buf = vec![0 as c_char; 4096];
    if unsafe { getcwd(buf.as_mut_ptr(), buf.len()) }.is_null() {
        x.code = -errno();
        return o;
    }
    let mut s = cbuf(&buf);
    if s.len() > 1 && s.last() == Some(&b'/') {
        s.pop();
    }
    x.strs.push(s);
    o
}

/// `uv_chdir`.
pub fn chdir_to(p: &[u8]) -> i32 {
    let z = zstr(p);
    if unsafe { chdir(z.as_ptr() as *const c_char) } != 0 {
        -errno()
    } else {
        0
    }
}

/// The passwd entry of the effective user (`uv__getpwuid_r`).
fn pw_entry() -> Result<(Vec<u8>, u32, u32, Vec<u8>, Vec<u8>), i32> {
    let mut pwd = std::mem::MaybeUninit::<Passwd>::zeroed();
    let mut res: *mut Passwd = std::ptr::null_mut();
    let mut len = 4096usize;
    loop {
        let mut buf = vec![0 as c_char; len];
        let r = unsafe { getpwuid_r(geteuid(), pwd.as_mut_ptr(), buf.as_mut_ptr(), len, &mut res) };
        if r == 34 {
            len *= 2;
            continue;
        }
        if r != 0 {
            return Err(-r);
        }
        if res.is_null() {
            return Err(-2);
        }
        let p = unsafe { pwd.assume_init_ref() };
        return Ok((cstr(p.pw_name), p.pw_uid, p.pw_gid, cstr(p.pw_shell), cstr(p.pw_dir)));
    }
}

/// `uv_os_homedir`: `HOME` if it is set and not empty, else the passwd
/// entry's directory.
pub fn homedir() -> LHandle {
    let o = done_op();
    let x = op(&o);
    if let Some(h) = std::env::var_os("HOME") {
        let b = std::os::unix::ffi::OsStrExt::as_bytes(h.as_os_str()).to_vec();
        if !b.is_empty() {
            x.strs.push(b);
            return o;
        }
    }
    match pw_entry() {
        Ok((_, _, _, _, dir)) => x.strs.push(dir),
        Err(e) => x.code = e,
    }
    o
}

/// `uv_os_tmpdir`: `TMPDIR`, `TMP`, `TEMP` or `TEMPDIR`, else `/tmp`, a
/// trailing slash dropped.
pub fn tmpdir() -> LHandle {
    let o = done_op();
    let x = op(&o);
    let mut d = b"/tmp".to_vec();
    for v in ["TMPDIR", "TMP", "TEMP", "TEMPDIR"] {
        if let Some(s) = std::env::var_os(v) {
            let b = std::os::unix::ffi::OsStrExt::as_bytes(s.as_os_str()).to_vec();
            if !b.is_empty() {
                d = b;
                break;
            }
        }
    }
    if d.len() > 1 && d.last() == Some(&b'/') {
        d.pop();
    }
    x.strs.push(d);
    o
}

/// `uv_os_get_passwd`: strings username, shell, homedir; words uid, gid.
pub fn passwd() -> LHandle {
    let o = done_op();
    let x = op(&o);
    match pw_entry() {
        Ok((name, uid, gid, shell, dir)) => {
            x.strs = vec![name, shell, dir];
            push_u64(&mut x.bytes, uid as u64);
            push_u64(&mut x.bytes, gid as u64);
        }
        Err(e) => x.code = e,
    }
    o
}

/// `uv_os_get_group`: strings the name then the members, word the gid;
/// code `UV_ENOENT` (-2) when there is no such group.
pub fn group(gid: u64) -> LHandle {
    let o = done_op();
    let x = op(&o);
    let mut grp = std::mem::MaybeUninit::<Group>::zeroed();
    let mut res: *mut Group = std::ptr::null_mut();
    let mut len = 4096usize;
    loop {
        let mut buf = vec![0 as c_char; len];
        let r = unsafe { getgrgid_r(gid as u32, grp.as_mut_ptr(), buf.as_mut_ptr(), len, &mut res) };
        if r == 34 {
            len *= 2;
            continue;
        }
        if r != 0 {
            x.code = -r;
            return o;
        }
        if res.is_null() {
            x.code = -2;
            return o;
        }
        let g = unsafe { grp.assume_init_ref() };
        x.strs.push(cstr(g.gr_name));
        let mut m = g.gr_mem;
        while !m.is_null() && !unsafe { *m }.is_null() {
            x.strs.push(cstr(unsafe { *m }));
            m = unsafe { m.add(1) };
        }
        push_u64(&mut x.bytes, g.gr_gid as u64);
        return o;
    }
}

/// `uv_os_environ`: names and values, alternating (an entry without `=` is
/// skipped, as libuv does).
pub fn environ_all() -> LHandle {
    let o = done_op();
    let x = op(&o);
    let mut p = unsafe { environ };
    while !p.is_null() && !unsafe { *p }.is_null() {
        let e = cstr(unsafe { *p });
        if let Some(i) = e.iter().position(|&c| c == b'=') {
            x.strs.push(e[..i].to_vec());
            x.strs.push(e[i + 1..].to_vec());
        }
        p = unsafe { p.add(1) };
    }
    o
}

/// `uv_os_getenv`: the value (code `UV_ENOENT` when unset).
pub fn getenv(name: &[u8]) -> LHandle {
    extern "C" {
        #[link_name = "getenv"]
        fn c_getenv(name: *const c_char) -> *const c_char;
    }
    let o = done_op();
    let x = op(&o);
    let z = zstr(name);
    let v = unsafe { c_getenv(z.as_ptr() as *const c_char) };
    if v.is_null() {
        x.code = -2;
    } else {
        x.strs.push(cstr(v));
    }
    o
}

/// `uv_os_setenv`, `uv_os_unsetenv`.
pub fn setenv_to(name: &[u8], value: Option<&[u8]>) -> i32 {
    let n = zstr(name);
    let r = match value {
        Some(v) => {
            let v = zstr(v);
            unsafe { setenv(n.as_ptr() as *const c_char, v.as_ptr() as *const c_char, 1) }
        }
        None => unsafe { unsetenv(n.as_ptr() as *const c_char) },
    };
    if r != 0 {
        -errno()
    } else {
        0
    }
}

/// `uv_os_gethostname`.
pub fn hostname() -> LHandle {
    let o = done_op();
    let x = op(&o);
    let mut buf = [0 as c_char; 257];
    if unsafe { gethostname(buf.as_mut_ptr(), 256) } != 0 {
        x.code = -errno();
    } else {
        x.strs.push(cbuf(&buf));
    }
    o
}

/// `uv_os_getpriority`: the priority as a word (an `int`, sign-extended).
pub fn get_priority(pid: u64) -> LHandle {
    let o = done_op();
    let x = op(&o);
    crate::cfile::set_errno(0);
    let r = unsafe { getpriority(0, pid as u32) };
    if r == -1 && errno() != 0 {
        x.code = -errno();
    } else {
        push_u64(&mut x.bytes, r as i64 as u64);
    }
    o
}

/// `uv_os_setpriority`.
pub fn set_priority(pid: u64, prio: u64) -> i32 {
    if unsafe { setpriority(0, pid as u32, prio as i64 as i32) } != 0 {
        -errno()
    } else {
        0
    }
}

/// `uv_os_uname`: sysname, release, version, machine.
pub fn uname_all() -> LHandle {
    let o = done_op();
    let x = op(&o);
    let mut u = std::mem::MaybeUninit::<UtsName>::zeroed();
    if unsafe { uname(u.as_mut_ptr()) } != 0 {
        x.code = -errno();
        return o;
    }
    let u = unsafe { u.assume_init_ref() };
    x.strs = vec![cbuf(&u.sysname), cbuf(&u.release), cbuf(&u.version), cbuf(&u.machine)];
    o
}

/// `uv_getrusage` (`RUSAGE_SELF`): the times in milliseconds, then the
/// counters.
pub fn rusage() -> LHandle {
    let o = done_op();
    let x = op(&o);
    let mut r = [0i64; 18];
    if unsafe { getrusage(0, &mut r) } != 0 {
        x.code = -errno();
        return o;
    }
    let ms = |s: i64, us: i64| (s as u64).wrapping_mul(1000).wrapping_add(us as u64 / 1000);
    push_u64(&mut x.bytes, ms(r[0], r[1]));
    push_u64(&mut x.bytes, ms(r[2], r[3]));
    for i in 4..18 {
        push_u64(&mut x.bytes, r[i] as u64);
    }
    o
}

/// `uv_exepath`: `/proc/self/exe`.
pub fn exepath() -> LHandle {
    let o = done_op();
    let x = op(&o);
    match std::fs::read_link("/proc/self/exe") {
        Ok(p) => x.strs.push(std::os::unix::ffi::OsStrExt::as_bytes(p.as_os_str()).to_vec()),
        Err(e) => x.code = -e.raw_os_error().unwrap_or(5),
    }
    o
}

/// A field of `/proc/meminfo`, in bytes.
fn meminfo(field: &str) -> Option<u64> {
    let s = std::fs::read_to_string("/proc/meminfo").ok()?;
    for l in s.lines() {
        if let Some(rest) = l.strip_prefix(field) {
            let kb: u64 = rest.trim().trim_end_matches("kB").trim().parse().ok()?;
            return Some(kb * 1024);
        }
    }
    None
}

/// The memory limit of the process's cgroup (v2 `memory.max`, or v1
/// `memory.limit_in_bytes`), 0 if none.
fn cgroup_limit() -> u64 {
    let cg = std::fs::read_to_string("/proc/self/cgroup").unwrap_or_default();
    for l in cg.lines() {
        if let Some(p) = l.strip_prefix("0::") {
            let f = format!("/sys/fs/cgroup{}/memory.max", p.trim());
            if let Ok(v) = std::fs::read_to_string(f) {
                return v.trim().parse().unwrap_or(0);
            }
        }
    }
    if let Ok(v) = std::fs::read_to_string("/sys/fs/cgroup/memory/memory.limit_in_bytes") {
        let n: u64 = v.trim().parse().unwrap_or(0);
        if n < (1u64 << 62) {
            return n;
        }
    }
    0
}

/// `uv_get_free_memory` (0), `uv_get_total_memory` (1),
/// `uv_get_constrained_memory` (2), `uv_get_available_memory` (3).
pub fn memory(which: u8) -> u64 {
    match which {
        0 => meminfo("MemAvailable:").unwrap_or(0),
        1 => meminfo("MemTotal:").unwrap_or(0),
        2 => cgroup_limit(),
        _ => {
            let free = meminfo("MemAvailable:").unwrap_or(0);
            let limit = cgroup_limit();
            if limit == 0 {
                free
            } else {
                limit.min(free)
            }
        }
    }
}

/// `uv_cpu_info`: per processor its model (`strs`) and 6 words (`bytes`):
/// the speed in MHz, then the user, nice, sys, idle and irq times in
/// milliseconds (`/proc/stat`, `/proc/cpuinfo`,
/// `/sys/devices/system/cpu/cpuN/cpufreq/scaling_cur_freq`).
pub fn cpu_info() -> LHandle {
    let o = done_op();
    let x = op(&o);
    let stat = match std::fs::read_to_string("/proc/stat") {
        Ok(s) => s,
        Err(e) => {
            x.code = -e.raw_os_error().unwrap_or(5);
            return o;
        }
    };
    let ticks = unsafe { sysconf(2) }.max(1) as u64; // _SC_CLK_TCK
    let mult = 1000 / ticks;
    let models: Vec<Vec<u8>> = std::fs::read_to_string("/proc/cpuinfo")
        .unwrap_or_default()
        .lines()
        .filter_map(|l| l.strip_prefix("model name\t: ").map(|m| m.as_bytes().to_vec()))
        .collect();
    let mut n = 0usize;
    for l in stat.lines() {
        let Some(rest) = l.strip_prefix("cpu") else { continue };
        let mut it = rest.split_whitespace();
        let Some(idx) = it.next() else { continue };
        let Ok(cpu) = idx.parse::<usize>() else { continue };
        let v: Vec<u64> = it.map(|w| w.parse().unwrap_or(0)).collect();
        let get = |i: usize| v.get(i).copied().unwrap_or(0) * mult;
        let speed = std::fs::read_to_string(format!("/sys/devices/system/cpu/cpu{}/cpufreq/scaling_cur_freq", cpu))
            .ok()
            .and_then(|s| s.trim().parse::<u64>().ok())
            .map(|k| k / 1000)
            .unwrap_or(0);
        x.strs.push(models.get(n).cloned().unwrap_or_else(|| b"unknown".to_vec()));
        push_u64(&mut x.bytes, speed);
        for i in [0, 1, 2, 3, 5] {
            push_u64(&mut x.bytes, get(i));
        }
        n += 1;
    }
    o
}

/// `uv_random` of `size` bytes (`getrandom`), completing through the event
/// loop as natively on libuv's thread pool.
pub fn random(size: u64, r: crate::task::LPromise) -> LHandle {
    let o = op_new();
    let mut buf = vec![0u8; size as usize];
    let mut off = 0;
    let mut code = 0;
    while off < buf.len() {
        let n = unsafe { getrandom(buf[off..].as_mut_ptr() as *mut c_void, buf.len() - off, 0) };
        if n < 0 {
            let e = errno();
            if e == 4 {
                continue;
            }
            code = -e;
            break;
        }
        off += n as usize;
    }
    op(&o).bytes = buf;
    crate::net::complete_now(&o, r, code);
    o
}
