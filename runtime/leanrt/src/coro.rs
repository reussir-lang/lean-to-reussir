//! Stacks and context switches for the scheduler's contexts (`sched`).
//!
//! Native Lean runs every task on a worker thread; here everything runs on
//! one thread, but a task that blocks (a contended mutex, a condition
//! variable, a promise nobody has resolved yet, a sleep) must let others go
//! on without finishing first. So a task the scheduler starts runs on a
//! stack of its own, and a blocked context is suspended by saving its
//! callee-saved registers on its stack and switching the stack pointer to
//! another context's (`switch`), as a thread switch does.
//!
//! A stack has the size of a native worker thread's (Lean's `lthread`:
//! 1 GiB on 64-bit targets, or `LEAN_STACK_SIZE_KB` plus a buffer), is
//! reserved without committing memory (`MAP_NORESERVE`), and has a guard
//! page below it that the stack-overflow handler (`rt`) recognizes, so
//! that overflowing a task's stack reports Lean's
//! `Stack overflow detected. Aborting.` as on a worker thread.

use std::ffi::c_void;
use std::sync::atomic::{AtomicUsize, Ordering};

extern "C" {
    fn mmap(addr: *mut c_void, len: usize, prot: i32, flags: i32, fd: i32, off: i64) -> *mut c_void;
    fn munmap(addr: *mut c_void, len: usize) -> i32;
    fn mprotect(addr: *mut c_void, len: usize, prot: i32) -> i32;
    fn sysconf(name: i32) -> i64;
}

const PROT_NONE: i32 = 0;
const PROT_READ: i32 = 1;
const PROT_WRITE: i32 = 2;
const MAP_PRIVATE: i32 = 0x02;
const MAP_ANONYMOUS: i32 = 0x20;
const MAP_NORESERVE: i32 = 0x4000;
const MAP_STACK: i32 = 0x20000;
const SC_PAGESIZE: i32 = 30;

/// A context's stack: `[base, base + len)`, the lowest page a guard.
pub struct Stack {
    base: usize,
    len: usize,
    guard_slot: usize,
}

/// Guard pages of the live stacks, `[lo, hi)` pairs (0 when free), read by
/// the SIGSEGV handler (`rt::segv_handler`), which must not allocate.
const GUARDS: usize = 4096;
pub static GUARD_LO: [AtomicUsize; GUARDS] = [const { AtomicUsize::new(0) }; GUARDS];
pub static GUARD_HI: [AtomicUsize; GUARDS] = [const { AtomicUsize::new(0) }; GUARDS];

/// Whether `addr` lies in the guard page of a context's stack.
pub fn in_guard(addr: usize) -> bool {
    for i in 0..GUARDS {
        let lo = GUARD_LO[i].load(Ordering::Relaxed);
        if lo != 0 && lo <= addr && addr < GUARD_HI[i].load(Ordering::Relaxed) {
            return true;
        }
    }
    false
}

fn page_size() -> usize {
    (unsafe { sysconf(SC_PAGESIZE) }) as usize
}

impl Stack {
    /// A new stack of `size` bytes (rounded up to pages) plus a guard page;
    /// `None` when the address space is exhausted.
    pub fn new(size: usize) -> Option<Stack> {
        let page = page_size();
        let size = (size + page - 1) / page * page;
        let len = size + page;
        let p = unsafe {
            mmap(std::ptr::null_mut(), len, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE | MAP_STACK, -1, 0)
        };
        if p as isize == -1 {
            return None;
        }
        let base = p as usize;
        unsafe { mprotect(p, page, PROT_NONE) };
        let mut guard_slot = usize::MAX;
        for i in 0..GUARDS {
            if GUARD_LO[i].load(Ordering::Relaxed) == 0 {
                GUARD_HI[i].store(base + page, Ordering::Relaxed);
                GUARD_LO[i].store(base, Ordering::Relaxed);
                guard_slot = i;
                break;
            }
        }
        Some(Stack { base, len, guard_slot })
    }

    /// The initial stack pointer of a context that starts by calling
    /// `entry(arg)` on this stack (`entry` never returns).
    pub fn init(&self, entry: extern "C" fn(usize) -> !, arg: usize) -> usize {
        let top = (self.base + self.len) & !15;
        unsafe { arch::init_frame(top, entry as usize, arg) }
    }
}

impl Stack {
    /// Give the stack's memory back (its contents are not needed any more);
    /// the address range stays reserved, for another context.
    pub fn release_memory(&self) {
        extern "C" {
            fn madvise(addr: *mut c_void, len: usize, advice: i32) -> i32;
        }
        const MADV_DONTNEED: i32 = 4;
        let page = page_size();
        unsafe { madvise((self.base + page) as *mut c_void, self.len - page, MADV_DONTNEED) };
    }
}

impl Drop for Stack {
    fn drop(&mut self) {
        if self.guard_slot != usize::MAX {
            GUARD_LO[self.guard_slot].store(0, Ordering::Relaxed);
            GUARD_HI[self.guard_slot].store(0, Ordering::Relaxed);
        }
        unsafe { munmap(self.base as *mut c_void, self.len) };
    }
}

/// Save the current context's registers on its stack, store its stack
/// pointer in `*save`, and continue the context whose stack pointer is
/// `to` (saved by an earlier `switch`, or made by `Stack::init`).
#[inline(always)]
pub unsafe fn switch(save: *mut usize, to: usize) {
    unsafe { l2r_coro_switch(save, to) }
}

extern "C" {
    fn l2r_coro_switch(save: *mut usize, to: usize);
}

#[cfg(target_arch = "aarch64")]
mod arch {
    // Callee-saved state of AAPCS64: x19-x28, the frame pointer x29, the
    // link register x30 (where `ret` continues) and the low halves of
    // v8-v15. A new context's frame "returns" into `l2r_coro_start`, which
    // calls `entry(arg)` (x19, x20) with the stack pointer at the top.
    core::arch::global_asm!(
        ".text",
        ".p2align 4",
        ".globl l2r_coro_switch",
        ".hidden l2r_coro_switch",
        ".type l2r_coro_switch, %function",
        "l2r_coro_switch:",
        "sub sp, sp, #160",
        "stp x19, x20, [sp, #0]",
        "stp x21, x22, [sp, #16]",
        "stp x23, x24, [sp, #32]",
        "stp x25, x26, [sp, #48]",
        "stp x27, x28, [sp, #64]",
        "stp x29, x30, [sp, #80]",
        "stp d8, d9, [sp, #96]",
        "stp d10, d11, [sp, #112]",
        "stp d12, d13, [sp, #128]",
        "stp d14, d15, [sp, #144]",
        "mov x9, sp",
        "str x9, [x0]",
        "mov sp, x1",
        "ldp x19, x20, [sp, #0]",
        "ldp x21, x22, [sp, #16]",
        "ldp x23, x24, [sp, #32]",
        "ldp x25, x26, [sp, #48]",
        "ldp x27, x28, [sp, #64]",
        "ldp x29, x30, [sp, #80]",
        "ldp d8, d9, [sp, #96]",
        "ldp d10, d11, [sp, #112]",
        "ldp d12, d13, [sp, #128]",
        "ldp d14, d15, [sp, #144]",
        "add sp, sp, #160",
        "ret",
        ".size l2r_coro_switch, . - l2r_coro_switch",
        ".p2align 4",
        ".globl l2r_coro_start",
        ".hidden l2r_coro_start",
        ".type l2r_coro_start, %function",
        "l2r_coro_start:",
        "mov x0, x20",
        "blr x19",
        "brk #0",
        ".size l2r_coro_start, . - l2r_coro_start",
    );

    extern "C" {
        fn l2r_coro_start();
    }

    pub unsafe fn init_frame(top: usize, entry: usize, arg: usize) -> usize {
        let sp = top - 160;
        let w = sp as *mut usize;
        unsafe {
            std::ptr::write_bytes(w, 0, 20);
            *w.add(0) = entry; // x19
            *w.add(1) = arg; // x20
            *w.add(10) = 0; // x29
            *w.add(11) = l2r_coro_start as *const () as usize; // x30
        }
        sp
    }
}

#[cfg(target_arch = "x86_64")]
mod arch {
    // Callee-saved state of the System V ABI: rbx, rbp, r12-r15, and the
    // MXCSR and x87 control words. A new context's frame "returns" into
    // `l2r_coro_start`, which calls `entry(arg)` (r12, r13).
    core::arch::global_asm!(
        ".text",
        ".p2align 4",
        ".globl l2r_coro_switch",
        ".hidden l2r_coro_switch",
        ".type l2r_coro_switch, @function",
        "l2r_coro_switch:",
        "push rbp",
        "push rbx",
        "push r12",
        "push r13",
        "push r14",
        "push r15",
        "sub rsp, 8",
        "stmxcsr [rsp]",
        "fnstcw [rsp + 4]",
        "mov [rdi], rsp",
        "mov rsp, rsi",
        "ldmxcsr [rsp]",
        "fldcw [rsp + 4]",
        "add rsp, 8",
        "pop r15",
        "pop r14",
        "pop r13",
        "pop r12",
        "pop rbx",
        "pop rbp",
        "ret",
        ".size l2r_coro_switch, . - l2r_coro_switch",
        ".p2align 4",
        ".globl l2r_coro_start",
        ".hidden l2r_coro_start",
        ".type l2r_coro_start, @function",
        "l2r_coro_start:",
        "mov rdi, r13",
        "call r12",
        "ud2",
        ".size l2r_coro_start, . - l2r_coro_start",
    );

    extern "C" {
        fn l2r_coro_start();
    }

    pub unsafe fn init_frame(top: usize, entry: usize, arg: usize) -> usize {
        // [csr][r15][r14][r13][r12][rbx][rbp][ret]: after the pops and
        // `ret` the stack pointer is `top` (16-byte aligned, as `call`
        // needs it).
        let sp = top - 64;
        let w = sp as *mut usize;
        unsafe {
            std::ptr::write_bytes(w, 0, 8);
            *(w as *mut u32) = 0x1F80; // MXCSR
            *((w as *mut u16).add(2)) = 0x037F; // x87 control word
            *w.add(3) = arg; // r13
            *w.add(4) = entry; // r12
            *w.add(7) = l2r_coro_start as *const () as usize;
        }
        sp
    }
}
