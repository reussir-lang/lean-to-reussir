//! Lean strings: one block like Lean's string object, a 32-byte header
//! (the reference count, the byte size, the capacity and the number of
//! characters, Lean's `m_length`) followed by the valid UTF-8 bytes (no
//! terminator). The character count is kept up to date by every function
//! that builds or changes a string, so that `String.length` is a field
//! read as natively.
//!
//! Positions are byte offsets (`String.Pos.Raw`). The rules on positions,
//! the comparisons and the character count are lean-runtime's
//! (`lean_runtime::semantics::string`, on the bytes); the functions here
//! make, grow and update strings, following Lean's C implementation in
//! `src/runtime/object.cpp`. Functions taking `LStr` by value consume it and
//! update it in place when it is unique.
//!
//! Positions arrive as `u64`; the Reussir side handles big `Nat` positions
//! (and the few functions where Lean's "not a scalar" case, `>= 2^63`,
//! differs from the out-of-range case) before calling in.

use crate::alloc::vec_from_slice;
use lean_runtime::semantics as sem;
use std::ffi::c_void;

extern "C" {
    fn mi_malloc(size: usize) -> *mut c_void;
    fn mi_realloc(p: *mut c_void, size: usize) -> *mut c_void;
    fn mi_free(p: *mut c_void);
}

/// The header of a string block:
///
/// ```text
///   0: count: u32, (padding)   the reference count Reussir's `rc.inc` bumps
///   8: len: usize              bytes in use
///  16: cap: usize              room for bytes
///  24: chars: u64              the number of characters (`m_length`)
///  32: bytes: [u8; cap]        valid UTF-8, the first `len` initialized
/// ```
///
/// `len` and `chars` are only written while the string is unique.
#[repr(C)]
struct Obj {
    count: u32,
    _pad: u32,
    len: usize,
    cap: usize,
    chars: u64,
}

const HDR: usize = std::mem::size_of::<Obj>();

/// The Reussir-visible string type: a `#[repr(transparent)]` pointer to its
/// block, owning one reference. The FFI contract for an opaque type (an rc
/// pointer whose `u32` count is at its address; `rc.dec` calls the drop
/// hook, which drops the Rust value) is all Reussir relies on, so `Clone`
/// and `Drop` here do the counting.
///
/// Safety argument for the raw block: every `LStr` points at a live block
/// from `alloc` or `grow` (`mi_malloc`/`mi_realloc`, 8-aligned: Reussir
/// builds mimalloc with `MI_MAX_ALIGN_SIZE=8`, which `Obj` needs) of
/// `HDR + cap` bytes or more, with `len <= cap` initialized bytes after the
/// header; the block is freed only by the reference that finds the count
/// at 1, and written or moved (`grow`) only through a unique handle (count
/// 1), which a move then replaces by the result.
#[repr(transparent)]
pub struct LStr(*mut Obj);

impl LStr {
    #[inline(always)]
    pub fn is_unique(&self) -> bool {
        unsafe { (*self.0).count == 1 }
    }
}

impl Clone for LStr {
    #[inline(always)]
    fn clone(&self) -> Self {
        // A clone is taken from a live reference: the count is at least
        // 1. Told to LLVM, a release right after (a read's `give`) folds
        // to nothing: no store at all for a shared block, such as a
        // constant's (`l2r_once_get` then a read).
        unsafe {
            let c = (*self.0).count;
            std::hint::assert_unchecked(c != 0);
            (*self.0).count = c + 1;
        }
        LStr(self.0)
    }
}

impl Drop for LStr {
    /// A shared handle is a decrement; the last reference is freed out of
    /// line (keeps the textures that read a string small enough to inline).
    #[inline(always)]
    fn drop(&mut self) {
        let o = self.0;
        unsafe {
            let c = (*o).count;
            if c == 1 {
                free(o)
            } else {
                (*o).count = c - 1;
            }
        }
    }
}

impl crate::Release for LStr {
    #[inline(always)]
    fn release(self) {
        std::mem::drop(self)
    }
}

#[cold]
#[inline(never)]
extern "C" fn free(o: *mut Obj) {
    unsafe { mi_free(o as *mut c_void) }
}

/// The bytes of the live string block at address `p`, borrowed while the
/// caller keeps a reference to it (`any::str_ref`: a boxed string).
#[inline(always)]
pub(crate) unsafe fn bytes_at<'a>(p: *mut u8) -> &'a [u8] {
    let o = p as *mut Obj;
    unsafe { std::slice::from_raw_parts(data(o), (*o).len) }
}

#[inline(always)]
unsafe fn data(o: *mut Obj) -> *mut u8 {
    (o as *mut u8).add(HDR)
}

/// A read of a string whose handle the caller gives up (the prelude's
/// read textures whose rule has a call in it, `l2r_string_get` and
/// others): `f` on the bytes. The release is decided before `f` runs: a
/// shared string is decremented first (another reference keeps the block
/// alive; one thread runs Lean code), so the rule's out-of-line paths (the
/// decoding of a character that is not ASCII; the panic of a big position
/// in `l2r_string_get_fast_word`) come after the decrement, and LLVM
/// removes the caller's increment and this decrement on every path. The
/// last reference runs `f`, then frees the block, as `Drop`.
#[inline(always)]
pub fn read_owned<R>(s: LStr, f: impl FnOnce(&[u8]) -> R) -> R {
    let o = s.0;
    std::mem::forget(s);
    unsafe {
        let c = (*o).count;
        if c != 1 {
            (*o).count = c - 1;
        }
        let r = f(std::slice::from_raw_parts(data(o), (*o).len));
        if c == 1 {
            free(o);
        }
        r
    }
}

/// Byte views of strings and byte buffers, for functions that accept either.
pub trait Utf8 {
    fn utf8(&self) -> &[u8];
}

impl Utf8 for [u8] {
    #[inline(always)]
    fn utf8(&self) -> &[u8] {
        self
    }
}

impl Utf8 for Vec<u8> {
    #[inline(always)]
    fn utf8(&self) -> &[u8] {
        self
    }
}

impl Utf8 for LStr {
    #[inline(always)]
    fn utf8(&self) -> &[u8] {
        unsafe { std::slice::from_raw_parts(data(self.0), (*self.0).len) }
    }
}

/// The bytes of a string.
#[inline(always)]
pub fn bytes(s: &LStr) -> &[u8] {
    s.utf8()
}

/// `String.decEq` (`lean_string_dec_eq`): two references to the same block
/// are equal without comparing the bytes, as natively (`lean_string_eq`:
/// `s1 == s2 ||` the sizes and the bytes). The lengths are compared first
/// here, then the blocks, then the bytes (the same answer; strings of other
/// lengths skip the block test: measured, 0.1 % fewer instructions in
/// monadic-interp than the block test first). Both handles are released.
#[inline(always)]
pub fn dec_eq(a: LStr, b: LStr) -> bool {
    let (x, y) = (a.utf8(), b.utf8());
    let r = x.len() == y.len() && (a.0 == b.0 || x == y);
    drop(a);
    drop(b);
    r
}


#[cold]
#[inline(never)]
fn oom() -> ! {
    crate::lean_internal_panic(lean_runtime::semantics::panic::InternalPanic::OutOfMemory)
}

/// The block size for room for `cap` bytes: rounded up to a multiple of 8
/// (mimalloc's blocks are, so the rounding costs nothing and becomes
/// capacity).
#[inline(always)]
fn bytes_for(cap: usize) -> usize {
    match cap.checked_add(HDR + 7) {
        Some(b) => b & !7,
        None => oom(),
    }
}

/// A unique empty string with room for (at least) `cap` bytes (the
/// prelude's `l2r_string_with_capacity`: `String.ofList` at its exact
/// size).
#[inline(never)]
pub fn with_capacity(cap: u64) -> LStr {
    alloc(cap as usize)
}

/// A fresh unique string with room for (at least) `cap` bytes, empty.
#[inline(always)]
fn alloc(cap: usize) -> LStr {
    let bytes = bytes_for(cap);
    unsafe {
        let o = mi_malloc(bytes) as *mut Obj;
        if o.is_null() {
            oom();
        }
        std::ptr::write(o, Obj { count: 1, _pad: 0, len: 0, cap: bytes - HDR, chars: 0 });
        LStr(o)
    }
}

/// A string of the bytes `b` (valid UTF-8) with `chars` characters
/// (`utf8_count(b)`).
#[inline]
pub fn from_counted(b: &[u8], chars: u64) -> LStr {
    debug_assert_eq!(chars, utf8_count(b));
    let s = alloc(b.len());
    unsafe {
        std::ptr::copy_nonoverlapping(b.as_ptr(), data(s.0), b.len());
        (*s.0).len = b.len();
        (*s.0).chars = chars;
    }
    s
}

#[inline]
pub fn from_bytes(b: &[u8]) -> LStr {
    from_counted(b, utf8_count(b))
}

/// A string of valid UTF-8 bytes (a copy, as natively).
#[inline]
pub fn from_vec(v: Vec<u8>) -> LStr {
    from_bytes(&v)
}

/// The bytes of a string as a vector (a copy, as natively), releasing it.
#[inline]
pub fn into_vec(s: LStr) -> Vec<u8> {
    let v = vec_from_slice(bytes(&s), 0);
    crate::rc_release(s);
    v
}

/// The character count a string caches (Lean's `m_length`):
/// lean-runtime's `utf8_strlen`, the count `lean_utf8_n_strlen` makes. Short
/// strings are counted in line, longer ones out of line, which keeps the
/// textures that make strings small enough to inline.
#[inline]
pub fn utf8_count(s: &[u8]) -> u64 {
    if s.len() <= 16 {
        sem::string::utf8_strlen(s)
    } else {
        utf8_count_long(s)
    }
}

#[inline(never)]
fn utf8_count_long(s: &[u8]) -> u64 {
    sem::string::utf8_strlen(s)
}

/// Unique access with room for `extra` more bytes, for a push or an
/// append: a shared string is copied first (at least doubling), a full one
/// grown.
#[inline]
fn make_mut(s: &mut LStr, extra: usize) -> *mut Obj {
    // By value: the address of `s` must not escape (see array::make_mut).
    if !s.is_unique() {
        unsafe { std::ptr::write(s, copy_shared(std::ptr::read(s), extra, true)) };
    } else {
        let o = s.0;
        let need = match unsafe { (*o).len }.checked_add(extra) {
            Some(n) => n,
            None => oom(),
        };
        if need > unsafe { (*o).cap } {
            unsafe { std::ptr::write(s, grow(std::ptr::read(s), need)) };
        }
    }
    s.0
}

/// A private copy of a shared string with room for `extra` more bytes,
/// releasing the shared one: at least doubling for a push or an append
/// (`double`; `lean_string_push` copies a shared string with twice its
/// size), with room for exactly `len + extra` bytes for `set_slow`: the new
/// size, or the old one when the new character is shorter (natively
/// `lean_string_utf8_set` makes a string of exactly its new size; doubling
/// cost each modified copy of a shared string its length again, review
/// HSTR-01).
#[cold]
#[inline(never)]
extern "C" fn copy_shared(s: LStr, extra: usize, double: bool) -> LStr {
    let src = bytes(&s);
    let room = if double { extra.max(src.len()) } else { extra };
    let cap = match src.len().checked_add(room) {
        Some(c) => c,
        None => oom(),
    };
    let c = alloc(cap);
    unsafe {
        std::ptr::copy_nonoverlapping(src.as_ptr(), data(c.0), src.len());
        (*c.0).len = src.len();
        (*c.0).chars = (*s.0).chars;
    }
    crate::rc_release(s);
    c
}

/// Grow a unique string to room for at least `need` bytes, at least
/// doubling (so appends are amortized O(1)). The capacity is all of the
/// block: mimalloc's size classes for small blocks (`alloc::good_size`), powers
/// of two beyond 4 KiB (as `array::grow`).
#[cold]
#[inline(never)]
extern "C" fn grow(s: LStr, need: usize) -> LStr {
    debug_assert!(s.is_unique());
    let o = s.0;
    // The block moves: the unique handle is given up for the result.
    std::mem::forget(s);
    unsafe {
        let want = need.max((*o).cap.saturating_mul(2)).max(8);
        let b = bytes_for(want);
        let bytes = if b > 4096 { b.checked_next_power_of_two().unwrap_or(b) } else { crate::alloc::good_size(b) };
        // `bytes >= b >= HDR + want`; realloc keeps the header and the
        // `len` bytes.
        let n = mi_realloc(o as *mut c_void, bytes) as *mut Obj;
        if n.is_null() {
            oom();
        }
        (*n).cap = bytes - HDR;
        LStr(n)
    }
}

/// Append bytes to a unique string with room for them (`make_mut`), and
/// count `chars` more characters.
#[inline(always)]
unsafe fn extend(o: *mut Obj, b: &[u8], chars: u64) {
    let n = (*o).len;
    debug_assert!(n + b.len() <= (*o).cap);
    std::ptr::copy_nonoverlapping(b.as_ptr(), data(o).add(n), b.len());
    (*o).len = n + b.len();
    (*o).chars += chars;
}

/// `String.push`: an inline fast path for an ASCII character appended to
/// a unique string with spare capacity.
#[inline(always)]
pub fn push(s: LStr, c: u32) -> LStr {
    if c < 0x80 && s.is_unique() {
        let o = s.0;
        unsafe {
            let n = (*o).len;
            if n < (*o).cap {
                *data(o).add(n) = c as u8;
                (*o).len = n + 1;
                (*o).chars += 1;
                return s;
            }
        }
    }
    push_slow(s, c)
}

#[inline(never)]
fn push_slow(s: LStr, c: u32) -> LStr {
    let mut s = s;
    let mut buf = [0u8; 4];
    let n = sem::string::push_unicode_scalar(c, &mut buf) as usize;
    // Room for the character's own bytes: a string made at its exact size
    // (`with_capacity`) takes its last character without growing.
    let o = make_mut(&mut s, n);
    unsafe { extend(o, &buf[..n], 1) };
    s
}

#[inline(always)]
pub fn append(a: LStr, b: LStr) -> LStr {
    if a.is_unique() {
        let o = a.0;
        // `b` holds a reference of its own, so it is another block.
        let bs = bytes(&b);
        unsafe {
            if (*o).len + bs.len() <= (*o).cap {
                extend(o, bs, (*b.0).chars);
                crate::rc_release(b);
                return a;
            }
        }
    }
    append_slow(a, b)
}

#[inline(never)]
fn append_slow(a: LStr, b: LStr) -> LStr {
    let bs = bytes(&b);
    if bs.is_empty() {
        crate::rc_release(b);
        return a;
    }
    let mut a = a;
    // Copying or growing `a` leaves `b`'s block in place (when `a` and `b`
    // are the same string, the copy releases only `a`'s reference).
    let o = make_mut(&mut a, bs.len());
    unsafe { extend(o, bytes(&b), (*b.0).chars) };
    crate::rc_release(b);
    a
}

/// `String.length`: the character count.
#[inline(always)]
pub fn length(s: &LStr) -> u64 {
    unsafe { (*s.0).chars }
}

/// The lead bytes `set` replaces a character at. lean-runtime's
/// `semantics::string::utf8_set` has the same rule (object.cpp's
/// `lean_string_utf8_set`); `set_slow` applies it to leanrt's own string
/// block (the lead byte's size, the end clamped to the size, a shared
/// string copied first, the character count kept).
#[inline]
fn is_utf8_first_byte(c: u8) -> bool {
    (c & 0x80) == 0 || (c & 0xe0) == 0xc0 || (c & 0xf0) == 0xe0 || (c & 0xf8) == 0xf0
}

/// `String.Pos.Raw.extract` (`lean_string_utf8_extract`): the bytes of
/// lean-runtime's `utf8_extract` range (a big position is `u64::MAX`).
#[inline(never)]
pub fn extract(s: LStr, b: u64, e: u64) -> LStr {
    let r = sem::string::utf8_extract(bytes(&s), b, e);
    of_range(s, r)
}

/// `String.extract` on valid positions (`lean_string_utf8_extract_fast`):
/// the bytes of lean-runtime's `utf8_extract_fast` range.
#[inline(never)]
pub fn extract_fast(s: LStr, b: u64, e: u64) -> LStr {
    let r = sem::string::utf8_extract_fast(bytes(&s), b, e);
    of_range(s, r)
}

/// The bytes `r` of `s` as a string, consuming `s`: `s` itself for the whole
/// string, else a copy. A string with as many characters as bytes is ASCII
/// (valid UTF-8 without continuation bytes), so every range of it is too:
/// the copy's count is its length, without counting.
#[inline]
fn of_range(s: LStr, r: std::ops::Range<usize>) -> LStr {
    let v = bytes(&s);
    if r.start == 0 && r.end == v.len() {
        return s;
    }
    let b = &v[r];
    let chars = if length(&s) == v.len() as u64 { b.len() as u64 } else { utf8_count(b) };
    let out = from_counted(b, chars);
    crate::rc_release(s);
    out
}

/// `String.Pos.Raw.set` for a scalar position. The fast path (natively
/// too) overwrites an ASCII character of a unique string with an ASCII
/// character. One character replaces one: the count does not change.
#[inline(always)]
pub fn set(s: LStr, i: u64, c: u32) -> LStr {
    if c < 0x80 && s.is_unique() {
        let o = s.0;
        unsafe {
            if (i as usize) < (*o).len {
                let b = data(o).add(i as usize);
                if *b < 0x80 {
                    *b = c as u8;
                    return s;
                }
            }
        }
    }
    set_slow(s, i, c)
}

#[inline(never)]
fn set_slow(s: LStr, i: u64, c: u32) -> LStr {
    let v = bytes(&s);
    let len = v.len();
    if i >= len as u64 {
        return s;
    }
    let i = i as usize;
    let old = v[i];
    if !is_utf8_first_byte(old) {
        return s;
    }
    let old_len = if old & 0x80 == 0 {
        1
    } else if (old & 0xe0) == 0xc0 {
        2
    } else if (old & 0xf0) == 0xe0 {
        3
    } else {
        4
    };
    let mut enc = [0u8; 4];
    let n = sem::string::push_unicode_scalar(c, &mut enc) as usize;
    // The old character's bytes `[i, end)` become the new one's `n`.
    let end = (i + old_len).min(len);
    let old_n = end - i;
    let extra = n.saturating_sub(old_n);
    // A shared string is copied with room for `len + extra` bytes (the new
    // size, or the old one for a shorter character), a unique one updated
    // in place (grown when full).
    let mut s = if s.is_unique() { s } else { copy_shared(s, extra, false) };
    let o = make_mut(&mut s, extra);
    unsafe {
        // `make_mut` keeps the bytes (`len` of them) and leaves room for
        // `len - old_n + n`; the tail moves within the block (memmove).
        let d = data(o);
        if n != old_n {
            std::ptr::copy(d.add(end), d.add(i + n), len - end);
            (*o).len = len - old_n + n;
        }
        std::ptr::copy_nonoverlapping(enc.as_ptr(), d.add(i), n);
    }
    s
}

/// An ASCII string.
#[inline]
fn from_ascii(b: &[u8]) -> LStr {
    from_counted(b, b.len() as u64)
}

/// `lean_string_of_usize` (`USize.repr`, and `Nat.repr` below 2^64): the
/// decimal digits, lean-runtime's (`sem::repr::decimal_u64_bytes`).
#[inline(never)]
pub fn of_u64(n: u64) -> LStr {
    from_ascii(sem::repr::decimal_u64_bytes(n, &mut [0; 20]))
}

/// The decimal text of `n`, with a `-` when negative (`Int.repr` of a
/// small value).
#[inline(never)]
pub fn of_i64(n: i64) -> LStr {
    let mut buf = [0u8; 21];
    let d = sem::repr::decimal_u64_bytes(n.unsigned_abs(), (&mut buf[1..]).try_into().unwrap());
    let k = d.len();
    if n < 0 {
        buf[20 - k] = b'-';
        from_ascii(&buf[20 - k..])
    } else {
        from_ascii(&buf[21 - k..])
    }
}

struct Global<T>(std::cell::UnsafeCell<T>);
unsafe impl<T> Sync for Global<T> {}

/// The strings of `Nat.reprArray` (natively a closed term, built at
/// initialization): `Nat.repr n` for `n < 128` returns the same string
/// every time, so it is shared and costs no allocation. Built on first use;
/// the table keeps one reference to each (the runtime is single-threaded).
static SMALL_REPR: Global<[*mut Obj; 128]> = Global(std::cell::UnsafeCell::new([std::ptr::null_mut(); 128]));

/// `Nat.repr n` for `n < 128`: the shared string.
#[inline(always)]
pub fn repr_small(n: u64) -> LStr {
    let p = match unsafe { (*SMALL_REPR.0.get()).get(n as usize) } {
        Some(&p) if !p.is_null() => p,
        _ => return repr_small_init(n),
    };
    // A new reference to the table's string.
    LStr::clone(&std::mem::ManuallyDrop::new(LStr(p)))
}

#[cold]
#[inline(never)]
extern "C" fn repr_small_init(n: u64) -> LStr {
    if n >= 128 {
        return of_u64(n);
    }
    let s = of_u64(n);
    // The table's reference.
    let p = std::mem::ManuallyDrop::new(s.clone()).0;
    unsafe { (*SMALL_REPR.0.get())[n as usize] = p };
    s
}

/// One empty string, kept for the run (as `SMALL_REPR`'s strings).
static SHARED_EMPTY: Global<usize> = Global(std::cell::UnsafeCell::new(0));

/// The shared empty string: a new reference, no allocation. lean2rr passes
/// it as the placeholder of a string parameter that is never read (the
/// slots of a state machine, Opt/StateMachines).
#[inline(always)]
pub fn shared_empty() -> LStr {
    let p = unsafe { *SHARED_EMPTY.0.get() };
    if p == 0 {
        return shared_empty_init();
    }
    let r = std::mem::ManuallyDrop::new(unsafe { std::mem::transmute::<usize, LStr>(p) });
    LStr::clone(&r)
}

#[cold]
#[inline(never)]
extern "C" fn shared_empty_init() -> LStr {
    let s = from_bytes(&[]);
    let p = unsafe { std::mem::transmute::<LStr, usize>(s.clone()) };
    unsafe { *SHARED_EMPTY.0.get() = p };
    s
}

/// The literal cache: the strings of lean2rr's literal constants (a
/// constant or closed term whose code is one string literal), one slot per
/// id of the program's literal table (`l2r_str_lit`). The generated
/// `l2r_str_lit_cached(id)` reads it: at the first read the slot is empty,
/// and the generated code makes the string from the table and stores it
/// (`lit_put`); every read takes a new reference to it (`lit_ready`,
/// `lit_get`). The slot keeps its reference for the rest of the run, as a
/// once-cell keeps a constant's value (`once`) and `SMALL_REPR` its
/// strings: a value read is never unique, so an update copies it, as
/// natively a closed term is made once and is persistent (never unique).
///
/// A slot's word is the string's address, never 0: 0 is an empty slot. The
/// slots below `LIT_FAST` are a table at a fixed address (in `.bss`:
/// untouched pages cost no memory), so, with the textures inlined, a read
/// of a set slot is one load, a test and the increment, as a constant's
/// (`once::has`). The other slots are in a record (`LIT_REC`).
///
/// There is no claim, unlike a once-cell (`once::claim`): making a
/// literal's string runs no Lean code, takes no lock and cannot switch the
/// scheduler's context, so no other context runs between the test and the
/// store. Single-threaded as `once`: the initializers run on the process's
/// main thread before `main`'s thread starts, and Lean code then runs on
/// `main`'s thread only.
pub const LIT_FAST: usize = 1 << 16;

#[repr(transparent)]
struct LitWord(std::cell::UnsafeCell<usize>);
struct LitTable([LitWord; LIT_FAST]);
unsafe impl Sync for LitTable {}

static LIT_TABLE: LitTable = LitTable([const { LitWord(std::cell::UnsafeCell::new(0)) }; LIT_FAST]);

/// The slots from `LIT_FAST` on (`LIT_REC[id - LIT_FAST]`).
static LIT_REC: Global<Vec<usize>> = Global(std::cell::UnsafeCell::new(Vec::new()));

/// The word of literal slot `id` (0: empty).
#[inline(always)]
fn lit_word(id: u64) -> usize {
    let i = id as usize;
    if i < LIT_FAST {
        unsafe { *LIT_TABLE.0[i].0.get() }
    } else {
        lit_rec_word(i)
    }
}

#[inline(never)]
fn lit_rec_word(i: usize) -> usize {
    let rec = unsafe { &*LIT_REC.0.get() };
    rec.get(i - LIT_FAST).copied().unwrap_or(0)
}

/// Whether literal slot `id` has its string (`l2r_lit_ready`): one load.
/// The empty side is marked cold (only the first read takes it).
#[inline(always)]
pub fn lit_ready(id: u64) -> bool {
    if lit_word(id) != 0 {
        return true;
    }
    std::hint::cold_path();
    false
}

/// Store `s`, the string of literal `id`, in its empty slot: the reference
/// moves into the slot (`l2r_lit_put`). Returns 0. `#[cold]`: Reussir's
/// language has no branch hint, so the attribute is the hint (as for the
/// slow paths of `nat`): LLVM then lays the first read's path out of line.
#[cold]
#[inline(never)]
pub extern "C" fn lit_put(id: u64, s: LStr) -> u64 {
    let w = std::mem::ManuallyDrop::new(s).0 as usize;
    let i = id as usize;
    let slot = if i < LIT_FAST {
        unsafe { &mut *LIT_TABLE.0[i].0.get() }
    } else {
        let rec = unsafe { &mut *LIT_REC.0.get() };
        if rec.len() <= i - LIT_FAST {
            rec.resize(i - LIT_FAST + 1, 0);
        }
        &mut rec[i - LIT_FAST]
    };
    if *slot != 0 {
        crate::internal_panic(&format!("leanrt: literal slot {} set twice", id))
    }
    *slot = w;
    0
}

/// A new reference to the string of set literal slot `id` (`l2r_lit_get`;
/// reading an empty slot is a runtime bug: reported). Inline: after
/// `lit_ready(id)` its load and test fold away.
#[inline(always)]
pub fn lit_get(id: u64) -> LStr {
    let w = lit_word(id);
    if w == 0 {
        lit_unset(id)
    }
    LStr::clone(&std::mem::ManuallyDrop::new(LStr(w as *mut Obj)))
}

/// A read of an empty literal slot. `extern "C"`: it cannot unwind (it
/// exits), so the inlined reads need no landing pad.
#[cold]
#[inline(never)]
extern "C" fn lit_unset(id: u64) -> ! {
    crate::internal_panic(&format!("leanrt: read of the empty literal slot {}", id))
}

/// `lean_mk_string_from_bytes`: validate, replacing each invalid
/// sequence start with U+FFFD as `lean_mk_string_lossy_recover` does
/// (lean-runtime's `semantics::string::lossy_utf8`).
pub fn from_bytes_lossy(s: &[u8]) -> LStr {
    if std::str::from_utf8(s).is_ok() {
        return from_bytes(s);
    }
    let mut out = String::with_capacity(s.len() + 8);
    // A `String`'s writes cannot fail.
    let _ = sem::string::lossy_utf8(s, &mut out);
    from_vec(out.into_bytes())
}

/// `lean_string_validate_utf8`.
#[inline]
pub fn validate(s: &[u8]) -> bool {
    std::str::from_utf8(s).is_ok()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn s(b: &str) -> LStr {
        from_bytes(b.as_bytes())
    }

    /// The cached count agrees with a recount, and the bytes are `want`.
    fn ok(x: &LStr, want: &str) {
        assert_eq!(bytes(x), want.as_bytes());
        assert_eq!(length(x), want.chars().count() as u64, "count of {:?}", want);
    }

    #[test]
    fn counts_follow_every_update() {
        let a = push(push(s("aé"), 'x' as u32), 0x1F600);
        ok(&a, "aéx😀");
        let shared = a.clone();
        let b = push(shared, 'ü' as u32); // copy-on-write
        ok(&b, "aéx😀ü");
        ok(&a, "aéx😀");
        let c = append(a.clone(), b.clone());
        ok(&c, "aéx😀aéx😀ü");
        ok(&append(s(""), s("€")), "€");
        ok(&append(s("€"), s("")), "€");
        // set: every width over every width, unique and shared.
        let ws = ['a', 'é', '€', '😀'];
        for &o in &ws {
            for &n in &ws {
                let base = format!("x{}y", o);
                let t = set(s(&base), 1, n as u32);
                ok(&t, &format!("x{}y", n));
                let keep = s(&base);
                let t2 = set(keep.clone(), 1, n as u32);
                ok(&t2, &format!("x{}y", n));
                ok(&keep, &base);
                // Not a character boundary, or out of range: unchanged.
                if o.len_utf8() > 1 {
                    ok(&set(s(&base), 2, n as u32), &base);
                }
                ok(&set(s(&base), 99, n as u32), &base);
            }
        }
        ok(&extract(s("aé€😀b"), 1, 6), "é€");
        ok(&extract(s("aé€😀b"), 2, 6), "");
        ok(&extract(s("aé€😀b"), 0, 99), "aé€😀b");
        // Ranges of an ASCII string (counted by their length) and of strings
        // with one character of each width, short and long, unique and
        // shared.
        for t in ["plain ascii text, long enough to pass sixteen bytes", "ascii then é", "😀 first", "mid € dle"] {
            let n = t.len() as u64;
            for b in 0..=n {
                for e in b..=n + 1 {
                    let want = t.get(b as usize..(e.min(n)) as usize).unwrap_or("");
                    if t.is_char_boundary(b as usize) && t.is_char_boundary(e.min(n) as usize) {
                        ok(&extract(s(t), b, e), want);
                        let keep = s(t);
                        ok(&extract(keep.clone(), b, e), want);
                        ok(&keep, t);
                    }
                }
            }
        }
        ok(&of_u64(18446744073709551615), "18446744073709551615");
        ok(&of_i64(-9223372036854775808), "-9223372036854775808");
        ok(&from_bytes_lossy(b"a\xffb\xe2\x82"), "a\u{fffd}b\u{fffd}");
        ok(&from_vec("é€😀".as_bytes().to_vec()), "é€😀");
        let long = "é".repeat(100) + &"a".repeat(37);
        ok(&s(&long), &long);
    }

    #[test]
    fn small_reprs_are_shared() {
        let a = repr_small(7);
        let b = repr_small(7);
        ok(&a, "7");
        assert!(std::ptr::eq(bytes(&a).as_ptr(), bytes(&b).as_ptr()));
        assert!(!a.is_unique());
        ok(&repr_small(127), "127");
        ok(&repr_small(0), "0");
        let p = push(b, '!' as u32); // shared: copied
        ok(&p, "7!");
        ok(&repr_small(7), "7");
    }

    #[test]
    fn byte_array_round_trip() {
        let a = s("é€");
        let keep = a.clone();
        let v = crate::array::bytes_of_string(a); // shared: copied
        ok(&keep, "é€");
        let back = crate::array::string_of_bytes(v);
        ok(&back, "é€");
        let v2 = crate::array::bytes_of_string(back); // unique: copied too
        ok(&crate::array::string_of_bytes(v2), "é€");
    }

    fn count(x: &LStr) -> u32 {
        unsafe { (*x.0).count }
    }

    fn cap(x: &LStr) -> usize {
        unsafe { (*x.0).cap }
    }

    #[test]
    fn layout() {
        // Lean's string header: the count word, size, capacity and length.
        assert_eq!(HDR, 32);
        assert_eq!(std::mem::size_of::<LStr>(), 8);
        assert_eq!(std::mem::offset_of!(Obj, count), 0);
        // The block rounding becomes capacity.
        assert_eq!(cap(&s("abc")), 8);
        assert_eq!(cap(&s("")), 0);
        assert_eq!(cap(&s("12345678")), 8);
        assert_eq!(cap(&s("123456789")), 16);
    }

    #[test]
    fn handles_and_growth() {
        let a = s("x");
        let b = a.clone();
        assert_eq!(count(&a), 2);
        crate::rc_release(b);
        assert_eq!(count(&a), 1);
        // Unique pushes grow the block in place; every byte and the count
        // survive the moves.
        let mut a = a;
        let mut want = String::from("x");
        for i in 0..20000u32 {
            let c = match i % 4 {
                0 => 'a',
                1 => 'é',
                2 => '€',
                _ => '😀',
            };
            a = push(a, c as u32);
            want.push(c);
            assert!(bytes(&a).len() <= cap(&a));
        }
        ok(&a, &want);
        assert_eq!(count(&a), 1);
        // Appending a shared string to itself: one copy, then the bytes of
        // the (unchanged) original.
        let small = s("ab€");
        let twice = append(small.clone(), small.clone());
        ok(&twice, "ab€ab€");
        ok(&small, "ab€");
        assert_eq!(count(&small), 1);
        // A unique string with room appends in place.
        let mut r = s("");
        for _ in 0..100 {
            r = append(r, small.clone());
        }
        ok(&r, &"ab€".repeat(100));
        assert_eq!(count(&small), 1);
        // Growing `set`s near the end of a full block, shrinking ones, on
        // unique and shared strings.
        let full = s("12345678"); // capacity 8: no room
        ok(&set(full, 7, '😀' as u32), "1234567😀");
        // A set copies a shared string at `len + extra` (HSTR-01); a push
        // or an append copies one with room to double.
        let long = s(&"a".repeat(40));
        let t = set(long.clone(), 3, '€' as u32); // 3 bytes for 1: 42 bytes
        ok(&t, &format!("aaa€{}", "a".repeat(36)));
        assert_eq!(cap(&t), 48);
        let t = set(long.clone(), 3, 'b' as u32);
        assert_eq!(cap(&t), 40);
        let p = push(long.clone(), 'b' as u32);
        assert!(cap(&p) >= 80);
        let p = append(long.clone(), s("b"));
        assert!(cap(&p) >= 80);
        ok(&long, &"a".repeat(40));
        assert_eq!(count(&long), 1);
        let wide = s("a😀b");
        let keep = wide.clone();
        ok(&set(wide, 1, 'z' as u32), "azb");
        ok(&keep, "a😀b");
        ok(&of_i64(0), "0");
        ok(&of_i64(-7), "-7");
        ok(&of_i64(i64::MAX), "9223372036854775807");
        ok(&of_u64(0), "0");
    }

    /// The literal cache: a slot of the table and one of the record (slots
    /// far from any other test's: the cache is global). A read is a new
    /// reference to the one string; it is never unique, so a push copies
    /// it and the slot's string stays as it was.
    #[test]
    fn literal_cache() {
        for id in [(LIT_FAST - 3) as u64, (LIT_FAST + 5) as u64] {
            assert!(!lit_ready(id));
            assert_eq!(lit_put(id, s("lit€")), 0);
            assert!(lit_ready(id));
            let a = lit_get(id);
            let b = lit_get(id);
            ok(&a, "lit€");
            assert_eq!(a.0, b.0);
            assert_eq!(count(&a), 3);
            let p = push(a, '!' as u32);
            ok(&p, "lit€!");
            assert_eq!(count(&b), 2);
            drop(b);
            let c = lit_get(id);
            ok(&c, "lit€");
            assert_eq!(count(&c), 2);
        }
        assert!(!lit_ready((LIT_FAST + 4) as u64));
    }

    /// `dec_eq`: the same block, equal bytes in two blocks, other lengths
    /// and other bytes; both handles are released every time.
    #[test]
    fn dec_eq_releases_both() {
        let a = s("abc");
        assert!(dec_eq(a.clone(), a.clone()));
        assert_eq!(count(&a), 1);
        let b = s("abc");
        assert!(dec_eq(a.clone(), b.clone()));
        assert!(!dec_eq(a.clone(), s("abd")));
        assert!(!dec_eq(a.clone(), s("ab")));
        assert!(dec_eq(s(""), shared_empty()));
        assert_eq!((count(&a), count(&b)), (1, 1));
    }
}
