//! Lean strings: one block like Lean's string object, a 32-byte header
//! (the reference count, the byte size, the capacity and the number of
//! characters, Lean's `m_length`) followed by the valid UTF-8 bytes (no
//! terminator). The character count is kept up to date by every function
//! that builds or changes a string, so that `String.length` is a field
//! read as natively.
//!
//! Positions are byte offsets (`String.Pos.Raw`). Every function follows the
//! C implementation in Lean's `src/runtime/object.cpp` (which in turn follows
//! the Lean-level reference model), including its behaviour on positions
//! that are out of range or not at a character boundary. Functions taking
//! `LStr` by value consume it and update it in place when it is unique.
//!
//! Positions arrive as `u64`; the Reussir side handles `Nat::Big` positions
//! (and the few functions where Lean's "not a scalar" case, `>= 2^63`,
//! differs from the out-of-range case) before calling in.

use crate::alloc::vec_from_slice;
use std::ffi::c_void;

extern "C" {
    fn mi_malloc(size: usize) -> *mut c_void;
    fn mi_realloc(p: *mut c_void, size: usize) -> *mut c_void;
    fn mi_free(p: *mut c_void);
    fn mi_good_size(size: usize) -> usize;
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
        unsafe { (*self.0).count += 1 };
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

#[inline(always)]
unsafe fn data(o: *mut Obj) -> *mut u8 {
    (o as *mut u8).add(HDR)
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

/// `lean_char_default_value`: `'A'`.
pub const DEFAULT_CHAR: u32 = 65;

#[cold]
#[inline(never)]
fn oom() -> ! {
    crate::internal_panic("out of memory")
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

/// Number of Unicode scalars of valid UTF-8, counted like `utf8_strlen`:
/// every byte that is not a continuation byte starts a character.
#[inline]
pub fn utf8_count(s: &[u8]) -> u64 {
    if s.len() <= 16 {
        let mut n = 0;
        for &b in s {
            n += ((b & 0xC0) != 0x80) as u64;
        }
        n
    } else {
        utf8_count_long(s)
    }
}

#[inline(never)]
fn utf8_count_long(s: &[u8]) -> u64 {
    s.iter().filter(|&&b| (b & 0xC0) != 0x80).count() as u64
}

/// The UTF-8 encoding of a scalar into `buf`, returning its length
/// (`utf8.cpp:push_unicode_scalar`, which also encodes invalid code points,
/// by masking, as C does).
#[inline(always)]
pub fn encode_scalar(buf: &mut [u8; 4], code: u32) -> usize {
    if code < 0x80 {
        buf[0] = code as u8;
        1
    } else if code < 0x800 {
        buf[0] = ((code >> 6) & 0x1F) as u8 | 0xC0;
        buf[1] = (code & 0x3F) as u8 | 0x80;
        2
    } else if code < 0x10000 {
        buf[0] = ((code >> 12) & 0x0F) as u8 | 0xE0;
        buf[1] = ((code >> 6) & 0x3F) as u8 | 0x80;
        buf[2] = (code & 0x3F) as u8 | 0x80;
        3
    } else {
        buf[0] = ((code >> 18) & 0x07) as u8 | 0xF0;
        buf[1] = ((code >> 12) & 0x3F) as u8 | 0x80;
        buf[2] = ((code >> 6) & 0x3F) as u8 | 0x80;
        buf[3] = (code & 0x3F) as u8 | 0x80;
        4
    }
}

/// `utf8.cpp:push_unicode_scalar`.
#[inline]
pub fn push_scalar(v: &mut Vec<u8>, code: u32) {
    let mut buf = [0u8; 4];
    let n = encode_scalar(&mut buf, code);
    v.extend_from_slice(&buf[..n]);
}

/// Unique access with room for `extra` more bytes, for an in-place update:
/// a shared string is copied first, a full one grown.
#[inline]
fn make_mut(s: &mut LStr, extra: usize) -> *mut Obj {
    // By value: the address of `s` must not escape (see array::make_mut).
    if !s.is_unique() {
        unsafe { std::ptr::write(s, copy_shared(std::ptr::read(s), extra)) };
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

/// A private copy of a shared string (with room for `extra` more bytes, at
/// least doubling as `lean_string_push` does), releasing the shared one.
#[cold]
#[inline(never)]
extern "C" fn copy_shared(s: LStr, extra: usize) -> LStr {
    let src = bytes(&s);
    let cap = match src.len().checked_add(extra.max(src.len())) {
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
/// block: mimalloc's size classes for small blocks (`mi_good_size`), powers
/// of two beyond 4 KiB (as `tagvec::grow`).
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
        let bytes = if b > 4096 { b.checked_next_power_of_two().unwrap_or(b) } else { mi_good_size(b) };
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
    let n = encode_scalar(&mut buf, c);
    let o = make_mut(&mut s, 4);
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

#[inline]
fn is_utf8_first_byte(c: u8) -> bool {
    (c & 0x80) == 0 || (c & 0xe0) == 0xc0 || (c & 0xf0) == 0xe0 || (c & 0xf8) == 0xf0
}

/// `lean_string_utf8_get_core`: decode at `i < size`, validating the value
/// ranges (not the continuation bits), or `None`.
#[inline(never)]
fn get_core(s: &[u8], size: usize, i: usize) -> Option<u32> {
    let c = s[i] as u32;
    if c & 0x80 == 0 {
        return Some(c);
    }
    let at = |k: usize| -> u32 { s.get(k).copied().unwrap_or(0) as u32 };
    if (c & 0xe0) == 0xc0 && i + 1 < size {
        let r = ((c & 0x1f) << 6) | (at(i + 1) & 0x3f);
        if r >= 0x80 {
            return Some(r);
        }
    }
    if (c & 0xf0) == 0xe0 && i + 2 < size {
        let r = ((c & 0x0f) << 12) | ((at(i + 1) & 0x3f) << 6) | (at(i + 2) & 0x3f);
        if r >= 0x800 && !(0xD800..=0xDFFF).contains(&r) {
            return Some(r);
        }
    }
    if (c & 0xf8) == 0xf0 && i + 3 < size {
        let r = ((c & 0x07) << 18) | ((at(i + 1) & 0x3f) << 12) | ((at(i + 2) & 0x3f) << 6) | (at(i + 3) & 0x3f);
        if (0x10000..=0x10FFFF).contains(&r) {
            return Some(r);
        }
    }
    None
}

/// `String.Pos.Raw.get`: the character at byte `i`, or `'A'`.
#[inline(always)]
pub fn get(s: &[u8], i: u64) -> u32 {
    match s.get(i as usize) {
        None => DEFAULT_CHAR,
        Some(&c) if c < 0x80 => c as u32,
        Some(_) => get_core(s, s.len(), i as usize).unwrap_or(DEFAULT_CHAR),
    }
}

/// `String.Pos.Raw.get?`: `0x110000` encodes `none` (not a scalar value).
#[inline]
pub fn get_opt(s: &[u8], i: u64) -> u32 {
    if i >= s.len() as u64 {
        return 0x110000;
    }
    get_core(s, s.len(), i as usize).unwrap_or(0x110000)
}

/// `lean_string_utf8_get_fast` (valid position): note the cold path bounds
/// against the size including C's terminating NUL.
#[inline(always)]
pub fn get_fast(s: &[u8], i: u64) -> u32 {
    let i = i as usize;
    match s.get(i) {
        None => DEFAULT_CHAR,
        Some(&c) if c & 0x80 == 0 => c as u32,
        Some(_) => get_core(s, s.len() + 1, i).unwrap_or(DEFAULT_CHAR),
    }
}

/// `String.Pos.Raw.next` for `i < size`; `0` stands for "the position is at
/// or past the end" (the caller then returns `i + 1` as a `Nat`).
#[inline(always)]
pub fn next(s: &[u8], i: u64) -> u64 {
    if i >= s.len() as u64 {
        return 0;
    }
    let c = s[i as usize];
    i + if c & 0x80 == 0 {
        1
    } else if (c & 0xe0) == 0xc0 {
        2
    } else if (c & 0xf0) == 0xe0 {
        3
    } else if (c & 0xf8) == 0xf0 {
        4
    } else {
        1
    }
}

/// `lean_string_utf8_next_fast` (valid position before the end).
#[inline(always)]
pub fn next_fast(s: &[u8], i: u64) -> u64 {
    match s.get(i as usize) {
        None => i + 1,
        Some(&c) => {
            i + if c & 0x80 == 0 {
                1
            } else if (c & 0xe0) == 0xc0 {
                2
            } else if (c & 0xf0) == 0xe0 {
                3
            } else if (c & 0xf8) == 0xf0 {
                4
            } else {
                1
            }
        }
    }
}

/// `String.Pos.Raw.prev`.
#[inline(always)]
pub fn prev(s: &[u8], i: u64) -> u64 {
    let sz = s.len() as u64;
    if i == 0 {
        return 0;
    }
    if i > sz {
        return i - 1;
    }
    let mut i = (i - 1) as usize;
    while !is_utf8_first_byte(s[i]) {
        if i == 0 {
            break;
        }
        i -= 1;
    }
    i as u64
}

/// `String.Pos.Raw.isValid`.
#[inline]
pub fn is_valid_pos(s: &[u8], i: u64) -> bool {
    let sz = s.len() as u64;
    if i > sz {
        return false;
    }
    if i == sz {
        return true;
    }
    is_utf8_first_byte(s[i as usize])
}

/// `String.Pos.Raw.extract` for scalar positions.
#[inline(never)]
pub fn extract(s: LStr, b: u64, e: u64) -> LStr {
    let v = bytes(&s);
    let sz = v.len() as u64;
    if b >= e || b >= sz || !is_utf8_first_byte(v[b as usize]) {
        crate::rc_release(s);
        return from_counted(&[], 0);
    }
    let mut e = e.min(sz);
    if e < sz && !is_utf8_first_byte(v[e as usize]) {
        e = sz;
    }
    if b == 0 && e == sz {
        return s;
    }
    let r = from_bytes(&v[b as usize..e as usize]);
    crate::rc_release(s);
    r
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
    let n = encode_scalar(&mut enc, c);
    // The old character's bytes `[i, end)` become the new one's `n`.
    let end = (i + old_len).min(len);
    let old_n = end - i;
    let mut s = s;
    let o = make_mut(&mut s, n.saturating_sub(old_n));
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

#[inline]
pub fn dec_eq(a: &[u8], b: &[u8]) -> bool {
    a == b
}

/// `lean_string_lt`: bytewise lexicographic (= code point order for UTF-8).
#[inline]
pub fn dec_lt(a: &[u8], b: &[u8]) -> bool {
    a < b
}

/// `lean_string_compare`: 0 = lt, 1 = eq, 2 = gt (`Ordering` constructor
/// indices).
#[inline]
pub fn compare(a: &[u8], b: &[u8]) -> u8 {
    match a.cmp(b) {
        std::cmp::Ordering::Less => 0,
        std::cmp::Ordering::Equal => 1,
        std::cmp::Ordering::Greater => 2,
    }
}

#[inline]
pub fn hash(s: &[u8]) -> u64 {
    crate::hash::murmur64a(s, 11)
}

/// An ASCII string.
#[inline]
fn from_ascii(b: &[u8]) -> LStr {
    from_counted(b, b.len() as u64)
}

/// `lean_string_of_usize`.
#[inline(never)]
pub fn of_u64(n: u64) -> LStr {
    let mut buf = [0u8; 20];
    let mut i = 20;
    let mut n = n;
    loop {
        i -= 1;
        buf[i] = b'0' + (n % 10) as u8;
        n /= 10;
        if n == 0 {
            break;
        }
    }
    from_ascii(&buf[i..])
}

/// Decimal representation of a signed word.
#[inline(never)]
pub fn of_i64(n: i64) -> LStr {
    let mut buf = [0u8; 21];
    let mut i = 21;
    let mut m = n.unsigned_abs();
    loop {
        i -= 1;
        buf[i] = b'0' + (m % 10) as u8;
        m /= 10;
        if m == 0 {
            break;
        }
    }
    if n < 0 {
        i -= 1;
        buf[i] = b'-';
    }
    from_ascii(&buf[i..])
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
static SHARED_EMPTY: Global<*mut Obj> = Global(std::cell::UnsafeCell::new(std::ptr::null_mut()));

/// The shared empty string: a new reference, no allocation. lean2rr passes
/// it as the placeholder of a string parameter that is never read (the
/// slots of a state machine, Opt/StateMachines).
#[inline(always)]
pub fn shared_empty() -> LStr {
    let p = unsafe { *SHARED_EMPTY.0.get() };
    if p.is_null() {
        return shared_empty_init();
    }
    // A new reference to the kept string.
    LStr::clone(&std::mem::ManuallyDrop::new(LStr(p)))
}

#[cold]
#[inline(never)]
extern "C" fn shared_empty_init() -> LStr {
    let s = from_bytes(b"");
    // The kept reference.
    let p = std::mem::ManuallyDrop::new(s.clone()).0;
    unsafe { *SHARED_EMPTY.0.get() = p };
    s
}

/// `lean_mk_string_from_bytes`: validate, replacing each maximal invalid
/// sequence start with U+FFFD as `lean_mk_string_lossy_recover` does.
pub fn from_bytes_lossy(s: &[u8]) -> LStr {
    if std::str::from_utf8(s).is_ok() {
        return from_bytes(s);
    }
    let mut out = Vec::with_capacity(s.len() + 8);
    let mut pos = 0;
    let mut start = 0;
    while pos < s.len() {
        match validate_one(s, pos) {
            Some(p) => pos = p,
            None => {
                out.extend_from_slice(&s[start..pos]);
                out.extend_from_slice("\u{fffd}".as_bytes());
                pos += 1;
                while pos < s.len() && (s[pos] & 0xc0) == 0x80 {
                    pos += 1;
                }
                start = pos;
            }
        }
    }
    out.extend_from_slice(&s[start..pos]);
    from_vec(out)
}

/// `validate_utf8_one`: the position after one valid character, or `None`.
fn validate_one(s: &[u8], pos: usize) -> Option<usize> {
    let size = s.len();
    let c = s[pos] as u32;
    if c & 0x80 == 0 {
        Some(pos + 1)
    } else if (c & 0xe0) == 0xc0 {
        if pos + 1 >= size {
            return None;
        }
        let c1 = s[pos + 1] as u32;
        if c1 & 0xc0 != 0x80 {
            return None;
        }
        let r = ((c & 0x1f) << 6) | (c1 & 0x3f);
        if r < 0x80 {
            return None;
        }
        Some(pos + 2)
    } else if (c & 0xf0) == 0xe0 {
        if pos + 2 >= size {
            return None;
        }
        let (c1, c2) = (s[pos + 1] as u32, s[pos + 2] as u32);
        if c1 & 0xc0 != 0x80 || c2 & 0xc0 != 0x80 {
            return None;
        }
        let r = ((c & 0x0f) << 12) | ((c1 & 0x3f) << 6) | (c2 & 0x3f);
        if r < 0x800 || (0xD800..=0xDFFF).contains(&r) {
            return None;
        }
        Some(pos + 3)
    } else if (c & 0xf8) == 0xf0 {
        if pos + 3 >= size {
            return None;
        }
        let (c1, c2, c3) = (s[pos + 1] as u32, s[pos + 2] as u32, s[pos + 3] as u32);
        if c1 & 0xc0 != 0x80 || c2 & 0xc0 != 0x80 || c3 & 0xc0 != 0x80 {
            return None;
        }
        let r = ((c & 0x07) << 18) | ((c1 & 0x3f) << 12) | ((c2 & 0x3f) << 6) | (c3 & 0x3f);
        if !(0x10000..=0x10FFFF).contains(&r) {
            return None;
        }
        Some(pos + 4)
    } else {
        None
    }
}

/// `lean_string_validate_utf8`.
#[inline]
pub fn validate(s: &[u8]) -> bool {
    std::str::from_utf8(s).is_ok()
}

/// `lean_string_memcmp`.
#[inline]
pub fn memcmp(a: &[u8], b: &[u8], ls: u64, rs: u64, len: u64) -> bool {
    let (ls, rs, len) = (ls as usize, rs as usize, len as usize);
    match (a.get(ls..ls + len), b.get(rs..rs + len)) {
        (Some(x), Some(y)) => x == y,
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// `String.Internal.*` functions implemented by exported Lean definitions.

/// `String.Internal.isPrefixOf p s`.
#[inline]
pub fn is_prefix_of(p: &[u8], s: &[u8]) -> bool {
    s.starts_with(p)
}

/// Byte offset after skipping `n` characters from `from` (clamped to the end).
fn skip_chars(s: &[u8], mut i: usize, mut n: u64) -> usize {
    while n > 0 && i < s.len() {
        i = next_fast(s, i as u64) as usize;
        n -= 1;
    }
    i.min(s.len())
}

/// `String.Internal.drop s n`: drop the first `n` characters.
#[inline(never)]
pub fn drop(s: LStr, n: u64) -> LStr {
    let v = bytes(&s);
    let i = skip_chars(v, 0, n);
    if i == 0 {
        return s;
    }
    let r = from_bytes(&v[i..]);
    crate::rc_release(s);
    r
}

/// `String.Internal.dropRight s n`: drop the last `n` characters.
#[inline(never)]
pub fn drop_right(s: LStr, n: u64) -> LStr {
    let v = bytes(&s);
    let mut e = v.len() as u64;
    let mut n = n;
    while n > 0 && e > 0 {
        e = prev(v, e);
        n -= 1;
    }
    if e == v.len() as u64 {
        return s;
    }
    let r = from_bytes(&v[..e as usize]);
    crate::rc_release(s);
    r
}

/// Byte position of the first occurrence of character `c`, or the end.
#[inline]
pub fn pos_of(s: &[u8], c: u32) -> u64 {
    let mut i = 0usize;
    while i < s.len() {
        if get_fast(s, i as u64) == c {
            return i as u64;
        }
        i = next_fast(s, i as u64) as usize;
    }
    s.len() as u64
}

#[inline]
pub fn contains(s: &[u8], c: u32) -> bool {
    pos_of(s, c) < s.len() as u64
}

/// `String.Internal.pushn s c n`.
#[inline(never)]
pub fn pushn(s: LStr, c: u32, n: u64) -> LStr {
    if n == 0 {
        return s;
    }
    let mut enc = [0u8; 4];
    let k = encode_scalar(&mut enc, c);
    // More bytes than memory can hold: out of memory (as a `Nat::Big` count).
    let extra = match (k as u64).checked_mul(n) {
        Some(b) if b <= isize::MAX as u64 => b as usize,
        _ => oom(),
    };
    let mut s = s;
    let o = make_mut(&mut s, extra);
    unsafe {
        for _ in 0..n {
            extend(o, &enc[..k], 0);
        }
        (*o).chars += n;
    }
    s
}

/// ASCII whitespace as used by `String.trimAscii`: `Char.isWhitespace`
/// restricted to ASCII (space, `\t`, `\n`, `\r`).
#[inline]
fn is_ascii_ws(b: u8) -> bool {
    b == b' ' || b == b'\t' || b == b'\n' || b == b'\r'
}

/// `String.Internal.trim` (= `trimAscii`).
#[inline(never)]
pub fn trim(s: LStr) -> LStr {
    let v = bytes(&s);
    let b = v.iter().position(|&c| !is_ascii_ws(c)).unwrap_or(v.len());
    let e = v.iter().rposition(|&c| !is_ascii_ws(c)).map(|p| p + 1).unwrap_or(b);
    if b == 0 && e == v.len() {
        return s;
    }
    // Only ASCII whitespace (one byte, one character each) is removed.
    let r = from_counted(&v[b..e.max(b)], length(&s) - (v.len() - (e.max(b) - b)) as u64);
    crate::rc_release(s);
    r
}

/// `String.Internal.capitalize`: upper-case the first character (ASCII
/// letters only, as `Char.toUpper`).
#[inline(never)]
pub fn capitalize(s: LStr) -> LStr {
    match bytes(&s).first() {
        Some(&c) if c.is_ascii_lowercase() => {
            let mut s = s;
            let o = make_mut(&mut s, 0);
            unsafe { *data(o) = c.to_ascii_uppercase() };
            s
        }
        _ => s,
    }
}

/// `String.Internal.offsetOfPos s pos`: the number of characters that start
/// strictly before byte `pos` (stepping by `next` from 0 while `< pos`).
#[inline]
pub fn offset_of_pos(s: &[u8], pos: u64) -> u64 {
    let mut i = 0u64;
    let mut k = 0u64;
    while i < pos && i < s.len() as u64 {
        i = next_fast(s, i);
        k += 1;
    }
    k
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
        ok(&drop(s("é€😀b"), 2), "😀b");
        ok(&drop_right(s("é€😀b"), 2), "é€");
        ok(&trim(s(" \t é€ \n")), "é€");
        ok(&trim(s("   ")), "");
        ok(&pushn(s("é"), '€' as u32, 3), "é€€€");
        ok(&capitalize(s("ébc")), "ébc");
        ok(&capitalize(s("abc")), "Abc");
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
        let wide = s("a😀b");
        let keep = wide.clone();
        ok(&set(wide, 1, 'z' as u32), "azb");
        ok(&keep, "a😀b");
        ok(&pushn(s("ab"), '€' as u32, 1000), &("ab".to_string() + &"€".repeat(1000)));
        ok(&pushn(keep.clone(), 'q' as u32, 0), "a😀b");
        ok(&of_i64(0), "0");
        ok(&of_i64(-7), "-7");
        ok(&of_i64(i64::MAX), "9223372036854775807");
        ok(&of_u64(0), "0");
    }
}
