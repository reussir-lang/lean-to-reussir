//! Lean strings: `Rc<(Vec<u8>, u64)>`: valid UTF-8 bytes (no terminator)
//! and the number of characters, Lean's `m_length`, kept up to date by every
//! function that builds or changes a string, so that `String.length` is a
//! field read as natively.
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

use reussir_rt::rc::Rc;
use crate::alloc::{rc_new, reserve, vec_from_slice, vec_with_capacity};

/// The Reussir-visible type (spelled with std and reussir_rt types only, as
/// opaque FFI types must be): the bytes and the character count. The
/// count is only written while the string is unique.
pub type LStr = Rc<(Vec<u8>, u64)>;

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
        &self.0
    }
}

/// The bytes of a string.
#[inline(always)]
pub fn bytes(s: &LStr) -> &[u8] {
    &s.0
}

/// `lean_char_default_value`: `'A'`.
pub const DEFAULT_CHAR: u32 = 65;

/// A string from bytes and their character count (`utf8_count(&v)`).
#[inline(always)]
pub fn from_parts(v: Vec<u8>, chars: u64) -> LStr {
    debug_assert_eq!(chars, utf8_count(&v));
    rc_new((v, chars))
}

#[inline]
pub fn from_bytes(b: &[u8]) -> LStr {
    from_parts(vec_from_slice(b, 0), utf8_count(b))
}

#[inline]
pub fn from_vec(v: Vec<u8>) -> LStr {
    let n = utf8_count(&v);
    from_parts(v, n)
}

/// The bytes of a string as a vector: moved out when the string is unique.
#[inline]
pub fn into_vec(s: LStr) -> Vec<u8> {
    if s.is_unique() {
        unsafe { crate::alloc::rc_into_inner(s) }.0
    } else {
        let v = vec_from_slice(&s.0, 0);
        crate::rc_release(s);
        v
    }
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

/// Mutable access for an in-place update; copies (with room for `extra`
/// more bytes) when shared.
#[inline]
fn make_mut(s: &mut LStr, extra: usize) -> &mut (Vec<u8>, u64) {
    if !s.is_unique() {
        // By value: the address of `s` must not escape (see array::make_mut).
        unsafe { std::ptr::write(s, copy_shared(std::ptr::read(s), extra)) };
    }
    let d = unsafe { s.data_mut() };
    reserve(&mut d.0, extra);
    d
}

/// A private copy of a shared string (with room for `extra` more bytes, at
/// least doubling as `lean_string_push` does), releasing the shared one.
#[cold]
#[inline(never)]
extern "C" fn copy_shared(s: LStr, extra: usize) -> LStr {
    let c = rc_new((vec_from_slice(&s.0, extra.max(s.0.len())), s.1));
    crate::rc_release(s);
    c
}

/// `String.push`: an inline fast path for an ASCII character appended to
/// a unique string with spare capacity.
#[inline(always)]
pub fn push(s: LStr, c: u32) -> LStr {
    let mut s = s;
    if c < 0x80 && s.is_unique() {
        let d = unsafe { s.data_mut() };
        if d.0.len() < d.0.capacity() {
            d.0.push(c as u8);
            d.1 += 1;
            return s;
        }
    }
    push_slow(s, c)
}

#[inline(never)]
fn push_slow(s: LStr, c: u32) -> LStr {
    let mut s = s;
    let d = make_mut(&mut s, 4);
    push_scalar(&mut d.0, c);
    d.1 += 1;
    s
}

#[inline(always)]
pub fn append(a: LStr, b: LStr) -> LStr {
    let mut a = a;
    if a.is_unique() {
        let d = unsafe { a.data_mut() };
        if d.0.len() + b.0.len() <= d.0.capacity() {
            d.0.extend_from_slice(&b.0);
            d.1 += b.1;
            crate::rc_release(b);
            return a;
        }
    }
    append_slow(a, b)
}

#[inline(never)]
fn append_slow(a: LStr, b: LStr) -> LStr {
    if b.0.is_empty() {
        crate::rc_release(b);
        return a;
    }
    let mut a = a;
    let d = make_mut(&mut a, b.0.len());
    d.0.extend_from_slice(&b.0);
    d.1 += b.1;
    crate::rc_release(b);
    a
}

/// `String.length`: the character count.
#[inline(always)]
pub fn length(s: &LStr) -> u64 {
    s.1
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
    let sz = s.0.len() as u64;
    if b >= e || b >= sz || !is_utf8_first_byte(s.0[b as usize]) {
        crate::rc_release(s);
        return from_parts(Vec::new(), 0);
    }
    let mut e = e.min(sz);
    if e < sz && !is_utf8_first_byte(s.0[e as usize]) {
        e = sz;
    }
    if b == 0 && e == sz {
        return s;
    }
    let r = from_bytes(&s.0[b as usize..e as usize]);
    crate::rc_release(s);
    r
}

/// `String.Pos.Raw.set` for a scalar position. The fast path (natively
/// too) overwrites an ASCII character of a unique string with an ASCII
/// character. One character replaces one: the count does not change.
#[inline(always)]
pub fn set(s: LStr, i: u64, c: u32) -> LStr {
    let mut s = s;
    if c < 0x80 && s.is_unique() {
        let d = unsafe { s.data_mut() };
        if let Some(b) = d.0.get_mut(i as usize) {
            if *b < 0x80 {
                *b = c as u8;
                return s;
            }
        }
    }
    set_slow(s, i, c)
}

#[inline(never)]
fn set_slow(s: LStr, i: u64, c: u32) -> LStr {
    let sz = s.0.len() as u64;
    if i >= sz {
        return s;
    }
    let i = i as usize;
    let old = s.0[i];
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
    let mut s = s;
    let d = make_mut(&mut s, n.saturating_sub(old_len));
    let v = &mut d.0;
    let len = v.len();
    let end = (i + old_len).min(len);
    let old_n = end - i;
    if n != old_n {
        if n > old_n {
            // Room was reserved by `make_mut`.
            v.resize(len + (n - old_n), 0);
        }
        v.copy_within(end..len, i + n);
        if n < old_n {
            v.truncate(len - (old_n - n));
        }
    }
    v[i..i + n].copy_from_slice(&enc[..n]);
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
    from_parts(vec_from_slice(b, 0), b.len() as u64)
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
    let mut v = vec_with_capacity(20);
    if n < 0 {
        v.push(b'-');
    }
    let mut buf = [0u8; 20];
    let mut i = 20;
    let mut m = n.unsigned_abs();
    loop {
        i -= 1;
        buf[i] = b'0' + (m % 10) as u8;
        m /= 10;
        if m == 0 {
            break;
        }
    }
    v.extend_from_slice(&buf[i..]);
    let k = v.len() as u64;
    from_parts(v, k)
}

struct Global<T>(std::cell::UnsafeCell<T>);
unsafe impl<T> Sync for Global<T> {}

/// The strings of `Nat.reprArray` (natively a closed term, built at
/// initialization): `Nat.repr n` for `n < 128` returns the same string
/// every time, so it is shared and costs no allocation. Built on first use;
/// the table keeps one reference to each (the runtime is single-threaded).
static SMALL_REPR: Global<[usize; 128]> = Global(std::cell::UnsafeCell::new([0; 128]));

/// `Nat.repr n` for `n < 128`: the shared string.
#[inline(always)]
pub fn repr_small(n: u64) -> LStr {
    let p = match unsafe { (*SMALL_REPR.0.get()).get(n as usize) } {
        Some(&p) if p != 0 => p,
        _ => return repr_small_init(n),
    };
    // A new reference to the table's string (`Rc` is a transparent pointer).
    let r = std::mem::ManuallyDrop::new(unsafe { std::mem::transmute::<usize, LStr>(p) });
    LStr::clone(&r)
}

#[cold]
#[inline(never)]
extern "C" fn repr_small_init(n: u64) -> LStr {
    if n >= 128 {
        return of_u64(n);
    }
    let s = of_u64(n);
    let p = unsafe { std::mem::transmute::<LStr, usize>(s.clone()) };
    unsafe { (*SMALL_REPR.0.get())[n as usize] = p };
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
    let i = skip_chars(&s.0, 0, n);
    if i == 0 {
        return s;
    }
    let r = from_bytes(&s.0[i..]);
    crate::rc_release(s);
    r
}

/// `String.Internal.dropRight s n`: drop the last `n` characters.
#[inline(never)]
pub fn drop_right(s: LStr, n: u64) -> LStr {
    let mut e = s.0.len() as u64;
    let mut n = n;
    while n > 0 && e > 0 {
        e = prev(&s.0, e);
        n -= 1;
    }
    if e == s.0.len() as u64 {
        return s;
    }
    let r = from_bytes(&s.0[..e as usize]);
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
    let mut s = s;
    let d = make_mut(&mut s, k * n as usize);
    for _ in 0..n {
        d.0.extend_from_slice(&enc[..k]);
    }
    d.1 += n;
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
    let v = &s.0;
    let b = v.iter().position(|&c| !is_ascii_ws(c)).unwrap_or(v.len());
    let e = v.iter().rposition(|&c| !is_ascii_ws(c)).map(|p| p + 1).unwrap_or(b);
    if b == 0 && e == v.len() {
        return s;
    }
    // Only ASCII whitespace (one byte, one character each) is removed.
    let r = from_parts(vec_from_slice(&v[b..e.max(b)], 0), s.1 - (v.len() - (e.max(b) - b)) as u64);
    crate::rc_release(s);
    r
}

/// `String.Internal.capitalize`: upper-case the first character (ASCII
/// letters only, as `Char.toUpper`).
#[inline(never)]
pub fn capitalize(s: LStr) -> LStr {
    match s.0.first() {
        Some(&c) if c.is_ascii_lowercase() => {
            let mut s = s;
            make_mut(&mut s, 0).0[0] = c.to_ascii_uppercase();
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
        let v2 = crate::array::bytes_of_string(back); // unique: moved
        ok(&crate::array::string_of_bytes(v2), "é€");
    }
}
