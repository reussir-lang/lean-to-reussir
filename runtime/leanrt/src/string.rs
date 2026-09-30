//! Lean strings: `Rc<Vec<u8>>` holding valid UTF-8 (no terminator).
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

pub type LStr = Rc<Vec<u8>>;

/// `lean_char_default_value`: `'A'`.
pub const DEFAULT_CHAR: u32 = 65;

#[inline]
pub fn from_bytes(b: &[u8]) -> LStr {
    Rc::new(b.to_vec())
}

#[inline]
pub fn from_vec(v: Vec<u8>) -> LStr {
    Rc::new(v)
}

/// `utf8.cpp:push_unicode_scalar` (also used for invalid code points,
/// which it encodes by masking, exactly as C does).
#[inline]
pub fn push_scalar(v: &mut Vec<u8>, code: u32) {
    if code < 0x80 {
        v.push(code as u8);
    } else if code < 0x800 {
        v.push(((code >> 6) & 0x1F) as u8 | 0xC0);
        v.push((code & 0x3F) as u8 | 0x80);
    } else if code < 0x10000 {
        v.push(((code >> 12) & 0x0F) as u8 | 0xE0);
        v.push(((code >> 6) & 0x3F) as u8 | 0x80);
        v.push((code & 0x3F) as u8 | 0x80);
    } else {
        v.push(((code >> 18) & 0x07) as u8 | 0xF0);
        v.push(((code >> 12) & 0x3F) as u8 | 0x80);
        v.push(((code >> 6) & 0x3F) as u8 | 0x80);
        v.push((code & 0x3F) as u8 | 0x80);
    }
}

/// Mutable access for an in-place update; copies (with room for `extra`
/// more bytes) when shared.
#[inline]
fn make_mut(s: &mut LStr, extra: usize) -> &mut Vec<u8> {
    if !s.is_unique() {
        let mut v = Vec::with_capacity((s.len() + extra).max(s.len() * 2));
        v.extend_from_slice(s);
        *s = Rc::new(v);
    }
    unsafe { s.data_mut() }
}

/// `String.push`: an inline fast path for an ASCII character appended to
/// a unique string with spare capacity.
#[inline(always)]
pub fn push(s: LStr, c: u32) -> LStr {
    let mut s = s;
    if c < 0x80 && s.is_unique() {
        let v = unsafe { s.data_mut() };
        if v.len() < v.capacity() {
            v.push(c as u8);
            return s;
        }
    }
    push_slow(s, c)
}

#[inline(never)]
fn push_slow(s: LStr, c: u32) -> LStr {
    let mut s = s;
    push_scalar(make_mut(&mut s, 4), c);
    s
}

#[inline(never)]
pub fn append(a: LStr, b: LStr) -> LStr {
    if b.is_empty() {
        return a;
    }
    let mut a = a;
    make_mut(&mut a, b.len()).extend_from_slice(&b);
    a
}

/// Number of Unicode scalars, counted like `utf8_strlen`: every byte that
/// is not a continuation byte starts a character (for valid UTF-8).
#[inline(never)]
pub fn length(s: &[u8]) -> u64 {
    s.iter().filter(|&&b| (b & 0xC0) != 0x80).count() as u64
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
    let sz = s.len() as u64;
    if b >= e || b >= sz {
        return Rc::new(Vec::new());
    }
    if !is_utf8_first_byte(s[b as usize]) {
        return Rc::new(Vec::new());
    }
    let mut e = e.min(sz);
    if e < sz && !is_utf8_first_byte(s[e as usize]) {
        e = sz;
    }
    if b == 0 && e == sz {
        return s;
    }
    from_bytes(&s[b as usize..e as usize])
}

/// `String.Pos.Raw.set` for a scalar position.
#[inline(never)]
pub fn set(s: LStr, i: u64, c: u32) -> LStr {
    let sz = s.len() as u64;
    if i >= sz {
        return s;
    }
    let i = i as usize;
    let old = s[i];
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
    let mut enc = Vec::with_capacity(4);
    push_scalar(&mut enc, c);
    let mut s = s;
    let v = make_mut(&mut s, 4);
    let end = (i + old_len).min(v.len());
    if end - i == enc.len() {
        v[i..end].copy_from_slice(&enc);
    } else {
        v.splice(i..end, enc);
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
    from_bytes(&buf[i..])
}

/// Decimal representation of a signed word.
#[inline(never)]
pub fn of_i64(n: i64) -> LStr {
    let mut v = Vec::with_capacity(20);
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
    from_vec(v)
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
    let i = skip_chars(&s, 0, n);
    if i == 0 {
        return s;
    }
    from_bytes(&s[i..])
}

/// `String.Internal.dropRight s n`: drop the last `n` characters.
#[inline(never)]
pub fn drop_right(s: LStr, n: u64) -> LStr {
    let mut e = s.len() as u64;
    let mut n = n;
    while n > 0 && e > 0 {
        e = prev(&s, e);
        n -= 1;
    }
    if e == s.len() as u64 {
        return s;
    }
    from_bytes(&s[..e as usize])
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
    let mut enc = Vec::with_capacity(4);
    push_scalar(&mut enc, c);
    let mut s = s;
    let v = make_mut(&mut s, enc.len() * n as usize);
    for _ in 0..n {
        v.extend_from_slice(&enc);
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
    let b = s.iter().position(|&c| !is_ascii_ws(c)).unwrap_or(s.len());
    let e = s.iter().rposition(|&c| !is_ascii_ws(c)).map(|p| p + 1).unwrap_or(b);
    if b == 0 && e == s.len() {
        return s;
    }
    from_bytes(&s[b..e.max(b)])
}

/// `String.Internal.capitalize`: upper-case the first character (ASCII
/// letters only, as `Char.toUpper`).
#[inline(never)]
pub fn capitalize(s: LStr) -> LStr {
    match s.first() {
        Some(&c) if c.is_ascii_lowercase() => {
            let mut s = s;
            make_mut(&mut s, 0)[0] = c.to_ascii_uppercase();
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
