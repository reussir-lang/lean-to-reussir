#!/usr/bin/env python3
"""Generate the `Array Nat` / `Array Int` section of runtime/prelude.rr.

`LNatArr` and `LIntArr` store one tagged word per element
(leanrt::tagvec): small values inline, other values as big-number handles.
For each generic array extern `lean_array_xxx<E>` / primitive
`l2r_array_xxx<E>` the section defines `lean_natarr_xxx` / `l2r_natarr_xxx`
(and `intarr`) with the same arguments, the element type being `Nat`
(`Int`); `lean_mk_array` and `lean_mk_empty_array_with_capacity` become
`lean_mk_natarr` and `lean_mk_empty_natarr_with_capacity`.

Run: python3 runtime/gen_tagarr.py
"""
from pathlib import Path

PRELUDE = Path(__file__).resolve().parent / "prelude.rr"
BEGIN = "// BEGIN GENERATED: tagarr (runtime/gen_tagarr.py)"
END = "// END GENERATED: tagarr"

# kind, array type, element type, codec functions (Reussir source)
CODECS = {
    "nat": ("LNatArr", "Nat", """
// Small values below 2^63 are stored as `(v << 1) | 1`; all others as big
// numbers (normalized back to `Nat::Small` when read, for values below 2^64).
// The array is consumed once (a second use in one branch would make Reussir
// release it out of line in the other): a big word comes back owning a
// reference.
fn l2r_natarr_get(a : LNatArr, i : u64) -> Nat {
    let w = l2r_natarr_word_owned(a, i);
    if (w & 1) == 1 { Nat::Small{w >> 1} } else { l2r_nat_norm(l2r_big_of_owned_word(w)) }
}

fn l2r_natarr_set(a : LNatArr, i : u64, x : Nat) -> LNatArr {
    match x {
        Nat::Small(v) => if (v >> 63) == 0 { l2r_natarr_set_word(a, i, (v << 1) | 1) } else { l2r_natarr_set_big(a, i, l2r_big_of_u64(v)) },
        Nat::Big(b) => l2r_natarr_set_big(a, i, b)
    }
}

fn l2r_natarr_push(a : LNatArr, x : Nat) -> LNatArr {
    match x {
        Nat::Small(v) => if (v >> 63) == 0 { l2r_natarr_push_word(a, (v << 1) | 1) } else { l2r_natarr_push_big(a, l2r_big_of_u64(v)) },
        Nat::Big(b) => l2r_natarr_push_big(a, b)
    }
}

fn l2r_natarr_replicate(n : u64, x : Nat) -> LNatArr {
    match x {
        Nat::Small(v) => if (v >> 63) == 0 { l2r_natarr_replicate_word(n, (v << 1) | 1) } else { l2r_natarr_replicate_big(n, l2r_big_of_u64(v)) },
        Nat::Big(b) => l2r_natarr_replicate_big(n, b)
    }
}
"""),
    "int": ("LIntArr", "Int", """
// Small values in [-2^62, 2^62) are stored as `(v << 1) | 1`; all others as
// big numbers (normalized back to `Int::Small` when read).
fn l2r_int_is_tag_small(v : i64) -> bool { ((v + 4611686018427387904) as u64) < 9223372036854775808 }

fn l2r_intarr_get(a : LIntArr, i : u64) -> Int {
    let w = l2r_intarr_word_owned(a, i);
    if (w & 1) == 1 { Int::Small{(w as i64) >> 1} } else { l2r_int_norm(l2r_big_of_owned_word(w)) }
}

fn l2r_intarr_set(a : LIntArr, i : u64, x : Int) -> LIntArr {
    match x {
        Int::Small(v) => if l2r_int_is_tag_small(v) { l2r_intarr_set_word(a, i, ((v << 1) | 1) as u64) } else { l2r_intarr_set_big(a, i, l2r_big_of_i64(v)) },
        Int::Big(b) => l2r_intarr_set_big(a, i, b)
    }
}

fn l2r_intarr_push(a : LIntArr, x : Int) -> LIntArr {
    match x {
        Int::Small(v) => if l2r_int_is_tag_small(v) { l2r_intarr_push_word(a, ((v << 1) | 1) as u64) } else { l2r_intarr_push_big(a, l2r_big_of_i64(v)) },
        Int::Big(b) => l2r_intarr_push_big(a, b)
    }
}

fn l2r_intarr_replicate(n : u64, x : Int) -> LIntArr {
    match x {
        Int::Small(v) => if l2r_int_is_tag_small(v) { l2r_intarr_replicate_word(n, ((v << 1) | 1) as u64) } else { l2r_intarr_replicate_big(n, l2r_big_of_i64(v)) },
        Int::Big(b) => l2r_intarr_replicate_big(n, b)
    }
}
"""),
}

FFI = """
#[ffi(import)]
fn l2r_{k}arr_empty() -> {T} [{{ leanrt::tagvec::empty() }}];
#[ffi(import)]
fn l2r_{k}arr_with_capacity(n : u64) -> {T} [{{ leanrt::tagvec::with_capacity(n) }}];
#[ffi(import)]
fn l2r_{k}arr_replicate_word(n : u64, w : u64) -> {T} [{{ leanrt::tagvec::replicate_word(n, w) }}];
#[ffi(import)]
fn l2r_{k}arr_replicate_big(n : u64, b : LBig) -> {T} [{{ leanrt::tagvec::replicate_big(n, b) }}];
#[ffi(import)]
fn l2r_{k}arr_size(a : {T}) -> u64 [{{ {{ let r = leanrt::tagvec::size(&a); leanrt::rc_release(a); r }} }}];
#[ffi(import)]
fn l2r_{k}arr_word(a : {T}, i : u64) -> u64 [{{ {{ let r = leanrt::tagvec::word(&a, i); leanrt::rc_release(a); r }} }}];
#[ffi(import)]
fn l2r_{k}arr_big(a : {T}, i : u64) -> LBig [{{ {{ let r = leanrt::tagvec::big(&a, i); leanrt::rc_release(a); r }} }}];
// The word at `i`; a big word owns a reference (see `l2r_big_of_owned_word`).
#[ffi(import)]
fn l2r_{k}arr_word_owned(a : {T}, i : u64) -> u64 [{{ {{ let r = leanrt::tagvec::word_owned(&a, i); leanrt::rc_release(a); r }} }}];
#[ffi(import)]
fn l2r_{k}arr_set_word(a : {T}, i : u64, w : u64) -> {T} [{{ leanrt::tagvec::set_word(a, i, w) }}];
#[ffi(import)]
fn l2r_{k}arr_set_big(a : {T}, i : u64, b : LBig) -> {T} [{{ leanrt::tagvec::set_big(a, i, b) }}];
#[ffi(import)]
fn l2r_{k}arr_push_word(a : {T}, w : u64) -> {T} [{{ leanrt::tagvec::push_word(a, w) }}];
#[ffi(import)]
fn l2r_{k}arr_push_big(a : {T}, b : LBig) -> {T} [{{ leanrt::tagvec::push_big(a, b) }}];
#[ffi(import)]
fn l2r_{k}arr_pop(a : {T}) -> {T} [{{ leanrt::tagvec::pop(a) }}];
#[ffi(import)]
fn l2r_{k}arr_swap(a : {T}, i : u64, j : u64) -> {T} [{{ leanrt::tagvec::swap(a, i, j) }}];
#[ffi(import)]
fn l2r_{k}arr_append(a : {T}, b : {T}) -> {T} [{{ leanrt::tagvec::append(a, b) }}];
#[ffi(import)]
fn l2r_{k}arr_extract(a : {T}, s : u64, e : u64) -> {T} [{{ leanrt::tagvec::extract(a, s, e) }}];
#[ffi(import)]
fn l2r_{k}arr_truncate(a : {T}, n : u64) -> {T} [{{ leanrt::tagvec::truncate(a, n) }}];
#[ffi(import)]
fn l2r_{k}arr_reverse(a : {T}) -> {T} [{{ leanrt::tagvec::reverse(a) }}];
"""

EXTERNS = """
fn lean_mk_empty_{k}arr() -> {T} {{ l2r_{k}arr_empty() }}

fn lean_mk_empty_{k}arr_with_capacity(n : Nat) -> {T} {{
    match n {{
        Nat::Small(c) => if (c >> 63) == 0 {{ l2r_{k}arr_with_capacity(c) }} else {{ l2r_internal_panic_at<{T}>(4) }},
        Nat::Big(_) => l2r_internal_panic_at<{T}>(4)
    }}
}}

fn lean_{k}arr_get_size(v : {T}) -> Nat {{ Nat::Small{{l2r_{k}arr_size(v)}} }}
fn lean_{k}arr_size(v : {T}) -> u64 {{ l2r_{k}arr_size(v) }}
fn lean_{k}arr_fget(v : {T}, i : Nat) -> {E} {{ l2r_{k}arr_get(v, l2r_index_of_nat(i)) }}
fn lean_{k}arr_fget_borrowed(v : {T}, i : Nat) -> {E} {{ l2r_{k}arr_get(v, l2r_index_of_nat(i)) }}
fn lean_{k}arr_uget(v : {T}, i : u64) -> {E} {{ l2r_{k}arr_get(v, i) }}
fn lean_{k}arr_uget_borrowed(v : {T}, i : u64) -> {E} {{ l2r_{k}arr_get(v, i) }}

// `Array.get!Internal`: out of bounds, panic ("index out of bounds") and
// return the default.
fn lean_{k}arr_get(dflt : {E}, v : {T}, i : Nat) -> {E} {{
    if l2r_index_ok(i, l2r_{k}arr_size(v)) {{ l2r_{k}arr_get(v, l2r_index_of_nat(i)) }} else {{
        let ignored = l2r_panic_code(0);
        dflt
    }}
}}

fn lean_{k}arr_get_borrowed(dflt : {E}, v : {T}, i : Nat) -> {E} {{ lean_{k}arr_get(dflt, v, i) }}
fn lean_{k}arr_fset(v : {T}, i : Nat, x : {E}) -> {T} {{ l2r_{k}arr_set(v, l2r_index_of_nat(i), x) }}
fn lean_{k}arr_uset(v : {T}, i : u64, x : {E}) -> {T} {{ l2r_{k}arr_set(v, i, x) }}

// `Array.set!`: out of bounds, panic and return the array unchanged.
fn lean_{k}arr_set(v : {T}, i : Nat, x : {E}) -> {T} {{
    if l2r_index_ok(i, l2r_{k}arr_size(v)) {{ l2r_{k}arr_set(v, l2r_index_of_nat(i), x) }} else {{
        let ignored = l2r_panic_code(0);
        v
    }}
}}

fn lean_{k}arr_push(v : {T}, x : {E}) -> {T} {{ l2r_{k}arr_push(v, x) }}
fn lean_{k}arr_pop(v : {T}) -> {T} {{ l2r_{k}arr_pop(v) }}
fn lean_{k}arr_fswap(v : {T}, i : Nat, j : Nat) -> {T} {{ l2r_{k}arr_swap(v, l2r_index_of_nat(i), l2r_index_of_nat(j)) }}
fn lean_{k}arr_uswap(v : {T}, i : u64, j : u64) -> {T} {{ l2r_{k}arr_swap(v, i, j) }}

// `Array.swapIfInBounds`.
fn lean_{k}arr_swap(v : {T}, i : Nat, j : Nat) -> {T} {{
    let n = l2r_{k}arr_size(v);
    if l2r_index_ok(i, n) && l2r_index_ok(j, n) {{ l2r_{k}arr_swap(v, l2r_index_of_nat(i), l2r_index_of_nat(j)) }} else {{ v }}
}}

// `Array.replicate n x`.
fn lean_mk_{k}arr(n : Nat, x : {E}) -> {T} {{
    match n {{
        Nat::Small(c) => l2r_{k}arr_replicate(c, x),
        Nat::Big(_) => l2r_internal_panic_at<{T}>(4)
    }}
}}

// `Array.toList` glue (see `l2r_array_to_list`).
fn l2r_{k}arr_to_list<L>(a : {T}, nil : L, cons : {E} -> (L -> L)) -> L {{
    l2r_{k}arr_to_list_go(a, l2r_{k}arr_size(a), nil, cons)
}}

fn l2r_{k}arr_to_list_go<L>(a : {T}, i : u64, acc : L, cons : {E} -> (L -> L)) -> L {{
    if i == 0 {{ acc }} else {{ l2r_{k}arr_to_list_go(a, i - 1, cons(l2r_{k}arr_get(a, i - 1))(acc), cons) }}
}}
"""


def main():
    parts = [BEGIN]
    for k, (T, E, codec) in CODECS.items():
        parts.append(f"\n// ---- Array {E} ({T}) ----")
        parts.append(FFI.format(k=k, T=T))
        parts.append(codec)
        parts.append(EXTERNS.format(k=k, T=T, E=E))
    parts.append(END)
    text = PRELUDE.read_text()
    start = text.index(BEGIN)
    end = text.index(END) + len(END)
    PRELUDE.write_text(text[:start] + "\n".join(parts) + text[end:])


if __name__ == "__main__":
    main()
