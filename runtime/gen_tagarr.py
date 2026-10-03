#!/usr/bin/env python3
"""Generate the `Array Nat` / `Array Int` section of runtime/prelude.rr.

`LNatArr` and `LIntArr` store one word per element (leanrt::tagvec): the
element's own word (a small value inline, a big number as its handle).
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
// Elements are `Nat` words (see the Nat section): `lean_box` of a small
// value, an owned reference to a big number otherwise; the handles move in
// and out as their words. The array is consumed once (a second use in one
// branch would make Reussir release it out of line in the other): a big
// word comes back owning a reference.
fn l2r_natarr_get(a : LNatArr, i : u64) -> Nat { l2r_nat_of_raw(l2r_natarr_word_owned(a, i)) }
fn l2r_natarr_set(a : LNatArr, i : u64, x : Nat) -> LNatArr { l2r_natarr_set_word(a, i, l2r_nat_raw(x)) }
fn l2r_natarr_push(a : LNatArr, x : Nat) -> LNatArr { l2r_natarr_push_word(a, l2r_nat_raw(x)) }
fn l2r_natarr_replicate(n : u64, x : Nat) -> LNatArr { l2r_natarr_replicate_word(n, l2r_nat_raw(x)) }
"""),
    "int": ("LIntArr", "Int", """
// Elements are `Int` words (see the Int section), as for `LNatArr`.
fn l2r_intarr_get(a : LIntArr, i : u64) -> Int { l2r_int_of_raw(l2r_intarr_word_owned(a, i)) }
fn l2r_intarr_set(a : LIntArr, i : u64, x : Int) -> LIntArr { l2r_intarr_set_word(a, i, l2r_int_raw(x)) }
fn l2r_intarr_push(a : LIntArr, x : Int) -> LIntArr { l2r_intarr_push_word(a, l2r_int_raw(x)) }
fn l2r_intarr_replicate(n : u64, x : Int) -> LIntArr { l2r_intarr_replicate_word(n, l2r_int_raw(x)) }
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
fn l2r_{k}arr_size(a : {T}) -> u64 [{{ {{ let r = leanrt::tagvec::size(&a); leanrt::rc_release(a); r }} }}];
#[ffi(import)]
fn l2r_{k}arr_word(a : {T}, i : u64) -> u64 [{{ {{ let r = leanrt::tagvec::word(&a, i); leanrt::rc_release(a); r }} }}];
// The word at `i`; a big word owns a reference.
#[ffi(import)]
fn l2r_{k}arr_word_owned(a : {T}, i : u64) -> u64 [{{ {{ let r = leanrt::tagvec::word_owned(&a, i); leanrt::rc_release(a); r }} }}];
#[ffi(import)]
fn l2r_{k}arr_set_word(a : {T}, i : u64, w : u64) -> {T} [{{ leanrt::tagvec::set_word(a, i, w) }}];
#[ffi(import)]
fn l2r_{k}arr_push_word(a : {T}, w : u64) -> {T} [{{ leanrt::tagvec::push_word(a, w) }}];
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
    let w = l2r_nat_raw(n);
    if (w & 1) == 1 {{ l2r_{k}arr_with_capacity(w >> 1) }} else {{ l2r_internal_panic_at<{T}>(4) }}
}}

fn lean_{k}arr_get_size(v : {T}) -> Nat {{ l2r_nat_small(l2r_{k}arr_size(v)) }}
fn lean_{k}arr_size(v : {T}) -> u64 {{ l2r_{k}arr_size(v) }}
fn lean_{k}arr_fget(v : {T}, i : Nat) -> {E} {{ l2r_{k}arr_get(v, l2r_index_of_nat(i)) }}
fn lean_{k}arr_fget_borrowed(v : {T}, i : Nat) -> {E} {{ l2r_{k}arr_get(v, l2r_index_of_nat(i)) }}
fn lean_{k}arr_uget(v : {T}, i : u64) -> {E} {{ l2r_{k}arr_get(v, i) }}
fn lean_{k}arr_uget_borrowed(v : {T}, i : u64) -> {E} {{ l2r_{k}arr_get(v, i) }}

// `Array.get!Internal`: out of bounds, panic ("index out of bounds") and
// return the default.
fn lean_{k}arr_get(dflt : {E}, v : {T}, i : Nat) -> {E} {{
    let w = l2r_nat_raw(i);
    if l2r_word_index_ok(w, l2r_{k}arr_size(v)) {{ l2r_{k}arr_get(v, w >> 1) }} else {{
        let d = l2r_nat_drop_raw(w);
        let ignored = l2r_panic_code(0);
        dflt
    }}
}}

fn lean_{k}arr_get_borrowed(dflt : {E}, v : {T}, i : Nat) -> {E} {{ lean_{k}arr_get(dflt, v, i) }}
fn lean_{k}arr_fset(v : {T}, i : Nat, x : {E}) -> {T} {{ l2r_{k}arr_set(v, l2r_index_of_nat(i), x) }}
fn lean_{k}arr_uset(v : {T}, i : u64, x : {E}) -> {T} {{ l2r_{k}arr_set(v, i, x) }}

// `Array.set!`: out of bounds, panic and return the array unchanged.
fn lean_{k}arr_set(v : {T}, i : Nat, x : {E}) -> {T} {{
    let w = l2r_nat_raw(i);
    if l2r_word_index_ok(w, l2r_{k}arr_size(v)) {{ l2r_{k}arr_set(v, w >> 1, x) }} else {{
        let d = l2r_nat_drop_raw(w);
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
    let x = l2r_nat_raw(i);
    let y = l2r_nat_raw(j);
    if l2r_word_index_ok(x, n) && l2r_word_index_ok(y, n) {{ l2r_{k}arr_swap(v, x >> 1, y >> 1) }} else {{
        let d = l2r_nat_drop_raw(x) + l2r_nat_drop_raw(y);
        v
    }}
}}

// `Array.replicate n x`.
fn lean_mk_{k}arr(n : Nat, x : {E}) -> {T} {{
    let w = l2r_nat_raw(n);
    if (w & 1) == 1 {{ l2r_{k}arr_replicate(w >> 1, x) }} else {{ l2r_internal_panic_at<{T}>(4) }}
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
