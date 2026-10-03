#!/usr/bin/env python3
"""Generate the fixed-width integer section of runtime/prelude.rr.

The section between `// BEGIN GENERATED: scalars` and `// END GENERATED:
scalars` is rewritten in place. Each function mirrors the `static inline`
definition of the same name in lean.h (Lean 4.34; unchanged since 4.33):

* UIntN/USize: wrapping `+ - *`, `x / 0 = 0`, `x % 0 = x`, shifts by
  `b % N`, `log2 0 = 0`, saturating float conversions (NaN -> 0).
* IntN/ISize arrive as the unsigned bit pattern (Lean's mono unwraps them):
  signed division truncates, `x / 0 = 0`, `x % 0 = x`, `MIN / -1 = MIN`,
  `MIN % -1 = 0`, shift amounts are taken `smod N` (= the low bits), right
  shifts are arithmetic, float conversions saturate (NaN -> 0).

Run: python3 runtime/gen_scalars.py
"""
from pathlib import Path

PRELUDE = Path(__file__).resolve().parent / "prelude.rr"
BEGIN = "// BEGIN GENERATED: scalars (runtime/gen_scalars.py)"
END = "// END GENERATED: scalars"

UNSIGNED = [  # (lean name, bits, reussir type)
    ("uint8", 8, "u8"), ("uint16", 16, "u16"), ("uint32", 32, "u32"),
    ("uint64", 64, "u64"), ("usize", 64, "u64")]
SIGNED = [  # (lean name, bits, storage type, signed type)
    ("int8", 8, "u8", "i8"), ("int16", 16, "u16", "i16"), ("int32", 32, "u32", "i32"),
    ("int64", 64, "u64", "i64"), ("isize", 64, "u64", "i64")]


def umax(bits):
    return (1 << bits) - 1


def fl(x):
    """A float literal for the (possibly negative) integer x."""
    return f"(0.0 - {-x}.0)" if x < 0 else f"{x}.0"


def unsigned(name, bits, t):
    out = [f"// ---- {name} ----", ""]
    add = out.append
    add(f"fn lean_{name}_of_nat(a : Nat) -> {t} {{ l2r_nat_low(a) as {t} }}")
    add(f"fn lean_{name}_of_nat_mk(a : Nat) -> {t} {{ lean_{name}_of_nat(a) }}")
    if bits < 64:
        add(f"fn lean_{name}_to_nat(a : {t}) -> Nat {{ l2r_nat_small(a as u64) }}")
    else:
        add(f"fn lean_{name}_to_nat(a : {t}) -> Nat {{ l2r_nat_of_u64(a) }}")
    for op, e in [("add", "a + b"), ("sub", "a - b"), ("mul", "a * b"),
                  ("land", "a & b"), ("lor", "a | b"), ("xor", "a ^ b")]:
        add(f"fn lean_{name}_{op}(a : {t}, b : {t}) -> {t} {{ {e} }}")
    add(f"fn lean_{name}_div(a : {t}, b : {t}) -> {t} {{ if b == 0 {{ 0 }} else {{ a / b }} }}")
    add(f"fn lean_{name}_mod(a : {t}, b : {t}) -> {t} {{ if b == 0 {{ a }} else {{ a % b }} }}")
    add(f"fn lean_{name}_shift_left(a : {t}, b : {t}) -> {t} {{ a << (b % {bits}) }}")
    add(f"fn lean_{name}_shift_right(a : {t}, b : {t}) -> {t} {{ a >> (b % {bits}) }}")
    add(f"fn lean_{name}_complement(a : {t}) -> {t} {{ a ^ {umax(bits)} }}")
    add(f"fn lean_{name}_neg(a : {t}) -> {t} {{ 0 - a }}")
    add(f"fn lean_{name}_log2(a : {t}) -> {t} {{ if a == 0 {{ 0 }} else {{ {bits - 1} - core::intrinsic::math::ctlz(a) }} }}")
    add(f"fn lean_{name}_dec_eq(a : {t}, b : {t}) -> bool {{ a == b }}")
    add(f"fn lean_{name}_dec_lt(a : {t}, b : {t}) -> bool {{ a < b }}")
    add(f"fn lean_{name}_dec_le(a : {t}, b : {t}) -> bool {{ a <= b }}")
    for other, _, ot in UNSIGNED:
        if other != name:
            add(f"fn lean_{name}_to_{other}(a : {t}) -> {ot} {{ a as {ot} }}")
    add(f"fn lean_{name}_to_float(a : {t}) -> f64 {{ a as f64 }}")
    add(f"fn lean_{name}_to_float32(a : {t}) -> f32 {{ a as f32 }}")
    add(f"fn lean_bool_to_{name}(b : bool) -> {t} {{ if b {{ 1 }} else {{ 0 }} }}")
    for src, ft in [("float", "f64"), ("float32", "f32")]:
        conv = "a" if ft == "f64" else "(a as f64)"
        add(f"fn lean_{src}_to_{name}(a : {ft}) -> {t} {{")
        add(f"    let d : f64 = {conv};")
        add(f"    let hi : f64 = {fl(1 << bits)};")
        add(f"    if 0.0 <= d {{ if d < hi {{ d as {t} }} else {{ {umax(bits)} }} }} else {{ 0 }}")
        add("}")
    add("")
    return out


def signed(name, bits, t, s):
    mn, mx = 1 << (bits - 1), (1 << (bits - 1)) - 1  # MIN as a bit pattern, MAX
    out = [f"// ---- {name} ----", ""]
    add = out.append
    add(f"fn lean_{name}_of_int(a : Int) -> {t} {{ l2r_int_low_twos(a) as {t} }}")
    add(f"fn lean_{name}_of_nat(a : Nat) -> {t} {{ l2r_nat_low(a) as {t} }}")
    to_int = "lean_int64_to_int_sint" if name == "int64" else f"lean_{name}_to_int"
    if bits < 64:
        add(f"fn {to_int}(a : {t}) -> Int {{ l2r_int_small((a as {s}) as i64) }}")
    else:
        add(f"fn {to_int}(a : {t}) -> Int {{ l2r_int_of_i64(a as i64) }}")
    for op, e in [("add", "a + b"), ("sub", "a - b"), ("mul", "a * b"),
                  ("land", "a & b"), ("lor", "a | b"), ("xor", "a ^ b")]:
        add(f"fn lean_{name}_{op}(a : {t}, b : {t}) -> {t} {{ {e} }}")
    add(f"fn lean_{name}_neg(a : {t}) -> {t} {{ 0 - a }}")
    add(f"fn lean_{name}_div(a : {t}, b : {t}) -> {t} {{")
    add(f"    if b == 0 {{ 0 }} else {{ if b == {umax(bits)} {{ 0 - a }} else {{ ((a as {s}) / (b as {s})) as {t} }} }}")
    add("}")
    add(f"fn lean_{name}_mod(a : {t}, b : {t}) -> {t} {{")
    add(f"    if b == 0 {{ a }} else {{ if b == {umax(bits)} {{ 0 }} else {{ ((a as {s}) % (b as {s})) as {t} }} }}")
    add("}")
    add(f"fn lean_{name}_shift_left(a : {t}, b : {t}) -> {t} {{ a << (b & {bits - 1}) }}")
    add(f"fn lean_{name}_shift_right(a : {t}, b : {t}) -> {t} {{ ((a as {s}) >> ((b & {bits - 1}) as {s})) as {t} }}")
    add(f"fn lean_{name}_complement(a : {t}) -> {t} {{ a ^ {umax(bits)} }}")
    add(f"fn lean_{name}_abs(a : {t}) -> {t} {{ if (a as {s}) < 0 {{ 0 - a }} else {{ a }} }}")
    add(f"fn lean_{name}_dec_eq(a : {t}, b : {t}) -> bool {{ a == b }}")
    add(f"fn lean_{name}_dec_lt(a : {t}, b : {t}) -> bool {{ (a as {s}) < (b as {s}) }}")
    add(f"fn lean_{name}_dec_le(a : {t}, b : {t}) -> bool {{ (a as {s}) <= (b as {s}) }}")
    for other, obits, ot, os_ in SIGNED:
        if other == name:
            continue
        if obits >= bits:
            add(f"fn lean_{name}_to_{other}(a : {t}) -> {ot} {{ ((a as {s}) as {os_}) as {ot} }}")
        else:
            add(f"fn lean_{name}_to_{other}(a : {t}) -> {ot} {{ a as {ot} }}")
    add(f"fn lean_{name}_to_float(a : {t}) -> f64 {{ (a as {s}) as f64 }}")
    add(f"fn lean_{name}_to_float32(a : {t}) -> f32 {{ (a as {s}) as f32 }}")
    add(f"fn lean_bool_to_{name}(b : bool) -> {t} {{ if b {{ 1 }} else {{ 0 }} }}")
    for src, ft in [("float", "f64"), ("float32", "f32")]:
        conv = "a" if ft == "f64" else "(a as f64)"
        add(f"fn lean_{src}_to_{name}(a : {ft}) -> {t} {{")
        add(f"    let d : f64 = {conv};")
        add(f"    let lo : f64 = {fl(-(1 << (bits - 1)) - 1)};")
        add(f"    let hi : f64 = {fl(1 << (bits - 1))};")
        add(f"    if d != d {{ 0 }} else {{ if lo < d {{ if d < hi {{ (d as {s}) as {t} }} else {{ {mx} }} }} else {{ {mn} }} }}")
        add("}")
    add("")
    return out


def main():
    lines = [BEGIN, ""]
    for u in UNSIGNED:
        lines += unsigned(*u)
    for s in SIGNED:
        lines += signed(*s)
    lines.append(END)
    text = PRELUDE.read_text()
    start = text.index(BEGIN)
    end = text.index(END) + len(END)
    PRELUDE.write_text(text[:start] + "\n".join(lines) + text[end:])


if __name__ == "__main__":
    main()
