#!/usr/bin/env python3
"""Generate the fixed-width integer section of runtime/prelude.rr.

The section between `// BEGIN GENERATED: scalars` and `// END GENERATED:
scalars` is rewritten in place. Each function is the `static inline`
definition of the same name in lean.h (Lean 4.34; unchanged since 4.33).
Single operations (wrapping `+ - *`, the bitwise operations, negation,
comparisons, casts between widths and to floats) are inline Reussir code; the
rules with logic are lean-runtime's (`sem::uint`, `sem::sint`, `sem::float`,
`sem::float32`, called from textures):

* UIntN/USize: `x / 0 = 0`, `x % 0 = x`, shifts by `b % N`, `log2 0 = 0`,
  saturating float conversions (NaN -> 0).
* IntN/ISize arrive as the unsigned bit pattern (Lean's mono unwraps them):
  signed division truncates, `x / 0 = 0`, `x % 0 = x`, `MIN / -1 = MIN`,
  `MIN % -1 = 0`, shift amounts are taken `smod N` (= the low bits), right
  shifts are arithmetic, `abs MIN = MIN`, float conversions saturate
  (NaN -> 0).

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


def texture(fn, params, ret, call):
    """An `#[ffi(import)]` function whose body is the Rust expression `call`."""
    ps = ", ".join(f"{n} : {t}" for n, t in params)
    return [ "#[ffi(import)]", f"fn {fn}({ps}) -> {ret} [{{ {call} }}];"]


def arg(name, v):
    """An argument as lean-runtime takes it: `usize` for USize and ISize,
    which the prelude holds as `u64`."""
    return f"{v} as usize" if name in ("usize", "isize") else v


def res(name, e):
    """A result of lean-runtime's back in the prelude's type."""
    return f"{e} as u64" if name in ("usize", "isize") else e


def float_convs(name, t, out):
    """`Float.toUIntN`/`toIntN` and the `Float32` ones: lean-runtime's
    saturating conversions."""
    for src, ft, mod in [("float", "f64", "float"), ("float32", "f32", "float32")]:
        out += texture(f"lean_{src}_to_{name}", [("a", ft)], t, res(name, f"sem::{mod}::to_{name}(a)"))


def umax(bits):
    return (1 << bits) - 1


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
    for op in ["div", "mod", "shift_left", "shift_right"]:
        out += texture(f"lean_{name}_{op}", [("a", t), ("b", t)], t,
                       res(name, f"sem::uint::{name}_{op}({arg(name, 'a')}, {arg(name, 'b')})"))
    add(f"fn lean_{name}_complement(a : {t}) -> {t} {{ a ^ {umax(bits)} }}")
    add(f"fn lean_{name}_neg(a : {t}) -> {t} {{ 0 - a }}")
    out += texture(f"lean_{name}_log2", [("a", t)], t, res(name, f"sem::uint::{name}_log2({arg(name, 'a')})"))
    add(f"fn lean_{name}_dec_eq(a : {t}, b : {t}) -> bool {{ a == b }}")
    add(f"fn lean_{name}_dec_lt(a : {t}, b : {t}) -> bool {{ a < b }}")
    add(f"fn lean_{name}_dec_le(a : {t}, b : {t}) -> bool {{ a <= b }}")
    for other, _, ot in UNSIGNED:
        if other != name:
            add(f"fn lean_{name}_to_{other}(a : {t}) -> {ot} {{ a as {ot} }}")
    add(f"fn lean_{name}_to_float(a : {t}) -> f64 {{ a as f64 }}")
    add(f"fn lean_{name}_to_float32(a : {t}) -> f32 {{ a as f32 }}")
    add(f"fn lean_bool_to_{name}(b : bool) -> {t} {{ if b {{ 1 }} else {{ 0 }} }}")
    float_convs(name, t, out)
    add("")
    return out


def signed(name, bits, t, s):
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
    for op in ["div", "mod", "shift_left", "shift_right"]:
        out += texture(f"lean_{name}_{op}", [("a", t), ("b", t)], t,
                       res(name, f"sem::sint::{name}_{op}({arg(name, 'a')}, {arg(name, 'b')})"))
    add(f"fn lean_{name}_complement(a : {t}) -> {t} {{ a ^ {umax(bits)} }}")
    out += texture(f"lean_{name}_abs", [("a", t)], t, res(name, f"sem::sint::{name}_abs({arg(name, 'a')})"))
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
    float_convs(name, t, out)
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
