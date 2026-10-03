#!/usr/bin/env python3
"""Bug 22: write a .rr whose wildcard arms over a wide enum cost N^3 code.

    bug22-wildcard-wide-enum.py N OUT.rr [wild|sink|false]

The Reussir analogue of a derived BEq on a recursive inductive with N
constructors, shaped as lean2rr emitted it before its workaround: a
constructor-index test, then a match on `a` whose arm i matches `b` against
c_i with a `_ => unreach()` default. The pattern compiler copies each
wildcard arm into every constructor it covers (N - 1 copies), and each copy
releases the held fields of the enum's type in line, as a match over its N
variants: N^3 code. Modes:
  wild   (default) the wildcard arm only panics, as described;
  sink   the wildcard arm first passes each held field of a recursive type
         to `sink`, a #[transform_anchor] function (lean2rr's workaround,
         l2r_sink: the releases happen out of line);
  false  the wildcard arm returns false instead of panicking.

The program prints 100 in every mode. Build time on Reussir ef922049 (rrc
-O aggressive, wild, this machine): N = 10: 1.2 s, 20: 9.3 s, 30: 65 s,
40: 444 s.
"""
import sys
n, out = int(sys.argv[1]), sys.argv[2]
mode = sys.argv[3] if len(sys.argv) > 3 else "wild"
shapes = ["u64", "u64, E", "E, E", "L, i64", "f64, O"]
L = []
L.append("enum L { nil, cons(E, L) }")
L.append("enum O { none, some(E) }")
L.append("enum E {")
L.append(",\n".join(f"    c{i}({shapes[i % 5]})" for i in range(n)))
L.append("}")
L.append("fn unreach<T>() -> T { core::intrinsic::panic::panic<T>() }")
L.append("#[transform_anchor]\nfn sink<T>(x : T) -> u64 { 0 }")
def pats(i, p):
    k = shapes[i % 5].count(",") + 1
    return ", ".join(f"{p}{j}" for j in range(k))
L.append("fn idx(a : E) -> u64 {\n    match a {")
L.append(",\n".join(f"        E::c{i}({pats(i, 'x')}) => {{ {i} }}" for i in range(n)))
L.append("    }\n}")
L.append("""fn obeq(a : O, b : O) -> bool {
    match a {
        O::none => { match b { O::none => { true }, O::some(y) => { false } } },
        O::some(x) => { match b { O::none => { false }, O::some(y) => { beq(x, y) } } }
    }
}
fn lbeq(a : L, b : L) -> bool {
    match a {
        L::nil => { match b { L::nil => { true }, L::cons(y, ys) => { false } } },
        L::cons(x, xs) => { match b { L::nil => { false }, L::cons(y, ys) => { if beq(x, y) { lbeq(xs, ys) } else { false } } } }
    }
}""")
def body(i):
    s = i % 5
    if s == 0: return "x0 == y0"
    if s == 1: return "if x0 == y0 { beq(x1, y1) } else { false }"
    if s == 2: return "if beq(x0, y0) { beq(x1, y1) } else { false }"
    if s == 3: return "if lbeq(x0, y0) { x1 == y1 } else { false }"
    if s == 4: return "if x0 == y0 { obeq(x1, y1) } else { false }"
L.append("fn beq(a : E, b : E) -> bool {")
L.append("    let i : u64 = idx(a);\n    let j : u64 = idx(b);\n    if i == j {\n        match a {")
arms = []
for i in range(n):
    if mode == "wild":
        inner = f"match b {{ E::c{i}({pats(i, 'y')}) => {{ {body(i)} }}, _ => {{ unreach<bool>() }} }}"
    elif mode == "sink":
        k = shapes[i % 5].split(", ")
        sinks = "".join(f"let s{j} : u64 = sink<{t}>(x{j}); " for j, t in enumerate(k) if t in ("E", "L", "O"))
        inner = f"match b {{ E::c{i}({pats(i, 'y')}) => {{ {body(i)} }}, _ => {{ {sinks}unreach<bool>() }} }}"
    elif mode == "false":
        inner = f"match b {{ E::c{i}({pats(i, 'y')}) => {{ {body(i)} }}, _ => {{ false }} }}"
    arms.append(f"            E::c{i}({pats(i, 'x')}) => {{ {inner} }}")
L.append(",\n".join(arms))
L.append("        }\n    } else { false }\n}")
L.append("""fn mk(n : u64) -> E {
    if n == 0 { E::c0{1} } else { E::c2{mk(n - 1), E::c1{7, E::c0{n}}} }
}
#[ffi(import)]
fn say(x : u64) [{ println!("{}", x) }];
#[ffi(import)]
fn five() -> u64 [{ 5 }];
fn b2u(b : bool) -> u64 { if b { 1 } else { 0 } }
#[main]
fn main() { say(b2u(beq(mk(five()), mk(five()))) * 100 + b2u(beq(mk(five()), mk(4))) * 10 + b2u(beq(E::c0{1}, E::c1{1, E::c0{1}}))); }""")
open(out, "w").write("\n".join(L) + "\n")
