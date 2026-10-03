#!/usr/bin/env python3
"""Bug 31: write a .rr with deeply nested expressions; rrc overflows its stack.

    bug31-deep-expression.py N DEPTH OUT.rr

`chain` adds N calls (a left-nested `+` tree N deep, the shape of bug 11's
generator at large N) and `parens` wraps a literal in DEPTH parentheses.
The parser grows its own stack, but the elaborator (Elaborator::infer_expr
and infer_binop, crates/reussir-core/src/semi/check.rs) recursed on the
8 MiB main thread, about 1 KiB per level. The program prints
N * 1 + N * (N - 1) / 2 + 7.
Expected (N = 8000, DEPTH = 100000): compiles, prints 32004007.
Reussir ef922049: rrc aborts, "thread 'main' has overflowed its stack"
(each shape alone does it; N = 4000 still builds).
"""
import sys

n, d, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
lines = [
    "#[ffi(import)]",
    'fn say(x : u64) [{ println!("{}", x) }];',
    "#[ffi(import)]",
    "fn one() -> u64 [{ std::hint::black_box(1u64) }];",
    "fn f(x : u64, i : u64) -> u64 { x + i }",
    "fn chain(z : u64) -> u64 {",
    "    " + " + ".join(f"f(z, {i})" for i in range(n)),
    "}",
    "fn parens() -> u64 { " + "(" * d + "7" + ")" * d + " }",
    "#[main]",
    "fn main() { say(chain(one()) + parens()); }",
]
open(out, "w").write("\n".join(lines) + "\n")
