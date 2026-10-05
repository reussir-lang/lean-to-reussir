#!/usr/bin/env python3
"""Issue 10 (cost): write a .rr whose closure result type prints
exponentially large.

    bug10-closure-type-print.py K OUT.rr

D0 = struct(u64) and D(i) = struct(D(i-1), D(i-1)), so D(K) names 2^K copies
of D0 when printed with every named record expanded. Twenty closures of type
`u64 -> D(K)` are chosen at run time and applied through `ap`, so their
calls stay indirect. With -O aggressive, rrc's closure devirtualization
computes a type id for each closure result type by printing the type to a
string, at every vtable and indirect call site; `--no-closure-wpd` skips it.

The program prints 780 in every case. Build time on Reussir ef922049 (rrc,
-O aggressive, this machine): K = 18: 8.4 s (1.3 s with --no-closure-wpd),
K = 20: 24 s (0.8 s). Each 2 more levels multiply the printed text by 4.
"""
import sys

k, out = int(sys.argv[1]), sys.argv[2]
s = 20
L = ["struct D0(u64)"]
L += [f"struct D{i}(D{i-1}, D{i-1})" for i in range(1, k + 1)]
L.append("fn mk0(x : u64) -> D0 { D0{x} }")
L += [f"fn mk{i}(x : u64) -> D{i} {{ let a = mk{i-1}(x); D{i}{{a, a}} }}" for i in range(1, k + 1)]
L.append(f"fn get(d : D{k}) -> u64 {{ d{'.0' * (k + 1)} }}")
L.append(f"fn ap(f : u64 -> D{k}, x : u64) -> u64 {{ get(f(x)) }}")
pick = f"|x : u64| mk{k}(x)"
for j in reversed(range(s)):
    pick = f"if i == {j} {{ |x : u64| mk{k}(x + n + {j}) }} else {{ {pick} }}"
L.append(f"fn pick(i : u64, n : u64) -> u64 -> D{k} {{ {pick} }}")
L.append("fn loop_(i : u64, n : u64, acc : u64) -> u64 { if i == n { acc } else { loop_(i + 1, n, acc + ap(pick(i, n), i)) } }")
L.append("#[ffi(import)]")
L.append('fn say(x : u64) [{ println!("{}", x) }];')
L.append("#[ffi(import)]")
L.append(f"fn count() -> u64 [{{ {s} }}];")
L.append("#[main]")
L.append("fn main() { say(loop_(0, count(), 0)); }")
open(out, "w").write("\n".join(L) + "\n")
