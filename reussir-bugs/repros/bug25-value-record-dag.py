#!/usr/bin/env python3
"""Bug 25: write a .rr whose copy of a [value] record expands exponentially.

    bug25-value-record-dag.py K OUT.rr

D0 = [value] { s: S, n: u64 } (S a shared box) and D(i) = [value] { a: D(i-1),
b: D(i-1) }: a value of D(K) holds 2^K boxes. `run` uses one D(K) twice, so
rrc copies it once (a retain of every box inside). The first
acquire/drop expansion (AcquireDropExpansion, before ConvertToSTD) writes
that copy out in line, member by member, so the code is exponential in K,
although the program is linear in K. It prints 2 * n.
Command: rrc OUT.rr --emit mlir-llvm -O default
Expected: output and build time about linear in K.
Reussir ef922049 (and with every local patch): about 2x per level (see
25-value-record-dag.md).
"""
import sys

k, out = int(sys.argv[1]), sys.argv[2]
L = ["pub struct [shared] S(u64)", "pub struct [value] D0 { s: S, n: u64 }"]
L += [f"pub struct [value] D{i} {{ a: D{i-1}, b: D{i-1} }}" for i in range(1, k + 1)]
L.append("fn mk0(x : u64) -> D0 { D0 { s: S{x}, n: x } }")
L += [f"fn mk{i}(x : u64) -> D{i} {{ let a = mk{i-1}(x); D{i} {{ a: a, b: a }} }}" for i in range(1, k + 1)]
L.append(f"fn get(d : D{k}) -> u64 {{ d{'.a' * k}.s.0 }}")
L.append("#[ffi(import)]")
L.append('fn say(x : u64) [{ println!("{}", x) }];')
L.append("#[ffi(import)]")
L.append("fn seven() -> u64 [{ std::hint::black_box(7u64) }];")
L.append("#[main]")
L.append(f"fn main() {{ let v = mk{k}(seven()); let x = get(v); say(get(v) + x); }}")
open(out, "w").write("\n".join(L) + "\n")
