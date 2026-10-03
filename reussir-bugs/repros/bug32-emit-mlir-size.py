#!/usr/bin/env python3
"""Bug 32: write a .rr whose `rrc --emit mlir` output is exponential in K.

    bug32-emit-mlir-size.py K OUT.rr

D0 = struct(u64) and D(i) = struct(D(i-1), D(i-1)): D(K) names 2^K copies
of D0 when every named record's body is printed where it occurs, as
RecordType::print (lib/IR/ReussirTypes.cpp) does, and the MLIR printer has
no type aliases. The program itself is linear in K (it prints 1).
Command: rrc OUT.rr --emit mlir -o OUT.mlir
Expected: an output linear in K. Reussir ef922049: about 2x per level
(K = 8: 0.55 MB, K = 10: 2.2 MB, K = 12: 8.7 MB). Bug 10's generator, which
nests the same records in closure types: K = 16 prints 1.0 GB, in 14 s and
1.06 GB of rrc memory.
"""
import sys

k, out = int(sys.argv[1]), sys.argv[2]
L = ["struct D0(u64)"]
L += [f"struct D{i}(D{i-1}, D{i-1})" for i in range(1, k + 1)]
L.append("fn mk0(x : u64) -> D0 { D0{x} }")
L += [f"fn mk{i}(x : u64) -> D{i} {{ let a = mk{i-1}(x); D{i}{{a, a}} }}" for i in range(1, k + 1)]
L.append(f"fn get(d : D{k}) -> u64 {{ d{'.0' * (k + 1)} }}")
L.append("#[ffi(import)]")
L.append('fn say(x : u64) [{ println!("{}", x) }];')
L.append("#[main]")
L.append(f"fn main() {{ say(get(mk{k}(1))); }}")
open(out, "w").write("\n".join(L) + "\n")
