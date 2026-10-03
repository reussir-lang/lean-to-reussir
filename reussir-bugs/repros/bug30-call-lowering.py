#!/usr/bin/env python3
"""Bug 30: write an MLIR module whose call lowering scans the module per call.

    bug30-call-lowering.py N OUT.mlir

N functions f0..f(N-1) in the func dialect; each f(i) calls f(i-1) twice
(2N calls). `reussir-opt OUT.mlir --reussir-convert-to-llvm` lowers them to
the LLVM dialect. The func dialect's call lowering looked each callee up
with a linear scan of the module, so the conversion took time quadratic in
N. On Reussir ef922049 + the ten-patch list + 0016/0017 (this machine,
loaded): N = 5000: 0.75 s, N = 10000: 3.9 s, N = 20000: 13.2 s; with
patch 0062: 0.16 s, 0.27 s, 0.9 s (see 30-call-lowering-lookup.md).
"""
import sys

n, out = int(sys.argv[1]), sys.argv[2]
L = ["module {", "  func.func @f0(%x: i64) -> i64 { return %x : i64 }"]
for i in range(1, n):
    L.append(f"  func.func @f{i}(%x: i64) -> i64 {{")
    L.append(f"    %a = func.call @f{i-1}(%x) : (i64) -> i64")
    L.append(f"    %b = func.call @f{i-1}(%a) : (i64) -> i64")
    L.append("    return %b : i64")
    L.append("  }")
L.append("}")
open(out, "w").write("\n".join(L) + "\n")
