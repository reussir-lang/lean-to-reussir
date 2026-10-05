#!/usr/bin/env python3
"""Issue 11 (cost): write a .rr whose call graph makes MLIR's SCCP superlinear.

    bug11-sccp-call-graph.py N OUT.rr

N self-recursive functions f0..f(N-1) (not inlined) each call the same
function g; `run` calls all of them. rrc runs MLIR's module-level
(interprocedural) SCCP pass, whose data-flow solver revisits a callable's
terminator and its call sites as their states change; with N call sites of
g and N calls in `run` its time grows faster than N^2.

The program prints a number (the same for every compiler). Build time on
Reussir ef922049 (rrc -O aggressive, this machine): N = 1000: 1.6 s,
N = 2000: 6.5 s, N = 4000: 31 s; perf shows the time in
mlir::DataFlowSolver state lookups (DeadCodeAnalysis::visitCallableTerminator,
AbstractSparseForwardDataFlowAnalysis::visitCallableOperation).
"""
import sys

n, out = int(sys.argv[1]), sys.argv[2]
L = ["fn g(x : u64, n : u64) -> u64 { if n == 0 { x } else { g(x * 3 + 1, n - 1) } }"]
L += [f"fn f{i}(x : u64, n : u64) -> u64 {{ if n == 0 {{ g(x + {i}, {i % 7}) }} else {{ f{i}(x + 1, n - 1) }} }}"
      for i in range(n)]
L.append("#[ffi(import)]")
L.append('fn say(x : u64) [{ println!("{}", x) }];')
L.append("#[ffi(import)]")
L.append("fn zero() -> u64 [{ 0 }];")
L.append("fn run(z : u64) -> u64 {")
L.append("    " + " + ".join(f"f{i}(z, {i % 3})" for i in range(n)))
L.append("}")
L.append("#[main]")
L.append("fn main() { say(run(zero()) % 1000003); }")
open(out, "w").write("\n".join(L) + "\n")
