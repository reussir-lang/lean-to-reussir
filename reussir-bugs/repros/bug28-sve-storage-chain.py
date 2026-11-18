#!/usr/bin/env python3
"""bug28-sve-storage-chain.py N: a function of N + 1 blocks in plain MLIR
(std dialects only, no vector) whose region simplification needs about N
rounds. Block k gets two arguments that are equal only once block k - 1
has lost its own redundant arguments, and the last block comes first in
the layout, so each round of the greedy driver clears one level. MLIR's
`arm-sve-legalize-vector-storage` pass runs its patterns with region
simplification and reports the driver's round limit (10) as a failure."""
import sys

n = int(sys.argv[1])
lines = ["func.func @chain(%p: i1, %c: i64) -> i64 {", "  cf.br ^d0(%c, %c : i64, i64)"]
lines.append(f"^d{n}(%v{n}: i64, %w{n}: i64):\n  %r = arith.addi %v{n}, %w{n} : i64\n  return %r : i64")
for k in range(n - 1, -1, -1):
    lines.append(f"^d{k}(%v{k}: i64, %w{k}: i64):\n"
                 f"  cf.cond_br %p, ^d{k+1}(%v{k}, %w{k} : i64, i64), ^d{k+1}(%w{k}, %v{k} : i64, i64)")
lines.append("}")
print("\n".join(lines))
