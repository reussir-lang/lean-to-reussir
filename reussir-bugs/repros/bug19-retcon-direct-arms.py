#!/usr/bin/env python3
"""Issue 19 (bug): write a .rr whose drop code is exponential in N
(reussir-lang/reussir#759).

    bug19-retcon-direct-arms.py N OUT.rr

T0 .. T(N-1) are nested enums: T(k) = two(T(k), T(k)) | d0..d3(P, T(k-1))
(T0's direct arms hold P). Each T(k) is recursive through two arms, so its
drop is a retcon destructor; d0..d3 are its direct arms. k0 drops one
T(N-1). Upstream's AcquireDropExpansion drops a direct arm in place at
every drop site, and through it every nested type the same way: the whole
tree of direct-arm drops is unfolded, so the code grows about 4x per
level. Patch 19-a drops the direct arms in one function per type.
Command: rrc OUT.rr --emit mlir-llvm -O none -o OUT.mlir
Expected: about the same growth for each level (linear in N).
Upstream 7954a367 (the issue's measure, lines of the module): N = 3
25,144, N = 4 97,090 (3.9x); N = 5 runs out of memory above 12 GiB
(--emit obj). With 19-a: 6,753 and 9,548 (1.4x); N = 5 in 107 MiB.
"""
import sys

n, out = int(sys.argv[1]), sys.argv[2]
L = ["pub struct P(u64, u64)"]
for k in range(n):
    inner = "P" if k == 0 else f"T{k-1}"
    arms = ", ".join(f"d{i}(P, {inner})" for i in range(4))
    L.append(f"pub enum T{k} {{ two(T{k}, T{k}), {arms} }}")
L.append(f"pub fn k0(x : T{n-1}) -> unit {{ }}")
open(out, "w").write("\n".join(L) + "\n")
