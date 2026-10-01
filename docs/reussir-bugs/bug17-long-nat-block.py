#!/usr/bin/env python3
"""Bug 17: write a Lean program with a straight-line block of N lets on Nat.

    bug17-long-nat-block.py N OUT.lean [Nat|UInt64]

`longDo` computes x1 .. xN, each from the previous one, and calls itself
three times. `Nat` is a two-arm [value] enum in lean2rr's output (a small
number or a big one). lean2rr cuts long tail paths (bug 17 workaround), but
not in recursive functions, so this body reaches rrc whole. rrc's memory
grows about as N^2 on Nat and stays small on UInt64.

Output: one number, the same as native Lean's. Measured on this machine,
rrc only (Reussir ef922049): N = 250: 21 s, 417 MB; N = 500: 32 s, 1.16 GB;
N = 1000: 57 s, 4.1 GB.
"""
import sys

n, out = int(sys.argv[1]), sys.argv[2]
ty = sys.argv[3] if len(sys.argv) > 3 else "Nat"
L = ["set_option maxRecDepth 200000",
     f"def longDo (x0 : {ty}) : Nat → {ty}",
     "  | 0 => x0",
     "  | k+1 => Id.run do"]
L += [f"    let x{i+1} := (x{i} * 3 + x0) % 1000003" for i in range(n)]
arg = "(args.length + 7)" if ty == "Nat" else "(args.length + 7).toUInt64"
L += [f"    return longDo x{n} k",
      f'def main (args : List String) : IO Unit := IO.println s!"{{longDo {arg} 3}}"']
open(out, "w").write("\n".join(L) + "\n")
