#!/usr/bin/env python3
"""Bug 16: write a Lean program whose lean2rr output nests N IO matches.

    bug16-nested-io-matches.py N OUT.lean

`loop` runs N `IO.println` statements and calls itself. Every IO bind is a
match on the action's result whose ok arm holds the rest of the function,
so the body nests N matches deep. lean2rr cuts such tail paths into a chain
of functions (bug 16 workaround), but not in recursive functions, so this
one reaches rrc whole. With --reuse-across-call (lean2rr's default) rrc's
memory grows about as N^2.5.

Output: the N lines "line 0" .. "line N-1", once (the program runs loop 1
when called without arguments). Measured on this machine, rrc only (Reussir
ef922049): N = 50: 17 s, 261 MB; N = 100: 35 s, 1.15 GB; N = 150: 3.1 GB
(99 s for the whole build); N = 100 with --no-reuse-across-call: 15 s, 158 MB.
"""
import sys

n, out = int(sys.argv[1]), sys.argv[2]
L = ["set_option maxRecDepth 200000",
     "def loop : Nat → IO Unit",
     "  | 0 => pure ()",
     "  | k+1 => do"]
L += [f'    IO.println "line {i}"' for i in range(n)]
L += ["    loop k",
      "def main (args : List String) : IO Unit := loop (args.length + 1)"]
open(out, "w").write("\n".join(L) + "\n")
