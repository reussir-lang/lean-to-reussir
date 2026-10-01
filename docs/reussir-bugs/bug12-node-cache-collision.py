#!/usr/bin/env python3
"""Bug 12: write a .rr in which Reussir's parser swaps a syntax subtree.

    bug12-node-cache-collision.py OUT.rr

The parser builds its syntax tree with cstree's GreenNodeBuilder, whose node
cache reuses an earlier node of at most 3 children that has the same kind,
text length and 32-bit hash of its children, without comparing the
children. Token texts enter the hash through interner keys, given out in
order of first occurrence, so the comment lines below only serve to move
the keys of `vvvvvv` and `424242` to two values whose CtorArg nodes collide
(found by a search over the counts). `second`'s argument `T::One{424242}`
is then parsed as `T::One{vvvvvv}`, a variable that is in scope, so the
program compiles with no diagnostic.

Expected output: 424242. Reussir ef922049 prints 7 (second returns its
argument). The file is about 1.9 MB; it must be generated exactly like
this (any change before `second` moves the keys).
"""
import sys

V, S = "vvvvvv", "424242"
lines = [
    "enum T {",
    "    One(u64)",
    "}",
    "",
    "fn get(t: T) -> u64 {",
    "    match t {",
    "        T::One(a) => a",
    "    }",
    "}",
    "",
]
lines += ["// a%d" % i for i in range(149330)]
lines += [f"fn first({V}: u64) -> u64 {{ get(T::One{{{V}}}) }}", ""]
lines += ["// b%d" % i for i in range(38022)]
lines += [
    f"// second(n) returns {S}; with the bug it returns n.",
    f"fn second({V}: u64) -> u64 {{ get(T::One{{{S}}}) }}",
    "",
    "#[ffi(import)]",
    'fn say(x : u64) [{ println!("{}", x) }];',
    "#[main]",
    "fn main() { say(second(7)); }",
    "",
]
open(sys.argv[1], "w").write("\n".join(lines))
