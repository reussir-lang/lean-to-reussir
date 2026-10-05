#!/usr/bin/env python3
"""Issue 23 (cost): write a .rr with K distinct instances of a polymorphic
FFI import.

    bug23-polyffi-link.py K OUT.rr [heavy|light]

`id<T>` is instantiated at K distinct shared record types S0..S{K-1}. rrc
compiles one Rust texture per instance (one rustc process each) and then, in
`gatherCompiledModules` (lib/IR/ReussirOps.cpp), links the K bitcode modules
into one. ef922049 links them with one `llvm::Linker::linkModules` call each;
each call builds a new `llvm::IRMover`, whose constructor walks every type and
metadata node of the destination module linked so far, so the link phase is
quadratic in K. `heavy` (the default) makes each instance carry its own copy
of the generic `HashMap` code (about 48 KB of bitcode, like lean2rr's
`l2r_origin_note` instances); `light` returns the argument (a tiny module,
where the rustc processes dominate and the quadratic term stays small).

The program prints K*(K-1)/2 (the same for every compiler).

Link times on Reussir ef922049 (measured on l2r-local + 0016, which do not
touch this code), `rrc OUT.rr --emit executable -O aggressive`, heavy, on
the loaded test machine. The texture compiles are linear (about 0.1 s per
instance) and come first; the link is the part that grows:

    K      link    with 0017    whole build   with 0017
    300     4.0 s    0.3 s
    600    22.8 s    0.5 s
    1000   56 s      0.9 s        260 s         162 s
    2000  339 s      1.9 s        706 s         341 s

(link = from the exit of the last texture's rustc, logged by a rustc
wrapper, to "running the MLIR lowering pipeline" in `rrc -v`; run.sh's
bug23 does this for K = 300 and 600.) perf on a lean2rr program in the
same phase: 97% of the time in `llvm::IRMover::IRMover`, called from
`Linker::linkModules`.
"""
import sys

k, out = int(sys.argv[1]), sys.argv[2]
heavy = len(sys.argv) < 4 or sys.argv[3] != "light"
body = ("{ let mut m = ::std::collections::HashMap::new(); m.insert(1u64, x); "
        "m.remove(&1u64).unwrap() }") if heavy else "x"
L = [f"struct S{i} {{ v : u64 }}" for i in range(k)]
L.append("#[ffi(import)]")
L.append(f"fn id<T>(x : T) -> T [{{ {body} }}];")
L.append("#[ffi(import)]")
L.append('fn say(x : u64) [{ println!("{}", x) }];')
L += [f"fn f{i}(n : u64) -> u64 {{ let s = id(S{i} {{ v : n }}); s.v }}" for i in range(k)]
L.append("fn run() -> u64 {")
L.append("    let acc = 0;")
L += [f"    let acc = acc + f{i}({i});" for i in range(k)]
L.append("    acc")
L.append("}")
L.append("#[main]")
L.append("fn main() { say(run()); }")
open(out, "w").write("\n".join(L) + "\n")
