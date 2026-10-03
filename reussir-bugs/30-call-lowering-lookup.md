# 30. The call lowering scans the module once per call

## Summary

**Kind:** cost (build time). **Status:** patched (0062).

**Verdict: cost, with a small fix.** `reussir-convert-to-llvm` lowers every
`func.call` with the func dialect's stock pattern, which looks the callee
up by a linear scan of the module, because the pattern list is collected
through the func dialect's `ConvertToLLVMPatternInterface`, which passes no
symbol table. The time is quadratic in a module with many functions and
calls. Upstream's own `convert-func-to-llvm` passes a
`SymbolTableCollection` and avoids it, so the fix is three lines.

## Symptom and repro

Repro [`repros/bug30-call-lowering.py`](repros/bug30-call-lowering.py)
`N OUT.mlir` writes N functions in the func dialect, each calling the
previous one twice (2N calls).

**Command.** `reussir-opt OUT.mlir --reussir-convert-to-llvm` (the
conversion alone; `reussir-opt` is not in the default build target:
`ninja -C build reussir-opt`).

**Expected.** Time about linear in N.

**Actual on ef922049** (the apply list + 0016 + 0017, whose patches do not
touch this code; loaded machine):

| N | conversion | with 0062 |
|---|---|---|
| 5000 | 0.75 s | 0.16 s |
| 10000 | 3.9 s | 0.27 s |
| 20000 | 13.2 s | 0.9 s |

The output is identical with and without the patch. `run.sh` prints
`bug 30   REPRODUCES  reussir-opt --reussir-convert-to-llvm: N = 5000:
1.3 s, N = 10000: 5.2 s (4.00x for twice the calls)` on the unpatched
build.

Inside rrc (`-O none`, perf, a `.rr` of the same shape with N = 10000):
the conversion took about 11e9 cycles, 88% of them in the call lowering's
lookups (`CallOpLowering::matchAndRewrite` →
`SymbolTable::lookupNearestSymbolFrom` → `SymbolTable::lookupSymbolIn`);
with 0062 0.9e9. In that build MLIR's SCCP ([bug 11](11-sccp-call-graph.md))
takes most of the remaining time.

## Cause

`ConvertToLLVMPass::runOnOperation` (`lib/Conversion/BasicOpsLowering/BasicOpsLowering.cpp`)
collects its patterns the way upstream `convert-to-llvm` does:

```c++
for (mlir::Dialect *dialect : context->getLoadedDialects()) {
  if (auto *iface =
          llvm::dyn_cast<mlir::ConvertToLLVMPatternInterface>(dialect))
    iface->populateConvertToLLVMConversionPatterns(target, converter,
                                                   patterns);
}
```

The func dialect's interface (LLVM 23, `FuncToLLVM.cpp`,
`FuncToLLVMDialectInterface`) only calls
`populateFuncToLLVMConversionPatterns(converter, patterns)`, whose third
parameter, `SymbolTableCollection *symbolTables`, defaults to null.
`CallOpLowering` looks up each callee to see whether it carries
`llvm.bareptr`; with no collection it uses
`SymbolTable::lookupNearestSymbolFrom`, which walks the module's operations
until it finds the name. Checked by disassembling `libMLIRFuncToLLVM.a`
(the LLVM 23 build Reussir links): the interface tail-calls
`populateFuncToLLVMConversionPatterns` with a null collection, and
`CallOpLowering::matchAndRewrite` calls the collection's lookup when it has
one and `SymbolTable::lookupNearestSymbolFrom` otherwise.

## lean2rr

Build time only. lean2rr's large outputs have tens of thousands of
functions and calls (the Std.Http program of [bug 23](23-polyffi-link.md):
17,197 functions), so the conversion's cost grows with their product. No
workaround.

## Patch

Patch file
[`patches/0062-l2r-local-bug-30-look-up-call-lowering-s-callees-in-.patch`](patches/0062-l2r-local-bug-30-look-up-call-lowering-s-callees-in-.patch)
(made as commit `33bf4710` in a scratch checkout, after 0060 and 0061; it
does not depend on them). The func dialect's interface is skipped and its
patterns are added with a collection, as `convert-func-to-llvm` does:

```c++
     for (mlir::Dialect *dialect : context->getLoadedDialects()) {
+      if (llvm::isa<mlir::func::FuncDialect>(dialect))
+        continue;
       if (auto *iface = ...)
         iface->populateConvertToLLVMConversionPatterns(target, converter,
                                                        patterns);
     }
+    mlir::SymbolTableCollection symbolTables;
+    mlir::populateFuncToLLVMConversionPatterns(converter, patterns,
+                                               &symbolTables);
```

**Why it is correct.** The interface's hook is exactly that call without
the collection, so the pattern set is the same. With a collection, the
function conversion (`convertFuncOpToLLVMFuncOp`) keeps the table up to
date: it removes each `func.func` from the table and inserts its
`llvm.func`. The call lowering only reads the callee's `llvm.bareptr`
attribute, which the conversion carries over. The collection lives until
the conversion has finished.

**Verification.**

- Identical output for N = 5000, 10000 and 20000 (both through rrc, LLVM
  IR, and through reussir-opt).
- Test `conversion/convert_to_llvm_call_callee_lookup.mlir`: callees
  defined before and after the call, declared, recursive, and a callee
  with `llvm.bareptr`, which keeps its single-pointer convention (so the
  collection finds callees converted before and after the call). It passes
  on both builds (the patch changes time only).
- Reussir's lit suite and lean2rr's runtime tests: as for
  [bug 28](28-unique-carrying-join.md).
- `run.sh`: `bug 30   FIXED       reussir-opt --reussir-convert-to-llvm:
  N = 5000: 0.7 s, N = 10000: 0.4 s`.

**Effect on lean2rr.** Build time only: large programs convert in linear
time; the generated code is unchanged.

## Upstream note

`ConvertToLLVMPass` (`BasicOpsLowering.cpp`) gets the func patterns from
the func dialect's `ConvertToLLVMPatternInterface`, which passes no
`SymbolTableCollection`; `CallOpLowering` then finds each callee by a
linear scan of the module (quadratic: 2N calls among N functions, N =
20000: 13 s). Fix: skip that interface and call
`populateFuncToLLVMConversionPatterns(converter, patterns, &symbolTables)`.
