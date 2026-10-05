# 33. The rc and ref type parser drops the text after a comma

## Summary

**Kind:** bug (tooling). **Status:** patched (0064), applied in
`./reussir` (`l2r-local` cc8e5aa5).

**Verdict: bug.** The parser of `!reussir.rc<...>` and `!reussir.ref<...>`
reads `<`, the element type and any capability or atomic-kind keywords, and
returns at the first other token without reading the closing `>`. MLIR
does not check that a dialect type's parser used all of its text, so the
rest is silently dropped: `!reussir.rc<i64 rigid, atomic>` is read as
`!reussir.rc<i64 rigid>`, a different type, with no diagnostic. Every
other Reussir type parser ends at its `>`. It matters only for MLIR written
or edited by hand: Reussir's printer never writes anything after the
keywords.

Found by the review of patch 0061 ([bug 29](29-ffi-member-mlir.md)), as a
side note.

## Symptom and repro

Repro [`repros/bug33-rc-trailing-text.mlir`](repros/bug33-rc-trailing-text.mlir):

```
module {
  func.func private @f() -> !reussir.rc<i64 rigid, atomic>
}
```

**Command.** `rrc bug33-rc-trailing-text.mlir -x mlir --emit mlir -o OUT.mlir`
(or `reussir-opt` on the file).

**Expected.** An error: the type is malformed.

**Actual on ef922049** (and 91da4f80): it succeeds, and `OUT.mlir` declares
`func.func private @f() -> !reussir.rc<i64 rigid>`. Likewise
`!reussir.rc<i64, bogus words here>` reads as `!reussir.rc<i64>`, and
`!reussir.ref<i64, field>` as `!reussir.ref<i64>`. A misspelled keyword
before any comma is caught (`!reussir.rc<i64 garbage>`: "Unknown attribute
in RcType"). `run.sh` prints `issue 33   REPRODUCES  rrc -x mlir reads
!reussir.rc<i64 rigid, atomic> as !reussir.rc<i64 rigid>` on the unpatched
build.

## Cause

`parseTypeWithCapabilityAndAtomicKind` (`lib/IR/ReussirTypes.cpp`), shared
by `RcType::parse` and `RefType::parse`:

```c++
  if (parser.parseLess().failed())
    return {};
  Type eleTy;
  if (parser.parseType(eleTy).failed())
    return {};
  ...
  while (parser.parseOptionalKeyword(&keyword).succeeded()) {
    ... // a capability or an atomic kind, else "Unknown attribute in RcType"
  }
  Capability capValue = capability ? *capability : DefaultCap;
  ...
  return T::getChecked(encLoc, parser.getContext(), eleTy, capValue,
                       atomicValue);
```

There is no `parseGreater()`. MLIR gives a dialect's type parser the text
of the type and does not report text the parser left unread, so a comma
ends the loop and everything from it to the `>` is ignored. The other
custom parsers in the file (records, tokens, cells, rc boxes, closures,
arrays) all read their `>`.

## lean2rr

None: lean2rr never writes MLIR, and rrc's printer never puts anything
after the keywords, so its dumps read back correctly. It would matter to
someone bisecting a pass by hand with an edited dump.

## Patch

Patch file
[`patches/0064-l2r-local-bug-33-end-the-rc-and-ref-types-at-their-c.patch`](patches/0064-l2r-local-bug-33-end-the-rc-and-ref-types-at-their-c.patch)
(`l2r-local` commit `cc8e5aa5`, applied in `./reussir`; `l2r-local` head
cc8e5aa5). The parser reads the closing `>` after the keywords:

```c++
+  // The type ends here: anything else (`!reussir.rc<i64, rigid>`) is an
+  // error, not text to drop.
+  if (parser.parseGreater().failed())
+    return {};
   Capability capValue = capability ? *capability : DefaultCap;
```

**Why it is correct.** The printer writes `<element [capability]
[atomic kind]>`, so every printed type still parses to the same type; only
text that was dropped before is now an error ("expected '>'").

**Verification.** Test `basic/failure/rc_trailing_text.mlir` (three
malformed types, each "expected '>'"; it fails without the patch). The
whole lit suite on the final stack: 647 tests, 566 passed, 81 unsupported,
none failed (every test that prints and reparses rc or ref types passes).
`run.sh`: `issue 33   FIXED       rrc -x mlir rejects !reussir.rc<i64 rigid,
atomic>: expected '>'`.

**Review.** RV8 (e) round 2 (`rv8/reussir/e/round2/FINDINGS.txt`): no
defect. The rc and ref types both go through the changed function, and
rrc's printer always writes the closing `>`; four lean2rr MLIR dumps
(LeanBoolLoop, Rbmap, RtStateMachines, TypeclassGeneric: about 5.3M rc
types) read back and re-print byte-identically.

**Effect on lean2rr.** None.

## Upstream note

`parseTypeWithCapabilityAndAtomicKind` (`lib/IR/ReussirTypes.cpp`, used by
`RcType::parse` and `RefType::parse`) never calls `parseGreater()`, so text
after the keywords is silently ignored: `!reussir.rc<i64 rigid, atomic>`
parses as `!reussir.rc<i64 rigid>`. Fix: `parser.parseGreater()` before
building the type.
