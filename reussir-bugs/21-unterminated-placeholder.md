# 21. An unterminated `[:` in a polymorphic FFI texture is dropped

## Summary

**Kind:** bug. **Status:** patched (21-a), applied in `./reussir` (`l2r-local` cc8e5aa5); lean2rr also works around it
(it escapes `[` in its string literal table).

**Verdict: bug.** Reussir has two implementations of placeholder
substitution in texture bodies, and they disagree: the Rust one
(`substitute_placeholders`, `crates/reussir-core/src/full/ffi.rs`) keeps a
`[:` that has no closing `:]`; the C++ one used to compile textures drops
it, changing the Rust code handed to rustc.

The Rust body of an `#[ffi(import)]` function (a "texture") may contain
placeholders `[:Name:]`, which rrc replaces with the function's type or
value arguments before handing the body to rustc. The C++ code that does
the replacement treated every `[:` as the start of a placeholder. When no
`:]` followed, it dropped the `[:`, and it did not look for any later `[:`
either. Patch 21-a makes the C++ code keep such a `[:` as written, as the
Rust implementation does.

## Symptom and repro

Repro [`repros/bug21-unterminated-placeholder.rr`](repros/bug21-unterminated-placeholder.rr):

```
#[ffi(import)]
fn say(x : u64) [{ println!("{}", x) }];
#[ffi(import)]
fn unterminated_len() -> u64 [{ b"a[:b".len() as u64 }];
#[main]
fn main() { say(unterminated_len()); }
```

In Lean (found by round-6 testing, `adv6/stdlib/M03Bracket.lean`):

```
def main : IO Unit := IO.println "slice a[:3] and b[:4]"
```

**Command.** `rrc bug21-unterminated-placeholder.rr -O aggressive`.

**Expected.** `4` (the byte string `a[:b` has four bytes). Lean: `slice
a[:3] and b[:4]`, as native Lean prints.

**Actual on ef922049.** `2`: rustc was given `b"ab"`. Lean through
lean2rr (before its escape, below): `slice a3] and b[:4]`: the first `[:`,
with no `:]` anywhere after it, loses its two characters, and the second
survives only because the scan never looked at it. `run.sh` prints
`issue 21   REPRODUCES` on the unpatched build.

## Cause

Where it runs: in rrc, `LlvmLowering::prepare`
(`crates/reussir-backend/src/llvm.rs`, called by `backend_module` in
`crates/reussir-compiler/src/driver/backend.rs` before the MLIR lowering
pipeline) calls `compilePolymorphicFFI`, which renders each texture with
`monomorphize` and compiles it with rustc; the pipeline's
`CompilePolymorphicFFI` pass later finds nothing left to compile. The Rust
frontend has already substituted the `[:T:]` placeholders
(`substitute_placeholders`, `crates/reussir-core/src/full/ffi.rs`), and
codegen emits `reussir.polyffi` with the texture only, never a
`substitutions` attribute. So the C++ scan re-reads text that is already
final, and its only possible effect is to drop an unterminated `[:`.

`monomorphize`
(`lib/Conversion/CompilePolymorphicFFI/CompilePolymorphicFFI.cpp`) scans
the body with a cursor and a flag:

```c++
while (index < text.size()) {
  if (!inSubstitution) {
    if (text.substr(index, 2) != SUBSTART) { index++; continue; }
    inSubstitution = true;
    os << text.substr(cursor, index - cursor);   // text before the `[:`
    index += 2;
    cursor = index;                              // cursor is past the `[:`
  } else {
    if (text.substr(index, 2) != SUBEND) { index++; continue; }
    ... look up the key, write the substitution (or `[:key:]` if unknown) ...
  }
}
os << text.substr(cursor);                       // the rest
```

On a `[:` it writes the text before it, moves its cursor past the `[:` and
looks for `:]`. If the body ends before any `:]`, the loop ends with
`inSubstitution` still set, and the last line writes only
`text.substr(cursor)`, the text after the `[:`. The two characters are
gone.

The Rust implementation (`substitute_placeholders`,
`crates/reussir-core/src/full/ffi.rs`) copies an unterminated `[:` and the
rest of the body unchanged. So the two implementations disagree, and the
C++ one changes what the program means.

Why lean2rr hits it: lean2rr's string literals live in a single texture
body. `l2r_str_lit(id)` holds a table of Rust byte strings
(`LowerBase.strLitTable`), and printable ASCII is written as it is. So a
`[:` in any Lean string literal, with no `:]` anywhere after it in the
table, was dropped: any literal could be the one.

## lean2rr

Without the fix, a Lean program printing a string with `[:` (a Python or Go
slice in a message, an IPv6 address like `[::1]`) printed it wrong, and
string operations on such literals gave wrong results (`"a[:b".replace
"[:" "<>"` with the pattern literal emptied). It was not limited to one
literal: the first `[:` in the whole table was dropped whenever no `:]`
followed it anywhere in the table.

lean2rr now writes `[` as `\x5b` in the literal table, so no literal can
contain placeholder syntax, with or without the patch (round-6 review,
RV6L-01). The patch fixes the cause in Reussir, for any other texture with
such a `[:`: every `[:` in lean2rr's prelude starts a closed placeholder,
so lean2rr itself no longer depends on it.

## Patch

Patch file
[`patches/21-a-unterminated-placeholder.patch`](patches/21-a-unterminated-placeholder.patch)
(`l2r-local` commit `17657841`, applied in `./reussir`; `l2r-local` head cc8e5aa5). Write the pending `[:`
before the rest of the body, as the Rust implementation does:

```c++
   }
+  // A `[:` without a closing `:]` is not a placeholder: keep it as written
+  // (as `substitute_placeholders` in crates/reussir-core/src/full/ffi.rs
+  // does), instead of dropping it with the text that follows.
+  if (inSubstitution)
+    os << SUBSTART;
   os << text.substr(cursor);
   return buffer;
```

**Why it is correct.** When the loop ends with `inSubstitution` set, the
output holds everything before the last unmatched `[:`, and `cursor` is
just after it. Writing `[:` and then `text.substr(cursor)` writes the body
from that `[:` to the end, so the output is the input with only the
complete placeholders replaced. A later `[:` inside that tail cannot be a
placeholder either: a placeholder needs a `:]`, and none follows. Bodies
in which every `[:` is closed take the old path unchanged.

**Verification.**

- New Reussir test
  `tests/integration/frontend/ffi_unterminated_placeholder_e2e` (`.rr` and
  `.c`): `b"a[:b".len()` (4), and a texture whose `[:` is closed by a `:]`
  in a later byte string (`b"x[:y"`, `b"z:]"`: an unknown key, kept as
  written, 4 * 10 + 3 = 43). The driver checks for 443. It exits 0 with
  the patch and 1 without it.
- `run.sh`: `issue 21 FIXED` on the patched build (prints 4).
- lean2rr's runtime test `tests/runtime/RtStrLitBracket.lean`: literals
  with `[:` and with `[::`, `[:` built by interpolation, `splitOn "[:"`,
  `replace "[:" "<>"`. Its output equals native Lean's (it passes with or
  without the patch, thanks to lean2rr's escape of `[`).
- Round-6 review (RV6L-01) traced the C++ scan and found the patch correct:
  with 21-a, `monomorphize` returns its input unchanged when there are no
  substitutions, the Rust frontend never attaches any, and Reussir has no
  other substitution site (`CompilePolymorphicFFI.cpp` and `ffi.rs` are
  the only two). It also checked the e2e test's values (4 and 43, so 443).

**Effect on lean2rr.** None needed with the escape; the patch removes the
cause for every texture.

## Upstream note

`monomorphize` in `CompilePolymorphicFFI.cpp` drops a `[:` that has no
closing `:]` (it writes only the text after it), so a texture containing
`b"a[:b"` reaches rustc as `b"ab"`. The Rust `substitute_placeholders`
keeps it. Fix: when the scan ends inside a placeholder, write `[:` before
the rest of the body.
