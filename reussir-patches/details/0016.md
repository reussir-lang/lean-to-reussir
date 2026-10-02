# Patch 0016: an unterminated `[:` in an FFI texture is dropped (bug 21)

Patch file: `../0016-l2r-local-bug-21-keep-an-unterminated-in-a-polymorph.patch`
(made as commit `17657841` in a scratch checkout). Bug section:
[docs/reussir-bugs.md, bug 21](../../docs/reussir-bugs.md#21-an-unterminated--in-a-polymorphic-ffi-texture-is-dropped).

## 1. Summary

The Rust body of an `#[ffi(import)]` function (a "texture") may contain
placeholders `[:Name:]`, which rrc replaces with the function's type or
value arguments before handing the body to rustc. The C++ code that does
the replacement treated every `[:` as the start of a placeholder. When no
`:]` followed, it dropped the `[:`, and it did not look for any later
`[:` either. Reussir's Rust implementation of the same substitution keeps
such a `[:` as written. The patch makes the C++ code do the same.

## 2. Symptom

Repro `docs/reussir-bugs/bug21-unterminated-placeholder.rr`:

```
#[ffi(import)]
fn say(x : u64) [{ println!("{}", x) }];
#[ffi(import)]
fn unterminated_len() -> u64 [{ b"a[:b".len() as u64 }];
#[main]
fn main() { say(unterminated_len()); }
```

Command: `rrc bug21-unterminated-placeholder.rr -O aggressive`.

- Expected: prints `4` (the byte string `a[:b` has four bytes).
- Actual on ef922049: prints `2`. rustc was given `b"ab"`. `run.sh`
  prints `bug 21   REPRODUCES` on the unpatched build.

Found by round-6 testing (`adv6/stdlib/M03Bracket.lean`). In Lean:

```
def main : IO Unit := IO.println "slice a[:3] and b[:4]"
```

Native Lean prints `slice a[:3] and b[:4]`. Built by lean2rr it printed
`slice a3] and b[:4]`: the first `[:` is lost, and the second survives
only because the scan never looked at it.

## 3. Root cause

`lib/Conversion/CompilePolymorphicFFI/CompilePolymorphicFFI.cpp`,
`monomorphize`, scans the body with a cursor and a flag:

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

On a `[:` it writes the text before it and moves the cursor past it. If
the body ends before any `:]`, the loop ends with `inSubstitution` still
set, and the last line writes only the text after the `[:`. The two
characters are gone.

The Rust implementation (`substitute_placeholders`,
`crates/reussir-core/src/full/ffi.rs`) copies an unterminated `[:` and the
rest of the body unchanged. So the two implementations disagree, and the
C++ one changes what the program means.

Why lean2rr hits it: lean2rr's string literals live in a single texture
body. `l2r_str_lit(id)` holds a table of Rust byte strings
(`LowerBase.strLitTable`), and printable ASCII is written as it is. So a
`[:` in any Lean string literal, with no `:]` anywhere after it in the
table, was dropped.

## 4. The fix

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

## 5. Verification

- New Reussir test `tests/integration/frontend/ffi_unterminated_placeholder_e2e`
  (`.rr` and `.c`): `b"a[:b".len()` (4), and a texture whose `[:` is
  closed by a `:]` in a later byte string (`b"x[:y"`, `b"z:]"`: an unknown
  key, kept as written, 4 * 10 + 3 = 43). The driver checks for 443. It
  exits 0 with the patch and 1 without it.
- `docs/reussir-bugs/run.sh`: `bug 21 FIXED` on the patched build
  (prints 4).
- lean2rr's runtime test `tests/runtime/RtStrLitBracket.lean`: literals
  with `[:` and with `[::`, `[:` built by interpolation, `splitOn "[:"`,
  `replace "[:" "<>"`. Its output equals native Lean's (with lean2rr's
  escape of `[`, also without the patch).

## 6. Effect on lean2rr

Without the patch, a Lean program printing a string with `[:` (a Python
or Go slice in a message, an IPv6 address like `[::1]`) printed it wrong,
and string operations on such literals gave wrong results (`"a[:b".replace
"[:" "<>"` with the pattern literal emptied). It was not limited to one
literal: the first `[:` in the whole table was dropped whenever no `:]`
followed it anywhere in the table.

lean2rr now also writes `[` as `\x5b` in the literal table, so its literals
never contain placeholder syntax, with or without the patch (round-6 review,
RV6L-01). The patch fixes the cause in Reussir, for any texture: every `[:`
in lean2rr's prelude starts a closed placeholder, so lean2rr itself no
longer depends on it.

## 7. Upstream note

`monomorphize` in `CompilePolymorphicFFI.cpp` drops a `[:` that has no
closing `:]` (it writes only the text after it), so a texture containing
`b"a[:b"` reaches rustc as `b"ab"`. The Rust `substitute_placeholders`
keeps it. Fix: when the scan ends inside a placeholder, write `[:` before
the rest of the body.
