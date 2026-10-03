# Strings

Paths: `runtime/prelude.rr`, `runtime/leanrt/src/string.rs`, and
`lean2rr/LeanToReussir/` for lean2rr's files.

### A string keeps its character count

- **What:** `LStr` is `Rc<(Vec<u8>, u64)>`: valid UTF-8 bytes without a
  terminator, and the number of characters (Lean's `m_length`), which every
  function that builds or changes a string keeps up to date. It is
  copy-on-write: modified in place when unique.
- **Why:** `String.length` was an out-of-line byte scan; now it is an
  inlined field read, as natively (adv4 PF4-02, 5dfb324).
- **Where:** `prelude.rr`: `LStr`, `lean_string_length`;
  `leanrt/src/string.rs`.
- **Remove only if:** never. Cost: two allocations (the counted box and the
  byte buffer) where Lean has one. In progress on branch `ffi-c`
  (7a784e1): one block with Lean's 32-byte string header, so C code can
  read it as it is ([../externs-ffi/c-ffi.md](../externs-ffi/c-ffi.md)).

### `String.set` updates in place without a temporary vector

- **What:** `String.set` encodes the character into a stack buffer and
  overwrites in place when the width does not change, with an inline fast
  path for an ASCII character over an ASCII character of a unique string;
  `String.append` has an inline fast path for a unique left string with
  spare capacity.
- **Why:** As C's fast paths (adv4 PF4-05, 5dfb324; 5153e6c).
- **Where:** `prelude.rr`: `lean_string_utf8_set`, `lean_string_append`;
  `leanrt/src/string.rs`: `set`, `append`.
- **Remove only if:** never (speed only).

### String literals come from a generated table

- **What:** A string literal is `l2r_str_lit(id)`, a runtime function
  generated with the program that builds the string from a table of Rust
  byte strings. The bytes are written as escapes, so every literal
  round-trips exactly. Literals are deduplicated by content.
- **Why:** A Reussir `str` argument goes through a stack slot whose
  address escapes, and LLVM then never turns the enclosing function's tail
  calls into loops (9346467). The prelude avoids `str` parameters on hot
  paths for the same reason.
- **Where:** `LowerBase.lean`: `strLit`, `strLitTable`;
  `Emit/Program.lean`: `LoweredProgram.render`; plan
  [§5.4](../../translation-plan.md#54-let-return-literals).
- **Remove only if:** Reussir passes `str` without an escaping slot (or
  guarantees tail calls).

### `[` is escaped in the string literal table

- **What:** `strLitTable` writes `[` as `\x5b`, like `"`, `\` and
  non-printable bytes.
- **Why:** The table is the body of a polymorphic FFI texture, where `[:`
  starts a placeholder `[:Name:]`. Reussir dropped an unterminated `[:`, so
  a literal containing `[:` (an IPv6 address `[::1]`, a Python slice)
  printed without it, and the first such `[:` of the whole table was lost
  ([Reussir bug 21](../../../reussir-bugs/21-unterminated-placeholder.md);
  round 6 RV6L-01, 96c7140; test `RtStrLitBracket`).
- **Where:** `LowerBase.lean`: `strLitTable`.
- **Remove only if:** never needed with patch 0016 applied (it is not, on
  `l2r-local`); the escape costs nothing, so it can stay.

### Strings from the operating system are decoded as `lean_mk_string`

- **What:** Strings that come from the OS or libuv (environment, home and
  temporary directories, process title, passwd entries, paths of temporary
  files, `argv`) are decoded with invalid UTF-8 replaced by U+FFFD.
- **Why:** Native Lean builds them with `lean_mk_string`, which does this
  (round 6 IO6 findings, 1362da1).
- **Where:** `leanrt/src/string.rs`: `from_bytes_lossy`;
  `prelude.rr`: `l2r_argv`.
- **Remove only if:** never.
