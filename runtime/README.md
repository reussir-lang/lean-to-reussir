# lean2rr runtime

The runtime has two parts:

- `prelude.rr` — Reussir source that lean2rr prepends to every generated
  program. It defines the runtime types and one function per Lean extern
  (`lean_xxx` for the extern whose C symbol is `lean_xxx`), plus `l2r_*`
  primitives for lean2rr-generated glue.
- `leanrt/` — a Rust crate (rlib) linked into every program. The prelude's
  `#[ffi(import)]` textures call into it. It holds the bignum code (GMP),
  string algorithms, float formatting, buffered stdio, once-cells and panic
  handling — and, being a single crate, the one copy of all global state
  (statics in the prelude's `extern "rust"` block would be duplicated per
  texture).

Semantics follow Lean 4.33's C runtime (`lean.h`, `src/runtime/*.cpp`)
exactly; comments at each function say which C function it mirrors.

## Building and linking

`scripts/l2r.py` does everything:

1. builds `leanrt` with the pinned rustc (`L2R_RUSTC`) into
   `runtime/leanrt/target/libleanrt.rlib`, cached by a hash of its sources;
2. runs lean2rr with `--prelude runtime/prelude.rr`;
3. runs rrc with
   - `--polyffi-rust-path runtime/leanrt/target/rustc-native`: a wrapper that
     adds `-C target-cpu=native -C target-feature=-outline-atomics`. With the
     plain rustc, textures are not inlined into Reussir code, and calls through
     the packed-argument boundary (float or `str` arguments, four or more
     parameters) leave an escaping stack slot that blocks tail-call
     elimination: loops that print floats overflow the stack.
   - `--polyffi-libdir runtime/leanrt/target` (so textures find `leanrt`),
   - `--link-lib libleanrt.rlib --link-lib libgmp.a` (GMP from the Lean
     toolchain, `$(lean --print-prefix)/lib/libgmp.a`, or `L2R_GMP`).

## Representations

| Lean (mono) | Reussir | Notes |
|---|---|---|
| `Nat` | `enum [value] Nat { Small(u64), Big(LBig) }` | `Big` only for values `>= 2^64` |
| `Int` | `enum [value] Int { Small(i64), Big(LBig) }` | `Big` only outside the `i64` range |
| big numbers | `LBig` = `Rc<(bool, Vec<u64>)>` | sign, little-endian limbs, normalized; GMP `mpn`/`mpz` |
| `String` | `LStr` = `Rc<Vec<u8>>` | valid UTF-8, no terminator; copy-on-write |
| `Array α` | `RVec<E>` = `reussir_rt::collections::vec::Vec<E>` | `E` = storage type of `α` |
| `ByteArray`, `FloatArray` | `RVec<u8>`, `RVec<f64>` | `RVec<u8>` and `LStr` share a layout: `String.toUTF8` is free |
| `ST.Ref σ α` / `IO.Ref α` | `LRef<E>` (a shared 0/1-element vector) | mutated through every alias; empty after `take` |
| `UInt8..64`, `USize` | `u8..u64`, `u64` | |
| `Int8..64`, `ISize` | `u8..u64`, `u64` (bit patterns) | signed semantics as `lean_int8_*` etc. |
| `Char` | `u32` | |
| `Float`, `Float32` | `f64`, `f32` | |
| `Bool` | `bool` | |
| `Unit`, `PUnit`, erased | `L2RUnit` | `enum [value] L2RUnit { u }` |

Every function consumes its arguments (Reussir's convention). Strings,
arrays and big numbers are updated in place when uniquely referenced
(`Rc::is_unique`), otherwise copied once.

## Calling convention

As fixed by lean2rr:

- The extern `lean_xxx` is called as the prelude function `lean_xxx`, with
  the extern's mono-phase parameters in order minus erased ones (types,
  proofs, `lcErased`) and minus the IO world (`lcVoid`).
- Polymorphic externs take explicit storage type arguments:
  `lean_array_push<E>(arr, x)`.
- Functions whose results mention Lean-defined inductive types (`List`,
  `Option`, `Prod`, `Ordering`, `EST.Out`, ...) cannot be written here; see
  "Requests for lean2rr".

Nat positions and indices: a `Nat::Big` value is never a valid position or
index. Where Lean's C code distinguishes "not a scalar" (`>= 2^63` in Lean)
from "out of range", the prelude reproduces that too
(`lean_string_utf8_extract`).

## Glue helpers

For externs over Lean-defined types the prelude offers generic helpers that
take the result type's constructors as arguments (nullary constructors as
values, others as curried closures). lean2rr's glue is then just a call:

| extern | helper |
|---|---|
| `lean_string_compare` (→ `Ordering`) | `l2r_string_compare_with<O>(a, b, lt, eq, gt)`; or `l2r_string_compare(a, b) -> u8` (0/1/2) |
| `lean_string_data` (`String.toList`, → `List Char`) | `l2r_string_to_list<L>(s, nil, \|c\| \|t\| cons(c, t))` |
| `lean_string_utf8_get_opt` (→ `Option Char`) | `l2r_string_utf8_get_opt_with<O>(s, p, none, \|c\| some(c))`; or `l2r_string_utf8_get_opt(s, p) -> u32` (`0x110000` = none) |
| `lean_array_to_list` (→ `List α`) | `l2r_array_to_list<E, L>(a, nil, \|x\| \|t\| cons(unbox(x), t))` |
| `lean_float_frexp`, `lean_float32_frexp` (→ `Float × Int`) | `l2r_float_frexp_with<P>(x, \|m\| \|e\| mk(m, e))`; or `l2r_float_frexp_mant`/`l2r_float_frexp_exp` |

## Requests for lean2rr

(See also the proposal patch described in `tests/runtime/README` of the
final report; each item was reproduced with the listed test.)

1. **Constructors with extern implementations.** `Int.ofNat` and
   `Int.negSucc` are constructors carrying `@[extern "lean_nat_to_int"]` /
   `@[extern "lean_int_neg_succ_of_nat"]`. lean2rr lowers them as
   constructors of the non-nominal `Int` and fails ("no representation
   conversion from Nat to L2RUnit"). They must be extern calls. This blocks
   almost every program (Int is reachable from `Float.ofScientific`,
   `Int.repr`, ...). Fix: in `calleeOf`, check `isExtern` before
   `ctorInfo`.
2. **Propositions as types.** `lowerTypeApp` builds nominal types for
   `Prop`-valued inductives (`ByteArray.IsValidUTF8`, from
   `String.fromUTF8?`) and crashes in `instantiateForall`. Propositions have
   no representation (`L2RUnit`), and extern parameters of a
   proposition type are proofs and must not be passed
   (`String.ofByteArray b h` passed `h`).
3. **Extern type arguments must be mono types.** `panicCore @[String.Slice.Pos]`
   gets type argument `T_String_Slice_Pos` while its values are `Nat`
   (Lean's `toMono` unwraps one-field structures). Apply `toMonoType` to
   extern instance type arguments.
4. **Box only type-variable positions of polymorphic externs.** For
   `Array.get!Internal @[Nat]` the index is boxed too
   (`lean_array_get<ElemBox>(ElemBox{d}, a, ElemBox{i})`), because boxing is
   decided by comparing instantiated parameter types with the type argument.
   Decide it from the extern's own polymorphic mono signature (`lcAny`
   positions), aligned from the end (instances drop leading type params).
5. **Externs over Lean-defined types** need glue (helpers above): at least
   `lean_string_compare`, `lean_string_data`, `lean_string_utf8_get_opt`,
   `lean_array_to_list`, `lean_float_frexp`, `lean_float32_frexp`,
   `lean_string_intercalate` (takes `List String`), `lean_slice_hash` /
   `lean_slice_dec_lt` (take `String.Slice`; primitives
   `l2r_slice_hash(s, b, e)`, `l2r_slice_dec_lt(s1, b1, e1, s2, b2, e2)`).
6. **Externs implemented by exported Lean code.** Many `String.Internal.*`,
   all `Substring.Raw.Internal.*`, `Array.toList` (`lean_array_to_list_impl`),
   `lean_string_intercalate`, `IO.eprint(ln)`, `lean_stream_of_handle`, the
   `IO.Error` constructors ... are `@[extern "sym"]` declarations whose `sym`
   is provided by an `@[export sym]` Lean definition. lean2rr should compile
   and call that definition (exact semantics for free). The prelude has
   hand-written versions of the `String.Internal.*` ones used by core code.
7. **Element-wise array conversion.** `tryCoerce` does not convert
   `RVec<A>` to `RVec<B>` for two instantiations of one inductive (Lean's
   `cse` merges e.g. the empty `HashMap` buckets across types). Needed by
   `RtHashMap`.
8. **Unsafe implementations.** `Array.map` (via `Array.mapMUnsafe`),
   `HashMap.filter` and `Array.modify` (via `Array.modifyM`, which stores
   `unsafeCast ()` in the slot) use `unsafeCast` between element types of
   different representations. lean2rr should use the safe reference
   definitions (not the `@[implemented_by]` unsafe ones), or map them to
   runtime primitives. Test: `RtArrayUnsafe`.
9. **IO/ST externs return `EST.Out`/`ST.Out`**, so they need wrapping
   (`wrapIOResult`) around runtime primitives: `ST.Prim.mkRef`/`Ref.get`/
   `set`/`swap`/`take`/`ptrEq` → `l2r_ref_new/get/set/swap/take/ptr_eq`;
   `IO.monoMsNow`/`monoNanosNow` → `l2r_io_mono_ms_now_nat`/`_nanos_`;
   `IO.getRandomBytes` → `l2r_io_get_random_bytes`; `IO.Process.getPID` →
   `l2r_io_process_get_pid`. `ST.Ref σ α` must be represented as `LRef<E>`.
10. **String literals**: keep them out of loops (once-cells); the prelude's
    `lean_mk_string(s : str)` copies on every evaluation.
11. **`Nat.repr`/`Int.repr` of big numbers** are Lean code that divides by
    10 digit by digit (quadratic); `l2r_nat_repr`/`l2r_int_repr` are exact
    replacements using GMP.

## Known divergences from native Lean

- Native `lean_string_utf8_extract` returns its borrowed string without a
  reference when a position is `>= 2^63`: a use-after-free natively. The
  prelude returns the string (the intended semantics).
- Panics print `backtrace:` and `(stack trace unavailable)` instead of a
  stack trace (unless `LEAN_BACKTRACE=0`, which prints neither, as native).

## Testing

`tests/runtime/run.sh [NAME...]` builds every `tests/runtime/Rt*.lean`
natively (`lean` + `leanc -O3 -DNDEBUG`, like Lake's release build) and
through lean2rr, runs both (`LEAN_BACKTRACE=0`, optional `NAME.args` and
`NAME.stdin`), and compares stdout, stderr and the exit code byte for byte.
`NAME.xfail` marks tests blocked by a lean2rr request.

`runtime/gen_scalars.py` regenerates the fixed-width integer section of the
prelude.
