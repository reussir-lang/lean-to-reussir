# Single externs in the runtime

Special cases inside the runtime's implementation of particular externs.
Paths are relative to the repository root.

### `Float.cbrt` and `Float32.cbrt` call glibc's, looked up in libm.so.6

- **What:** The prelude's `cbrt` and `cbrtf` call
  `leanrt::float::libm::cbrt`/`cbrtf`, which find glibc's functions once
  with `dlopen("libm.so.6")` and `dlsym`, and cache the answer. If libm.so.6
  cannot be opened, they look in the global scope (`dlsym(RTLD_DEFAULT,
  ..)`); with no C library function at all, they use Rust's `f64::cbrt`.
  The other libm functions without a Reussir lowering (`asinh`, `acosh`,
  `atanh` and their `f32` versions) are plain `extern "C"` declarations.
- **Why:** Natively these externs are the C library's `cbrt`/`cbrtf`.
  Rust's `compiler_builtins`, linked into every executable ahead of libm,
  defines its own `cbrt` (a port of CORE-MATH's correctly rounded one) and
  `cbrtf` (FreeBSD's) on Linux, and the static link binds any reference
  named `cbrt` to those, so a direct `extern "C"` declaration does not reach
  glibc. They differ from glibc's by 1-2 ulps on about half the doubles
  (cbrt 27.0 is 3.0 there and 3.0000000000000004 in glibc) and on about
  one float in ten (random bit patterns). Until fix-r9-misc the
  lookup used only the global scope, which holds libm only while the
  executable imports some other libm function. Every lean2rr executable
  does (the prelude's `asinh` & co., `frexp`, `scalbn`, `log`), so glibc's
  `cbrt` always ran; in an executable without such an import (checked with
  a plain Rust program) the lookup finds nothing, and the old code then
  used Rust's `cbrt` silently. Tests: `tests/runtime/RtFloatCbrt.lean`
  (54 doubles and 48 floats chosen so that 27 and 12 of them tell the two
  apart, plus 2000 random bit patterns) fails on 40 of its 103 lines when
  the fallback runs; leanrt's unit test `float::libm::tests::cbrt_is_the_c_librarys`
  (`tests/runtime/leanrt-unit.sh`, a binary without libm imports) fails
  with the old lookup. lean2rr executables are dynamic PIEs, and libm.so.6
  is one of their load-time dependencies. A fully static build would have
  no libm.so.6 to open and would silently fall back to Rust's `cbrt`, so if
  static linking is ever added, it must link glibc's `cbrt` some other way.
- **Where:** `runtime/leanrt/src/float.rs`: `libm::resolve`, `libm::cbrt`,
  `libm::cbrtf`; `runtime/prelude.rr`: `cbrt`, `cbrtf`.
- **Remove only if:** `compiler_builtins` stops defining `cbrt`/`cbrtf` on
  Linux (then a plain `extern "C"` declaration binds to libm), or Reussir
  links libm ahead of the Rust runtime.

### `System.Platform.target` follows leanrt's target

- **What:** `lean_system_platform_target` returns
  `leanrt::rt::PLATFORM_TARGET`, chosen by `cfg` for the target leanrt is
  compiled for: `aarch64-unknown-linux-gnu` or `x86_64-unknown-linux-gnu`,
  the triples the native Lean toolchains for those hosts report
  (`lean --version`). Any other target is a `compile_error!` naming what
  to do. The prelude's other platform answers are constants that rely on
  the same restriction: `isWindows`, `isOSX` and `isEmscripten` are false,
  and `numBits` is 64 (`USize` is `u64` in the prelude).
- **Why:** Natively the triple is `LEAN_PLATFORM_TARGET` from the
  toolchain's `version.h` (`lean.h` inlines `lean_system_platform_target`;
  Lean's CMake takes it from `clang --print-target-triple`), so it is the
  triple of the platform the program is built for. The prelude used to
  hard-code `aarch64-unknown-linux-gnu`, which is wrong on an x86-64 host
  (fix-r9-misc). leanrt builds only for Linux with glibc on aarch64 and
  x86-64 (signal structures, the glibc `FILE` model, `coro`'s stack
  switching), hence the error elsewhere instead of a guess. Test
  `tests/runtime/RtPlatform.lean` compares the triple, the word size, the
  three flags and the version strings with native.
- **Where:** `runtime/leanrt/src/rt.rs`: `PLATFORM_TARGET`;
  `runtime/prelude.rr`: `lean_system_platform_target`,
  `l2r_platform_target`, `lean_system_platform_windows`/`osx`/`emscripten`,
  `lean_system_platform_nbits`.
- **Remove only if:** never; extend `PLATFORM_TARGET` (and review the
  constants) when leanrt gains a target.
