# 16. rrc's 1 GiB driver stack breaks builds under an address-space limit

## Summary

**Kind:** bug (crash on valid input under a resource limit). **Status:**
not patched in lean2rr's builds: the reworked patch 16-a is parked
outside the series ([parked option](#parked-option-16-a)). It does not
affect lean2rr: lean2rr's builds set no address-space limit that rrc
comes near ([lean2rr](#lean2rr)).

**Upstream (2026-10-24):** Open at upstream 0378b744: the driver's stack
code (`crates/reussir-compiler/src/main.rs`) has no change since
7954a367. Upstream #686
(`3e34334f`) is our old patch 31-a, which fixed the stack overflow on
deep expressions (old entry 31); this entry is the part of old 31 that
remains. Upstream `ea240b19` (#758, 2026-10-25) changes rrc's
`driver.rs`, and `00906e38` (#804, 2026-10-25) only the commit of
mlir-rcgmp that the build fetches, not this stack code. No pull request
is planned (owner, 2026-10-19: no more upstream pull requests after
#758); the entry and the parked patch document it.

**Verdict: bug.** Since #686, rrc runs its driver on a thread with a
1 GiB stack. The stack is reserved address space, and an address-space
limit (`ulimit -v`, `RLIMIT_AS`) counts all of it. Under a limit that is
too small for the stack, the thread cannot be created, and rrc runs the
driver on the main thread as before: the build works. Under a limit
slightly larger, the thread is created, but the compilation then has
about 1 GiB less address space than before, and rrc aborts where an rrc
without the thread compiled.

## Symptom and repro

No repro file in [`repros/`](repros/): upstream's own test
`tests/integration/frontend/driver_stack_address_limit.rr` (a 3-line
program, with the C driver `driver_stack_address_limit.c`) is the repro
when it runs under other limits. From a scratch directory:

```sh
bash -c 'ulimit -v LIMIT && exec RRC_CHECKOUT/build/bin/rrc \
    RRC_CHECKOUT/tests/integration/frontend/driver_stack_address_limit.rr \
    -o out.o --relocation-mode pic'
```

**Expected.** Compiles (exit 0) under each limit, as rrc built from
upstream before #686 (for example `b6981996`) does.

**Actual on 7954a367 (and on `l2r-base3`, 2026-10-19), 20 cores:**

| LIMIT (KiB) | Result |
|---|---|
| 1000000 | compiles: the thread cannot be created, and the fallback runs |
| 1250000 | aborts (exit 134): `terminate called after throwing an instance of 'St9bad_alloc'` |
| 1600000 | aborts (exit 134): `LLVM ERROR: pthread_create failed: Resource temporarily unavailable` |

At 1600000 the failure is in the threads of LLVM's backend. With
`--disable-backend-multithreading` (as the test's own RUN line has it)
that limit compiles, and 1250000 still aborts. Under `ulimit -d`
(`RLIMIT_DATA`), the same three limits compile.

## Cause

`crates/reussir-compiler/src/main.rs`, `main`: `DRIVER_STACK_SIZE` is
1 GiB, and `main` spawns `reussir_compiler::driver::main` on a thread
with that stack. Only if the spawn fails does it run the driver on the
main thread. The spawn reserves the whole stack at once (`mmap`), and
`RLIMIT_AS` counts the reservation, although only the touched pages
become resident. So the spawn succeeds under any limit with 1 GiB free,
and later allocations of the compilation (the C++ `new` of the MLIR and
LLVM stages, LLVM's thread pool) fail. Upstream's test checks only a
limit below the spawn's need (1000000), where the fallback runs.

## lean2rr

No effect in practice:

- `scripts/l2r.py` sets no `ulimit`.
- `cg` (the memory cgroup of lean2rr's local tools) limits resident
  memory, not address space.
- The local `bin/l2r` wrapper sets `ulimit -v 16000000` (16 GB). rrc's
  virtual size on a lean2rr program is about 1.9 GB.

With 16-a, an rrc under `bin/l2r`'s `ulimit -v 16000000` keeps the
1 GiB driver thread: 16-a returns to the main thread only under a
finite limit below 2 GiB. A sum of 8000 terms still compiles there.

## Parked option: 16-a

Patch file:
[`patches/parked/16-a-driver-stack-rlimit.patch`](patches/parked/16-a-driver-stack-rlimit.patch)
(on `7954a367`; it applies to `0378b744` and the `l2r-base5` of then
too, checked 2026-10-24, and to `ea240b19`, `00906e38`, and
`l2r-base5`, `l2r-stepd`, `l2r-base9`, `l2r-base9-shared`, `l2r-base10` and `l2r-base11` on
`00906e38`, checked 2026-10-25, and to `95d9a1c8` and `l2r-base12` on
it, checked 2026-10-26). No build applies it.

The patch changes #686's code in `crates/reussir-compiler/src/main.rs`:

- The driver thread keeps #686's 1 GiB stack.
- A new function `keep_main_thread()` keeps the driver on the main
  thread, as before #686, when
  - `RLIMIT_AS` (`ulimit -v`) or `RLIMIT_DATA` (`ulimit -d`) has a finite
    soft limit below 2 GiB (both count the reserved stack;
    `RLIMIT_DATA` since Linux 4.7);
  - `RLIMIT_STACK` (`ulimit -s`) is unlimited or at least 1 GiB (the
    user's deeper main stack stays);
  - a limit cannot be read.
  On other targets it returns false.
- If the thread cannot be created, the driver runs on the main thread,
  as in #686.
- It adds a dependency on `libc` for Unix targets (for `getrlimit`), and
  a second build under `ulimit -d 1000000` to
  `driver_stack_address_limit.rr`.

**Why it is parked.** The owner's rule since 2026-10-07: Reussir is
changed only where lean2rr has no other way. lean2rr does not reach the
bug.

## Upstream note

rrc runs its driver on a thread with a 1 GiB stack (#686) and falls back
to the main thread only when the spawn fails. The reservation counts
against `RLIMIT_AS`, so under `ulimit -v 1250000` the spawn succeeds and
the compilation then aborts (`std::bad_alloc`, exit 134); under
`ulimit -v 1600000` LLVM's thread pool cannot start a thread
(`pthread_create failed`, exit 134). rrc before #686 compiles in both
cases. Fix (parked patch 16-a): keep the 1 GiB stack, and keep the
driver on the main thread when a finite `RLIMIT_AS` or `RLIMIT_DATA` is
below 2 GiB, when `RLIMIT_STACK` is unlimited or at least 1 GiB, or when
a limit cannot be read.
