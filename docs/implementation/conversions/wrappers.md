# Lazy conversions: function values, thunks and tasks

Function values, thunks and tasks are not rebuilt when they change
representation: they are wrapped, and the wrapper converts on use. Paths
are relative to `lean2rr/LeanToReussir/`. Plan
[§5.1](../../translation-plan.md#51-type-translation) (function values)
and [§5.14](../../translation-plan.md#514-thunks-and-tasks) (converted
thunks and tasks).

### Function values stay one wrapper deep

- **What:** `l2r_fconv_S_T(f)` converts a function value `f : S` to
  representation `T`: a wrapped value `w<R>(g)` is converted from `R`
  directly (`g` itself when `R` is `T`, else `l2r_fconv_R_T(g)`, generated
  on demand); any other value is wrapped once in `w<S>`, whose application
  converts the arguments and the result and calls the function exactly
  once. A function value is boxed as it is (its own variant), and
  unboxing it to another representation wraps it.
- **Why:** A structure with a closure field crossing uniform code in a
  loop built a chain of wrappers (adv2 data D1: 55 s → 0.00 s, 0cba3ff);
  a value read at three representations in a loop (`Nat → Nat`,
  `Nat → Box`, `Box → Box`) gained three wrappers per round (Rp3MinFn3
  3e6: 0.22 s and 418 MB → 0.16 s and 6 MB; 3e7 overflowed the stack;
  adv3 RP3-3, 288e722). Coming back to its own representation gives the
  value itself, as natively.
- **Where:** `Lower/FnValues.lean`: `fnConvFn`, `unboxFnFn`;
  `Lower/Finish.lean`: `genFnConv`, `genApply`; `Lower/Conv.lean`:
  `tryCoerce`.
- **Remove only if:** never. These functions are kept out of rrc's
  inliner ([../reussir-workarounds/build-time.md](../reussir-workarounds/build-time.md#bug-20-the-inliner-multiplies-conversion-code)).

### Thunks and tasks convert lazily and convert back to the original

- **What:** A thunk or task converted to another representation is a new
  cell in state `conv(g, o, a)`: `g` forces the original and converts its
  value (so the original's computation still runs at most once), `o` is
  the original cell (boxed), `a` its address. Converting it back gives `o`
  itself; converting a copy to a third representation converts the
  original directly. A computed value is converted at once
  (`convdone(v, o, a)`, which keeps the original so its address stays this
  cell's identity). For a task, `a` is also its identity for the runtime:
  the copy's state, `IO.cancel` and cancellation are the original's.
- **Why:** A thunk crossing between typed and uniform code in a loop built
  a chain of cells (DatThunkWrap 1e7: a stack overflow, then 6.6 MB; adv2
  D1, f9e06af). Asking a running task's state through a converted handle
  hung (787b48c).
- **Where:** `Lower/Conv.lean`: `lazyConv`; `LowerBase.lean`: `lazyState`
  (the `conv`/`convdone` variants); `Lower/LazyForce.lean`: `lazyGetFn`,
  `taskAddrFn`; `Lower/Identity.lean`: `lazyAddrFn`.
- **Remove only if:** never. Branch `mem-identity` (in progress) drops
  `convdone` and the thunk's recorded address (a task keeps the original's
  runtime identity).

### A converted thunk or task has no running state of its own

- **What:** Forcing a copy runs `g` and leaves the copy in `conv` while it
  runs; forcing it again meanwhile runs `g` again, which waits for the
  original if that is running and has the original's value once it has
  finished. Only the original is ever `busy`.
- **Why:** The copy used to go `busyconv` while forced. The original's
  end walks its `sync` dependents inside the copy's forcing, and one that
  forced the copy (as natively it may read the finished original) found it
  busy on the running context and waited forever (round 6 RV6T-04, adv4
  Tk4Box2; bf63d37; test `RtTaskConvSync`).
- **Where:** `Lower/LazyForce.lean`: `lazyGetFn`; `Lower/Conv.lean`:
  `lazyConv`.
- **Remove only if:** never.
