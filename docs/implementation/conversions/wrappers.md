# Lazy conversions: function values

Function values are not rebuilt when they change representation (a
function type has one per lowered type: `Nat → Nat` and `Box → Box`):
they are wrapped, and the wrapper converts on use. (Thunks and tasks have
one representation each, over `Box`, and never convert.) Paths are
relative to `lean2rr/LeanToReussir/`. Plan
[§5.1](../../translation-plan.md#51-type-translation).

### Function values stay one wrapper deep

- **What:** `l2r_fconv_S_T(f)` converts a function value `f : S` to
  representation `T`: a wrapped value `w<R>(g)` is converted from `R`
  directly (`g` itself when `R` is `T`, else `l2r_fconv_R_T(g)`, generated
  on demand); any other value is wrapped once in `w<S>`, whose application
  converts the arguments and the result and calls the function exactly
  once. A function value is boxed as it is (its own variant), and
  unboxing it to another representation wraps it. Types that differ only
  in phantom domains (rule 4) share an enum: a wrapper records its target
  type when that has phantom domains (`w<S>_<T>`), and `l2r_fconv_S_T`
  unwraps the wrappers made for `S`, or for a type that differs from `S`
  only in leading phantom domains when those are no arguments of the
  wrapped value either.
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
  inliner ([../reussir-workarounds/build-time.md](../reussir-workarounds/build-time.md#issue-20-cost-the-inliner-multiplies-conversion-code)).

