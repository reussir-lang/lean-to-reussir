# Monomorphization and types

How lean2rr turns Lean's polymorphic base LCNF into a closed monomorphic
program with exact types: Stage 1 (instances), Stage 2 (Lean's own passes,
edited), Stage 3 (types mono lost, recovered), and the places where a type
stays unknown (`lcAny`, the uniform `Box`). The rules themselves are in
plan [§2](../../translation-plan.md#2-stage-1--collect-and-monomorphize),
[§3](../../translation-plan.md#3-stage-2--leans-mono-pipeline-leans-passes-driven-by-us)
and [§4](../../translation-plan.md#4-stage-3--check-and-recover-lost-types).

- [instances.md](instances.md): Stage 1's instances: arities, names,
  static dictionaries, the declarations it treats specially.
- [polymorphic-recursion.md](polymorphic-recursion.md): the bounds and cuts
  that keep the set of instances and types finite.
- [lean-passes.md](lean-passes.md): Stage 2, Lean's mono pipeline with
  lean2rr's copies of three passes and two passes not run.
- [type-recovery.md](type-recovery.md): Stage 3's rules for types mono lost,
  and the parameters of type `lcErased` that receive data (a Lean
  compiler bug, retyped `lcAny` after Stage 1 and after Stage 2).
- [uniform-types.md](uniform-types.md): `lcAny`, relevance, Lean's
  uniform-representation library code, and the "can cast" fact.

How `lcAny` values are represented (`Box`) is in
[../representations/box-and-uniform.md](../representations/box-and-uniform.md);
how they are converted, in [../conversions/](../conversions/README.md).
