# Control flow

How mono LCNF's `let`, `cases`, join points and calls become structured
Reussir code, and how lean2rr keeps loops loops and functions small enough
for rrc. Plan [§5.2](../../translation-plan.md#52-declarations-calls-arities)
to [§5.6](../../translation-plan.md#56-join-points), and "Build time" in
[§10](../../translation-plan.md#10-known-divergences-and-unsupported-features).

- [calls-and-lets.md](calls-and-lets.md): arities, `let`s, constructors
  that are calls, panics.
- [cases.md](cases.md): `cases` lowering and the match shapes that help
  Reussir reuse cells.
- [join-points.md](join-points.md): the J1/J2/J1′/J3 strategy, sinking,
  the bounds on duplication, captures of outlined join points.
- [state-machines.md](state-machines.md): J4, loops through outlined join
  points as one function.
- [outline.md](outline.md): deep and long functions cut into parts after
  lowering.

The startup chain's chunks are in
[../startup/order.md](../startup/order.md#the-startup-chain-is-cut-into-chunks-of-128-steps).
