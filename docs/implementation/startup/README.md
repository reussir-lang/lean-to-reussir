# Startup

What runs before `main`, in which order, how constants are stored and
evaluated, and the entry point that reproduces native Lean's process
behaviour. Plan [§5.11](../../translation-plan.md#511-program-entry) and
[§5.12](../../translation-plan.md#512-constants-cafs-and-closed-terms).

- [order.md](order.md): roots, module phases, the initializer order, the
  startup chain.
- [constants.md](constants.md): once-cells, eager and lazy constants,
  closed-term chains, literal tables, waiting for tasks in constants.
- [entry.md](entry.md): threads, `IO.initializing`, standard streams,
  arguments, exit, startup descriptors.
