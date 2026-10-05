# Conversions and casts

One Lean type can have several Reussir representations (`List Nat` and the
uniform `List Box`, `LNatArr` and `RVec<Box>`, `Nat → Nat` and
`Box → Box`), and mono erases `unsafeCast`, so a value can meet code
expecting another type that Lean represents alike. lean2rr inserts a
conversion wherever a value's Reussir type differs from the type expected
where it is used: the typed counterpart of Lean's `explicitBoxing`. The
rules are in plan [§5.1](../../translation-plan.md#51-type-translation)
and [§5.5](../../translation-plan.md#55-cases).

- [structural.md](structural.md): converting between instantiations of
  one inductive and between arrays; loops instead of recursion; reusing
  the object when layouts agree.
- [wrappers.md](wrappers.md): function values and thunks/tasks, which are
  wrapped lazily instead of rebuilt.
- [box-unboxing.md](box-unboxing.md): which `Box` variants an unboxing
  function accepts, and how it converts them.
- [casts.md](casts.md): `unsafeCast` between different types, following
  Lean's native layouts and boxed scalars.
- [liveness.md](liveness.md): the helpers (unboxing, application and
  conversion functions, reference dispatch) generated only for what live
  code reaches, and the functions nothing reaches dropped (optional pass
  `conv-liveness`).

A converted value is a new, unshared value: it is not `ptrEq` to its
original, and an update of it never shows in the original
([../representations/identity.md](../representations/identity.md)).
