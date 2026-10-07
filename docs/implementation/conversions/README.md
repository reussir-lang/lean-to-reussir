# Conversions and casts

An inductive has one Reussir type, whatever its type arguments: `Tree Nat`
and `Tree α` are one type, whose field of type `α` is a `Box`
([../representations/records.md](../representations/records.md#an-inductive-has-one-type-whatever-its-arguments)).
So a value of an inductive is never rebuilt to change its layout: it goes
between a `Box` position and a typed position by boxing or unboxing. So
does a value of an array, a thunk, a task or a reference: one type each,
over `Box`. Only a function type still has several Reussir
representations (`Nat → Nat` and `Box → Box`). And mono erases
`unsafeCast`, so a value can meet code expecting another type that Lean
represents alike. lean2rr inserts a conversion wherever a value's Reussir
type differs from the type expected where it is used: the typed
counterpart of Lean's `explicitBoxing`. The rules are in plan
[§5.1](../../translation-plan.md#51-type-translation) and
[§5.5](../../translation-plan.md#55-cases).

- [structural.md](structural.md): where conversions are inserted;
  reusing the object when layouts agree.
- [wrappers.md](wrappers.md): function values, which are wrapped lazily
  instead of rebuilt.
- [box-unboxing.md](box-unboxing.md): which `Box` variants an unboxing
  function accepts, and how it converts them.
- [casts.md](casts.md): `unsafeCast` between different types, following
  Lean's native layouts and boxed scalars.
- [liveness.md](liveness.md): the helpers (unboxing, application and
  conversion functions) generated only for what live
  code reaches, and the functions nothing reaches dropped (optional pass
  `conv-liveness`).

A converted value is a new, unshared value: it is not `ptrEq` to its
original, and an update of it never shows in the original
([../representations/identity.md](../representations/identity.md)).
