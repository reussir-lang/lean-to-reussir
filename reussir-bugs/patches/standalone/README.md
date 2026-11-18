# Standalone forms of series patches

A patch of the series applies after the patches before it in `../series`.
When its series form depends on the context of an earlier series patch, a
second form that applies to the base alone (`../base`) is kept here, under
the same file name. These files are not in `series`; do not apply both forms.

- `30-a-vector-to-llvm-patterns.patch`: 30-a for pristine upstream. The
  series form depends on the context of 28-a.
