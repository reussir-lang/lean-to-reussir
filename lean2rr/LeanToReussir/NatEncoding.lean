/-!
# Which `Nat` and `Int` values are small

A `Nat` or `Int` is one word (the prelude's `struct Nat`, `struct Int`;
`leanrt::nat`): a small value is an immediate word, any other value a big
number on the heap. Only the prelude's Nat and Int sections and leanrt know
the words themselves (the encoding helpers `l2r_nat_small`,
`l2r_nat_word_is_small`, `l2r_nat_word_val`, `l2r_int_small`, ...):
lean2rr's generated code calls those, never a bit operation on a word.
What lean2rr's own rules need is only which values are small, because a
small value costs no allocation. They ask here:

- `Lower/Values`: `natLiteral` (a small literal is `l2r_nat_small(k)`, a
  bigger one is parsed from its decimal digits);
- `Opt/CheapConsts`: a constant that builds only small values is
  recomputed at every use;
- `Mono`: `constComputes` (a big literal allocates).

A new representation of `Nat`/`Int` changes these two definitions, the
prelude's two sections and leanrt, and nothing else
(docs/implementation/representations/nat-int.md, "The encoding is known in
one place").
-/

namespace LeanToReussir

/-- Whether `Nat` value `n` is small: below 2^63 (Lean's
`LEAN_MAX_SMALL_NAT`; the prelude's `l2r_nat_val_is_small`). -/
def natIsSmall (n : Nat) : Bool := n < 2 ^ 63

/-- Whether `Int` value `i` is small: in the `int32` range (Lean's
`LEAN_MIN_SMALL_INT`..`LEAN_MAX_SMALL_INT`; the prelude's
`l2r_int_val_is_small`). -/
def intIsSmall (i : Int) : Bool := -(2 ^ 31 : Int) ≤ i && i < 2 ^ 31

end LeanToReussir
