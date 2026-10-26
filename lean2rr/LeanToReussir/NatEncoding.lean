/-!
# Which values of `Nat` and `Int` are small

A `Nat` and an `Int` are Reussir's built-in integers (`core::num::Nat`/`Int`,
rcgmp; docs/implementation/representations/nat-int.md): an immediate (a
value in [-2^61, 2^61)) or a counted heap integer. (Until 2026-10-26
`--int-backend leanrt` chose a second representation, leanrt's one-word
encoding; clean-integration D8 removed it.)

Only the prelude's Nat and Int sections and Reussir know the words
themselves (the prelude's helpers `l2r_nat_word_is_small`,
`l2r_nat_word_val`, ...): lean2rr's generated code calls those, never a
bit operation on a word. What lean2rr's own rules need is only which
values are small, because a small value costs no allocation (a cost
model: a wrong answer never changes a result). A literal of any size
costs nothing: one outside the immediates is a read-only object in the
program's data, one of rcgmp's immortal integers (`Lower/Values`'
`natLiteral` builds every literal in line, and `Mono`'s `constComputes`
counts no number literal as an allocation). The rules ask here:

- `Opt/CheapConsts`: a constant that builds only small values is
  recomputed at every use (`natIsSmall`, `intIsSmall`);
- `Opt/ModPow2`: the smallest literal power of two it rewrites
  (`natSmallBits`);
- `Lower/Code`: `constIsImmediate` (`boxed-consts` boxes a constant in line
  when its box is an immediate: `natBoxIsImmediate`, `intBoxIsImmediate`).

A new representation of `Nat`/`Int` changes these definitions, the
prelude's Nat and Int sections, leanrt, and the lowering's uses of
Reussir's integers (the box functions, `natIntBoxFns?` in LowerBase)
(docs/implementation/representations/nat-int.md: "Reussir's built-in
integers (rcgmp)" for the prelude and leanrt, "The lowering" for the cost
model and the boxes).
-/

namespace LeanToReussir

/-- Whether `Nat` value `n` is small, an immediate: below 2^61 (rcgmp's
`Handle::immediateMax` is 2^61 - 1). -/
def natIsSmall (n : Nat) : Bool := n < 2 ^ 61

/-- Whether `Int` value `i` is small, an immediate: in [-2^61, 2^61). -/
def intIsSmall (i : Int) : Bool := -(2 ^ 61 : Int) ≤ i && i < 2 ^ 61

/-- Whether a box (`Box`, Lean's `lean_object *`) holds `Nat` value `n` as
an immediate word, `2n + 1`: below 2^63, as Lean's `lean_box` (the
prelude's `l2r_any_of_nat`). Boxing any other value makes a cell
(`boxAllocates`). -/
def natBoxIsImmediate (n : Nat) : Bool := n < 2 ^ 63

/-- Whether a box holds `Int` value `i` as an immediate word: in the
`int32` range (Lean's `lean_box((unsigned)(int)i)`), and in [2^32, 2^62)
and [-2^62, -2^31), the wider immediates `2i + 1`. [2^31, 2^32) and the
values from 2^62 in magnitude are cells (a word of [2^31, 2^32) would read
back as a negative `int32`). The rule is the prelude's, `l2r_any_of_int`
and `l2r_int_box_wide`: this mirrors it for lean2rr's choices
(`constIsImmediate`), where "cell" for an immediate is always safe (a
once-cell it did not need). -/
def intBoxIsImmediate (i : Int) : Bool :=
  (-(2 ^ 31 : Int) ≤ i && i < 2 ^ 31) ||
    (2 ^ 32 ≤ i && i < 2 ^ 62) || (-(2 ^ 62 : Int) ≤ i && i < -(2 ^ 31))

/-- The smallest `k` for which `2^k` is not small: 61. -/
def natSmallBits : Nat := 61

end LeanToReussir
