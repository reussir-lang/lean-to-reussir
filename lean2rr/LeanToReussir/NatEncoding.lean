/-!
# The representation of `Nat` and `Int`, and which values are small

`--int-backend` chooses how a `Nat` and an `Int` are represented
(docs/implementation/representations/nat-int.md):

- `rcgmp` (the default since 2026-10-25): Reussir's built-in integers
  (`core::num::Nat`/`Int`, rcgmp): an immediate (a value in
  [-2^61, 2^61)) or a counted heap integer;
- `leanrt` (the default until 2026-10-25): one word, Lean's own encoding
  (the prelude's `struct Nat`, `struct Int`; `leanrt::nat`): a small value
  is an immediate word, any other value a big number on the heap.

Only the prelude's Nat and Int sections and leanrt know the words
themselves (the encoding helpers `l2r_nat_small`, `l2r_nat_word_is_small`,
`l2r_nat_word_val`, `l2r_int_small`, ...). The prelude keeps both
representations in marked blocks (`filterIntBackend`), which define the
same functions: lean2rr's generated code calls those, never a bit
operation on a word. What lean2rr's own rules need is only which values
are small, because a small value costs no allocation (a cost model: a
wrong answer never changes a result). They ask here:

- `Lower/Values`: `natLiteral` (a literal that costs nothing, `natLitFree`,
  is built in line; under `leanrt` a bigger one is parsed from its
  decimal digits);
- `Opt/CheapConsts`: a constant that builds only small values is
  recomputed at every use;
- `Mono`: `constComputes` (a literal that is not free allocates);
- `Opt/ModPow2`: the smallest literal power of two it rewrites
  (`natSmallBits`);
- `Lower/Code`: `constIsImmediate` (`boxed-consts` boxes a constant in line
  when its box is an immediate: `natBoxIsImmediate`, `intBoxIsImmediate`).

A new representation of `Nat`/`Int` changes these definitions, the
prelude's blocks, leanrt, and the lowering's choices that read
`LowerCtx.intBackend` (the box functions, the containers that keep a
`Nat` out of the FFI's type arguments; LowerBase)
(docs/implementation/representations/nat-int.md, "The encoding is known in
one place").
-/

namespace LeanToReussir

/-- The representation of `Nat` and `Int` (`--int-backend`). -/
inductive IntBackend where
  /-- leanrt's one-word encoding (the default until 2026-10-25). -/
  | leanrt
  /-- Reussir's built-in integers (rcgmp; the default since 2026-10-25). -/
  | rcgmp
  deriving BEq, Inhabited, Repr

/-- The backend named `s` (`--int-backend`'s argument). -/
def IntBackend.ofString? : String → Option IntBackend
  | "leanrt" => some .leanrt
  | "rcgmp" => some .rcgmp
  | _ => none

/-- Whether `Nat` value `n` is small, an immediate of backend `b`: below
2^63 under `leanrt` (Lean's `LEAN_MAX_SMALL_NAT`; the prelude's
`l2r_nat_val_is_small`), below 2^61 under `rcgmp` (rcgmp's
`Handle::immediateMax` is 2^61 - 1). -/
def natIsSmall (b : IntBackend) (n : Nat) : Bool :=
  match b with
  | .leanrt => n < 2 ^ 63
  | .rcgmp => n < 2 ^ 61

/-- Whether `Int` value `i` is small, an immediate of backend `b`: in the
`int32` range under `leanrt` (Lean's
`LEAN_MIN_SMALL_INT`..`LEAN_MAX_SMALL_INT`; the prelude's
`l2r_int_val_is_small`), in [-2^61, 2^61) under `rcgmp`. -/
def intIsSmall (b : IntBackend) (i : Int) : Bool :=
  match b with
  | .leanrt => -(2 ^ 31 : Int) ≤ i && i < 2 ^ 31
  | .rcgmp => -(2 ^ 61 : Int) ≤ i && i < 2 ^ 61

/-- Whether the `Nat` literal `n` costs nothing to build under backend
`b`: a small value under `leanrt` (a bigger one is parsed from its digits
at each evaluation), any value under `rcgmp` (a literal outside the
immediates is a read-only object in the program's data, one of rcgmp's
immortal integers). -/
def natLitFree (b : IntBackend) (n : Nat) : Bool :=
  b == .rcgmp || natIsSmall b n

/-- Whether a box (`Box`, Lean's `lean_object *`) holds `Nat` value `n` as
an immediate word, `2n + 1`: below 2^63, as Lean's `lean_box` (under
`rcgmp` the prelude's `l2r_any_of_nat`). Under `rcgmp` boxing any other
value makes a cell (`boxAllocates`). -/
def natBoxIsImmediate (n : Nat) : Bool := n < 2 ^ 63

/-- Whether a box holds `Int` value `i` as an immediate word under backend
`b`: in the `int32` range (Lean's `lean_box((unsigned)(int)i)`); under
`rcgmp` also in [2^32, 2^62) and [-2^62, -2^31), the wider immediates
`2i + 1`. [2^31, 2^32) and the values from 2^62 in magnitude are cells (a
word of [2^31, 2^32) would read back as a negative `int32`). The rule is
the prelude's rcgmp block, `l2r_any_of_int` and `l2r_int_box_wide`: this
mirrors it for lean2rr's choices (`constIsImmediate`), where "cell" for an
immediate is always safe (a once-cell it did not need). -/
def intBoxIsImmediate (b : IntBackend) (i : Int) : Bool :=
  (-(2 ^ 31 : Int) ≤ i && i < 2 ^ 31) ||
    (b == .rcgmp && ((2 ^ 32 ≤ i && i < 2 ^ 62) || (-(2 ^ 62 : Int) ≤ i && i < -(2 ^ 31))))

/-- The smallest `k` for which `2^k` is not small under backend `b`: 63
under `leanrt`, 61 under `rcgmp`. -/
def natSmallBits : IntBackend → Nat
  | .leanrt => 63
  | .rcgmp => 61

/-- The prelude's text for backend `b`: the lines of the other backend's
blocks and the marker lines left out, every other line kept. A line
`// @int-backend NAME` (at the start of the line; `NAME` is `leanrt` or
`rcgmp`) opens a block, which `// @int-backend end` closes; blocks do not
nest. A block opened inside a block, an `end` outside one, an unknown
name, or a block left open is an error: the prelude would define a
function twice, or not at all. -/
def filterIntBackend (prelude : String) (b : IntBackend) : Except String String := do
  let marker := "// @int-backend "
  let mut out : Array String := #[]
  let mut cur : Option (IntBackend × Nat) := none
  let mut lineNo := 0
  for line in prelude.splitOn "\n" do
    lineNo := lineNo + 1
    if line.startsWith marker then
      let arg := (line.drop marker.length).trimAsciiEnd.toString
      if arg == "end" then
        if cur.isNone then throw s!"prelude line {lineNo}: `{marker}end` outside a block"
        cur := none
      else
        let some nb := IntBackend.ofString? arg
          | throw s!"prelude line {lineNo}: unknown backend `{arg}` (expected leanrt, rcgmp or end)"
        if let some (_, o) := cur then
          throw s!"prelude line {lineNo}: a block opened inside the block of line {o}"
        cur := some (nb, lineNo)
    else if cur.all (·.1 == b) then
      out := out.push line
  if let some (_, o) := cur then throw s!"prelude line {o}: block not closed by `{marker}end`"
  return "\n".intercalate out.toList

end LeanToReussir
