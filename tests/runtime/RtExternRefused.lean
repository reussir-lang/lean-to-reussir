/-!
`@[extern]` declarations of the program that lean2rr refuses at translation
time (translation plan §5.8, "Externs of the program"): lean2rr compiles
Lean code plus Lean's runtime library only, and these have no Lean
definition it can use and no binding of their C symbol. The message names
each declaration, its module and its symbol, and why:
- an `opaque` (the `apps/probe` repro's shape without a body), an axiom, a
  definition Lean cannot compile, inline C without a body;
- failed bindings to another declaration's `@[export]`, naming the failed
  test: the type (an `@[export]` of another type), the compiled signature
  (an `@[export]` function that takes the erased proof argument the
  extern's call does not pass);
- a symbol of Lean's runtime library, to which an extern of the program is
  never bound (the owner's decision of 2026-10-04), whatever its type:
  the message names the library's declaration to call instead
  (`lean_nat_add`: `Nat.add`; `lean_array_get_size` on an `Array`, a
  `List`, a one- or two-field structure: `Array.size`; `lean_string_push`
  with `@&` or a `UInt32`: `String.push`; `lean_array_push` with an extra
  argument or at `List β`: `Array.push`; `@[tagged_return]` on
  `lean_nat_add`; `lean_system_platform_nbits`; `lean_nat_dec_lt`;
  `lean_string_drop`, also the `@[export]` of Init's
  `String.Internal.dropImpl`, to which an extern of the program is not
  bound either: `String.Internal.drop`, review REB-14);
- `lean_decode_lossy_utf8`, a function of Lean's runtime whose
  declaration (`Lean.decodeLossyUTF8`) is in a module the program does not
  import: the message names the module (`Lean.Shell`), to import if that
  declaration is public (reviews REB-03, REB-10; it is not:
  `RtExternPrivate`); but not for `l2r_nat_repr` and `lean_natarr_push`,
  functions of lean2rr's own prelude that no module of Lean's library
  declares (review REB-07).
Native Lean compiles the program (`lean -c`); it would need C code for the
symbols to link.
-/

@[extern "rt_refused_opaque"]
opaque myOpaque : Nat → Nat

@[extern "rt_refused_axiom"]
axiom myAx : Nat → Nat

@[extern "rt_refused_nc"]
def nc (n : Nat) : Nat := n + Classical.choice ⟨0⟩

@[extern c inline "#1 * 2"]
opaque inl (a : UInt64) : UInt64

@[export rt_refused_triple]
def tripleImpl (n : Nat) : Nat := 3 * n

@[extern "rt_refused_triple"]
opaque tripleS : String → String

@[export rt_refused_pos]
def posImpl (n : Nat) (_h : n > 0) : Nat := n - 1

@[extern "rt_refused_pos"]
opaque myPos (n : Nat) (h : n > 0) : Nat

@[extern "lean_string_push"]
opaque pushB (s : @& String) (c : Char) : String

@[extern "lean_array_get_size"]
opaque sizeListO : @& List Nat → Nat

@[extern "lean_array_push"]
opaque pushExtraO (a : Array Nat) (v w : Nat) : Array Nat

@[extern "lean_nat_add", tagged_return]
opaque addTO : Nat → Nat → Nat

structure Two where
  val : Array Nat
  tag : Nat

@[extern "lean_array_get_size"]
opaque sizeTwoO : @& Two → Nat

structure Wrap where
  val : Array Nat

@[extern "lean_array_get_size"]
opaque sizeWrapO : @& Wrap → Nat

@[extern "lean_string_push"]
opaque pushU (s : String) (c : UInt32) : String

@[extern "lean_nat_add"]
opaque myAddO : Nat → Nat → Nat

@[extern "lean_array_get_size"]
opaque sizeNatO (a : @& Array Nat) : Nat

@[extern "lean_array_push"]
opaque pushListO {β : Type} (a : Array (List β)) (v : List β) : Array (List β)

@[extern "lean_system_platform_nbits"]
opaque nbO : Unit → Nat

@[extern "lean_nat_dec_lt"]
opaque ltBO : Nat → Nat → Bool

@[extern "lean_string_drop"]
opaque myDropO (s : String) (n : Nat) : String

@[extern "lean_decode_lossy_utf8"]
opaque decodeLossy : @& ByteArray → String

@[extern "l2r_nat_repr"]
opaque myRepr : Nat → String

@[extern "lean_natarr_push"]
opaque np : Array Nat → Nat → Array Nat

def main : IO Unit := do
  IO.println (myOpaque 1, myAx 2, nc 3, inl 4)
  IO.println (tripleS "x", myPos 5 (by decide), pushB "a" 'b')
  IO.println (sizeListO [1], pushExtraO #[] 1 2, addTO 1 2, sizeTwoO ⟨#[], 0⟩)
  IO.println (sizeWrapO ⟨#[]⟩, pushU "a" 98, myDropO "hello" 2)
  IO.println (decodeLossy "a".toUTF8, myRepr 5, np #[1] 2)
  IO.println (myAddO 1 2, sizeNatO #[], pushListO #[[1]] [2], nbO (), ltBO 1 2)
