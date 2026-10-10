/-! Runtime test: immediates in a `Box` read through `unsafeCast` at a
type held as an immediate (hunt HBOX2-01). The values are lists' heads, so
each is read from a box. Natively a boxed word read at `Bool` is
`(uint8_t)lean_unbox(x)`: 256 and 512 are `false`. At an enumeration it is
the index truncated to the enumeration's storage width (`u8`), then Lean's
`switch`, whose last alternative is its default: 256 is `C3.a`, 3 and 258
are `C3.c`. At an inductive whose last constructor has no fields it is
`lean_obj_tag`, again with the last alternative as the default: 5 is `T.c`.
lean2rr's typed casts read words so (`ofWord`), and now its unboxing does
too, in a program that casts. Before, a `Bool` was any nonzero word
(`bools TTTTF`), an enumeration's index was not masked (`c3 ccccb`), and a
word past `T`'s last constructor panicked (unreachable code). -/

inductive C3 | a | b | c

def c3s : C3 → String | .a => "a" | .b => "b" | .c => "c"

inductive T where
  | a (n : Nat)
  | b
  | c

def T.s : T → String | .a n => s!"a{n}" | .b => "b" | .c => "c"

@[noinline] unsafe def asBools (xs : List Nat) : List Bool := unsafeCast xs
@[noinline] unsafe def asC3 (xs : List Nat) : List C3 := unsafeCast xs
@[noinline] unsafe def asU8 (xs : List Nat) : List UInt8 := unsafeCast xs
@[noinline] unsafe def asT (n : Nat) : T := unsafeCast n
@[noinline] unsafe def asTs (ns : List Nat) : List T := unsafeCast ns

@[noinline] def showB : List Bool → String
  | [] => ""
  | b :: r => (if b then "T" else "F") ++ showB r

@[noinline] def showC : List C3 → String
  | [] => ""
  | c :: r => c3s c ++ showC r

unsafe def main (args : List String) : IO Unit := do
  let k := args.length
  let ns : List Nat := [256 + k, 512 + k, 257 + k, 1 + k, 0 + k]
  IO.println s!"bools {showB (asBools ns)}"
  IO.println s!"u8s {asU8 ns}"
  IO.println s!"c3 {showC (asC3 [256 + k, 3 + k, 258 + k, 2 + k, 1 + k])}"
  IO.println s!"typed {(asT (5 + k)).s} {(asT (1 + k)).s} {(asT (2 + k)).s}"
  IO.println s!"boxed {(asTs [1 + k, 2 + k]).map T.s}"
  IO.println s!"boxed {(asTs [5 + k, 3 + k, 1 + k]).map T.s}"
