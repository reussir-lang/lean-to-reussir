/-! Runtime test: a position plus a character's UTF-8 size, `p + c.utf8Size`
(`String.Pos.Raw + Char`, `Char + String.Pos.Raw`, `String.map`'s step and a
program's own sum), which lean2rr's optimization `utf8-size-add` computes by
the prelude's `l2r_nat_add_utf8_size` (1 for an ASCII character in a branch
of its own, else 2, 3 or 4). Pinned: the characters at each edge of the
sizes (0, 0x7F, 0x80, 0x7FF, 0x800, 0xD7FF, 0xE000, 0xFFFF, 0x10000,
0x10FFFF), positions 0, small, near 2^60, 2^61, 2^63 and 2^64 and above
(big `Nat` values), `String.map` with functions that change the size of
each character (ASCII to 2, 3 and 4 bytes and back, which rebuilds the
string and moves the next position by the new character's size), over
empty, ASCII-only and mixed strings, and the other uses of
`Char.utf8Size` the pass leaves alone (a comparison, a subtraction, sizes
in a list). -/

@[noinline] def idx (n : Nat) : Nat := n
@[noinline] def ch (n : Nat) : Char := Char.ofNat (idx n)

/-- The characters at the edges of the UTF-8 sizes. -/
def edges : List Nat := [0, 1, 0x41, 0x7E, 0x7F, 0x80, 0x81, 0xE9, 0x7FF, 0x800, 0x801, 0xD7FF, 0xE000,
  0xFFFE, 0xFFFF, 0x10000, 0x10001, 0x1F600, 0x10FFFE, 0x10FFFF]

/-- The positions: small, around 2^60, 2^61, 2^63, 2^64 and beyond. -/
def positions : List Nat := [0, 1, 5, 2^60 - 1, 2^60, 2^61 - 5, 2^61 - 1, 2^61, 2^62, 2^63 - 4, 2^63 - 1, 2^63,
  2^64 - 2, 2^64 - 1, 2^64, 2^100 + 3]

@[noinline] def posPlus (p : Nat) (c : Char) : Nat := (String.Pos.Raw.mk p + c).byteIdx
@[noinline] def plusPos (c : Char) (p : Nat) : Nat := (c + String.Pos.Raw.mk p).byteIdx
@[noinline] def ownSum (p : Nat) (c : Char) : Nat := p + c.utf8Size
@[noinline] def ownSumL (p : Nat) (c : Char) : Nat := c.utf8Size + p
/-- Two sizes: `c.utf8Size + d.utf8Size`, then plus `p`. -/
@[noinline] def twoSizes (p : Nat) (c d : Char) : Nat := c.utf8Size + d.utf8Size + p
/-- The size used twice: in the sum and in a comparison (the size's `let`
stays). -/
@[noinline] def sumAndTest (p : Nat) (c : Char) : Nat × Bool := (p + c.utf8Size, c.utf8Size < 3)
/-- Uses the pass leaves alone. -/
@[noinline] def otherUses (p : Nat) (c : Char) : Nat × Bool × List Nat :=
  ((String.Pos.Raw.mk p - c).byteIdx, c.utf8Size == 4, [c.utf8Size, c.utf8Size * 10])

/-- A loop of `p + c` over the characters of a string, read at each step
(the next position depends on the character just read). -/
@[noinline] def walk (s : String) : List Nat := Id.run do
  let mut p : String.Pos.Raw := 0
  let mut out := []
  for _ in [:s.length + 1] do
    if p.byteIdx < s.utf8ByteSize then
      out := p.byteIdx :: out
      p := p + p.get s
  return (p.byteIdx :: out).reverse

/-- Size-changing maps: by the character's size class, to an edge of
another class. -/
@[noinline] def grow (c : Char) : Char :=
  if c.val ≤ 0x7F then ch 0x7FF else if c.val ≤ 0x7FF then ch 0xFFFF else if c.val ≤ 0xFFFF then ch 0x10FFFF else ch 0x7F
@[noinline] def shrink (c : Char) : Char :=
  if c.val ≤ 0x7F then ch 0x10000 else if c.val ≤ 0x7FF then ch 0x41 else if c.val ≤ 0xFFFF then ch 0x80 else ch 0x800
@[noinline] def rot (c : Char) : Char :=
  if 'a' ≤ c && c ≤ 'z' then Char.ofNat ((c.toNat - 'a'.toNat + 13) % 26 + 'a'.toNat) else c

def show' (s : String) : String :=
  s!"{s.length}/{s.utf8ByteSize}:{s.toList.map Char.toNat}"

def main : IO Unit := do
  for c in edges do
    let k := ch c
    IO.println s!"{c}: size {k.utf8Size} {posPlus 0 k} {plusPos k 7} {ownSum 3 k} {ownSumL 4 k} {twoSizes 1 k (ch 0x80)} {sumAndTest 9 k} {otherUses 2 k}"
  for p in positions do
    IO.println s!"{p}: {(edges.map fun c => posPlus (idx p) (ch c))} {plusPos (ch 0x10000) (idx p)} {ownSum (idx p) (ch 0x7FF)} {otherUses (idx p) (ch 0x800)}"
  let strs : List String := ["", "a", "hello, world", String.mk ['h', ch 0xE9, 'l', 'l', 'o'],
    String.mk [ch 0x7FF, ch 0x800, ch 0xFFFF], String.mk [ch 0x10000, 'x', ch 0x10FFFF], String.mk [ch 0x7F, ch 0x80], String.mk (edges.map ch)]
  for s in strs do
    IO.println s!"walk {walk s}"
    IO.println s!"map grow {show' (s.map grow)} shrink {show' (s.map shrink)} rot {show' (s.map rot)} upper {show' s.toUpper}"
    IO.println s!"map twice {show' ((s.map grow).map grow)} {show' ((s.map shrink).map grow)}"
  -- A long mixed string: `String.map` in place for ASCII, rebuilt when a size changes.
  let long := String.mk ((List.range 3000).map fun i => ch (if i % 7 == 0 then 0xE9 else if i % 11 == 0 then 0x1F600 else 0x61 + i % 26))
  IO.println s!"long {(long.map rot).utf8ByteSize} {(long.map grow).utf8ByteSize} {(long.map shrink).utf8ByteSize} {(walk long).length} {(walk long).getLast?}"
