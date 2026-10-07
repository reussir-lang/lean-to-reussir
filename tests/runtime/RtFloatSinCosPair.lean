/-! Runtime test (lean-runtime's review HF-01): `Float.sin` and `Float.cos`
of one operand (bits from `NAME.args`), computed together and printed as
bits. Natively the C calls glibc's `sin` and `cos`, two calls. LLVM can make
a sine and a cosine of one operand in one basic block one call of glibc's
`sincos`, whose sine differs from `sin`'s at x = ±0x1.ad1fb54442d18p+0
(bits 4610228045947874584 and 13833600082802650392): `sin` gives
4607132368722284764, `sincos` 4607132368722284763 (and the negatives).
Each line computes the pair in another shape, each in a function of its
own: the pair of floats, the pair of their bits, and one scalar expression
(the exclusive or of the bits), where nothing is allocated between the two
calls. lean-runtime's `sin` and `cos` are never inlined (semantics-5), so
the calls stay two. Before, with lean-runtime 1d5d4d3, lean2rr inlined the
three functions into `main` and made one `sincos` call for all three
lines, which printed `sincos`'s sine. lean-runtime's case
`folding/sin_cos_one_operand`. -/

@[noinline] def floats (x : Float) : Float × Float := (Float.sin x, Float.cos x)

@[noinline] def bitsPair (x : Float) : UInt64 × UInt64 :=
  ((Float.sin x).toBits, (Float.cos x).toBits)

@[noinline] def bitsXor (x : Float) : UInt64 := (Float.sin x).toBits ^^^ (Float.cos x).toBits

def main (args : List String) : IO Unit := do
  for a in args do
    let x := Float.ofBits a.toNat!.toUInt64
    let (s, c) := floats x
    IO.println s!"{a} floats: {s.toBits} {c.toBits}"
    let (sb, cb) := bitsPair x
    IO.println s!"{a} bits: {sb} {cb}"
    IO.println s!"{a} xor: {bitsXor x}"
