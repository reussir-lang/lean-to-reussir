/-! Runtime test: `Float.cbrt` and `Float32.cbrt` are the C library's `cbrt`
and `cbrtf`, bit for bit. A Rust executable statically links
`compiler_builtins`' own `cbrt`/`cbrtf` (correctly rounded), which differ
from glibc's by 1-2 ulps on about half the doubles: cbrt 2.0 and 27.0, the
smallest subnormal, 0.1 and the 2-ulp inputs below all differ.
The program uses no other libm function, so nothing else makes the
executable depend on libm.so.6 (where a lookup through the global symbol
table, `dlsym(RTLD_DEFAULT, "cbrt")`, finds nothing and fell back to Rust's
copy). From the round-9 runtime inventory (fix-r9-misc). -/

-- Inputs as bit patterns: ±0, ±inf, NaNs, subnormals, the smallest normals,
-- near powers of two, perfect cubes, ordinary and large values, and inputs
-- where a correctly rounded cbrt differs from glibc's.
def d64 : Array UInt64 := #[
  0x0000000000000000, 0x8000000000000000, 0x7ff0000000000000, 0xfff0000000000000,
  0x7ff8000000000000, 0xfff8000000000000, 0x7ff8000000000123,
  0x0000000000000001, 0x8000000000000001, 0x0000000000000003, 0x00000000deadbeef,
  0x0008000000000000, 0x000fffffffffffff, 0x800fffffffffffff,
  0x0010000000000000, 0x8010000000000000, 0x0020000000000000,
  0x3ff0000000000000, 0x3ff0000000000001, 0x3fefffffffffffff,
  0x4000000000000000, 0x4000000000000001, 0x3fffffffffffffff,
  0x4020000000000000, 0x4020000000000001, 0x401fffffffffffff,
  0x3fc0000000000000, 0xc000000000000000, 0xc000000000000001, 0x7fe0000000000000,
  0x403b000000000000, 0xc03b000000000000, 0x408f400000000000, 0x400b000000000000,
  0x3fb999999999999a, 0x4008000000000000, 0x400921fb54442d18, 0xbfe0000000000000,
  0x7fefffffffffffff, 0xffefffffffffffff, 0x7e37e43c8800759c, 0x7fe1ccf385ebc8a0,
  0x97101dce4e7bfb79, 0x9ad2e144d6e8f2cf, 0xddaa4e85b0d6e28b, 0x8f8ea9d349428d8e,
  0x08f474ffb8e8ab15, 0x2ead854756d71f03, 0x0e1fc49bd63b809e, 0xfc5639b16b714b4f,
  0xb92199e83f5a101f, 0xc5765079fc5d43ff, 0x353cfc387dfae6b8, 0xa32edabf5585bd75]

def d32 : Array UInt32 := #[
  0x00000000, 0x80000000, 0x7f800000, 0xff800000, 0x7fc00000, 0xffc00000, 0x7fc00123,
  0x00000001, 0x80000001, 0x00000003, 0x00400000, 0x007fffff, 0x807fffff,
  0x00800000, 0x80800000,
  0x3f800000, 0x3f800001, 0x3f7fffff, 0x40000000, 0x40000001, 0x3fffffff,
  0x41000000, 0x41000001, 0x40ffffff, 0x3e000000, 0xc0000000, 0x7f000000,
  0x41d80000, 0xc1d80000, 0x447a0000, 0x40580000, 0x3dcccccd, 0x40490fdb,
  0x7f7fffff, 0xff7fffff, 0x7149f2ca,
  0x2ead8547, 0x0f1a50d5, 0xbc3a5b41, 0x6f0f3414, 0x7110b726, 0x5703572b,
  0x28a1e239, 0xf088256e, 0x7f30634d, 0xaa19ef48, 0x01640cfd, 0x3df4865f]

def main : IO Unit := do
  for b in d64 do
    IO.println s!"d {b}: {(Float.cbrt (Float.ofBits b)).toBits}"
  for b in d32 do
    IO.println s!"f {b}: {(Float32.cbrt (Float32.ofBits b)).toBits}"
  -- 2000 pseudo-random bit patterns (a 64-bit LCG; its high half for
  -- Float32), hashed.
  let mut s : UInt64 := 1
  let mut h : UInt64 := 0
  let mut h32 : UInt64 := 0
  for _ in [0:2000] do
    s := s * 6364136223846793005 + 1442695040888963407
    let hi : UInt32 := (s >>> 32).toUInt32
    let r32 : UInt32 := (Float32.cbrt (Float32.ofBits hi)).toBits
    h := h * 1000003 + (Float.cbrt (Float.ofBits s)).toBits
    h32 := h32 * 1000003 + r32.toUInt64
  IO.println s!"sweep {h} {h32}"
