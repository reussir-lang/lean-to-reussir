import Std.Tactic.BVDecide

/-!
Functions whose compiled calls a `@[csimp]` theorem replaces by an
`@[extern]` definition of the program, as lean-zip's `UInt64.ctz` →
`UInt64.ctzFast` (`Zip/Native/Wide.lean`, whose definitions are copied
here): Lean's compiled code calls the extern, so lean2rr runs its Lean
definition, the fast reference (natively the C code in
`RtExternCsimp.ffi.c`). Direct calls, function values, and a call in another
extern's definition.
-/

def UInt64.ctz (x : UInt64) : UInt64 := ⟨BitVec.ctz x.toBitVec⟩

@[extern "rt_csimp_ctz64"]
def UInt64.ctzFast (x : UInt64) : UInt64 :=
  if x == 0 then 64 else
    let s5 : UInt64 := if x &&& 0xFFFFFFFF == 0 then 32 else 0
    let x5 := x >>> s5
    let s4 : UInt64 := if x5 &&& 0xFFFF == 0 then 16 else 0
    let x4 := x5 >>> s4
    let s3 : UInt64 := if x4 &&& 0xFF == 0 then 8 else 0
    let x3 := x4 >>> s3
    let s2 : UInt64 := if x3 &&& 0xF == 0 then 4 else 0
    let x2 := x3 >>> s2
    let s1 : UInt64 := if x2 &&& 0x3 == 0 then 2 else 0
    let x1 := x2 >>> s1
    let s0 : UInt64 := if x1 &&& 0x1 == 0 then 1 else 0
    s5 + s4 + s3 + s2 + s1 + s0

@[csimp] theorem UInt64.ctz_eq_ctzFast : UInt64.ctz = UInt64.ctzFast := by
  funext x
  unfold UInt64.ctz UInt64.ctzFast
  bv_decide

def dbl (n : Nat) : Nat := 2 * n

@[extern "rt_csimp_dbl"]
def dblFast (n : Nat) : Nat := n + n

@[csimp] theorem dbl_eq_dblFast : dbl = dblFast := by
  funext n
  simp only [dbl, dblFast]
  omega

@[extern "rt_csimp_low_bit"]
def lowBit (x : UInt64) : UInt64 := if x == 0 then 0 else (1 : UInt64) <<< x.ctz

def main : IO Unit := do
  IO.println ((List.range 12).map fun i => ((((i.toUInt64 % 5) + 1) <<< (i.toUInt64 * 5) : UInt64)).ctz)
  IO.println ((0 : UInt64).ctz, (0x8000000000000000 : UInt64).ctz)
  IO.println ([6, 40, 0].map UInt64.ctz)
  IO.println (dbl 21, [1, 2, 2 ^ 70].map dbl)
  IO.println ([12, 0, 0x50000].map lowBit)
