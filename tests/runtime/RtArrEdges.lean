/-! Runtime test: array edges. DArrEdge: `extract` with reversed and
out-of-bounds bounds, pop/reverse/back on 0 and 1 elements, `insertIdx!`/
`eraseIdx!` panics, `get!` defaults per element type, `emptyWithCapacity 0/1`
pushes, ByteArray `get!`/`set!`/`extract`, 60 `copySlice` argument
combinations, FloatArray -0.0, `replicate 0`, `qsort` of 0/1 elements. DGrow:
70000 pushes on `Array Nat` (with bigs)/`Array Int`/`Array String`/ByteArray/
FloatArray/String with snapshots at block boundaries (1..65535), every
snapshot then updated (copy on write), shrink to 30000 and regrow. DConstMut:
top-level constants of 12 container kinds updated by callers and in loops:
the constants never change.
From the round-7 review, area D (rv7/rtdata), checks DArrEdge, DGrow and
DConstMut. -/

namespace DArrEdge
-- from rv7/rtdata/DArrEdge.lean
-- Array operations at sizes 0/1 and capacity boundaries, reversed extract
-- bounds, panicking insert/erase, ByteArray/FloatArray edge operations.
def main : IO Unit := do
  let e : Array Nat := #[]
  let one : Array Nat := #[2^64]
  IO.println s!"{e.extract 3 1} {one.extract 1 0} {one.extract 0 5} {(#[1,2,3,4] : Array Nat).extract 3 1} {(#[1,2,3] : Array Nat).extract 2 2}"
  IO.println s!"{e.pop} {one.pop} {e.reverse} {one.reverse} {e.back?} {one.back!} {e.swapIfInBounds 0 0}"
  IO.println s!"{(#[1,2,3] : Array Nat).insertIdx! 3 9} {(#[1,2,3] : Array Nat).insertIdx! 0 9}"
  IO.println s!"{(#[1,2,3] : Array Nat).insertIdx! 4 9}"
  IO.println s!"{(#[1,2,3] : Array Nat).eraseIdx! 2} {(#[1,2,3] : Array Nat).eraseIdx! 3}"
  IO.println s!"{(#["a","b"] : Array String).eraseIdx! 5} {(#["a"] : Array String).insertIdx! 7 "z"}"
  IO.println s!"{e[0]!} {one[1]!} {(#["s"] : Array String)[3]!} {(#[1.5] : Array Float)[2]!} {(#[some 1] : Array (Option Nat))[4]!}"
  let c := Array.emptyWithCapacity (α := Nat) 0
  let c2 := (c.push 1).push 2
  IO.println s!"{c} {c2} {(Array.emptyWithCapacity (α := String) 1).push "x" |>.push "y"}"
  let b := ByteArray.empty
  IO.println s!"{b.toList} {(b.push 1).toList} {b.get! 0} {(b.set! 0 5).toList} {(ByteArray.mk #[1,2,3]).extract 2 1 |>.toList} {(ByteArray.mk #[1,2,3]).extract 1 9 |>.toList}"
  let src := ByteArray.mk #[1,2,3,4,5]
  let dst := ByteArray.mk #[9,9,9]
  for so in [0, 2, 5, 6] do
    for d in [0, 1, 3, 4, 10] do
      for l in [0, 2, 9] do
        IO.print s!" {(src.copySlice so dst d l).toList}"
  IO.println ""
  let fa := FloatArray.empty
  IO.println s!"{fa.toList} {fa.get! 3} {(fa.push 1.5).toList} {(fa.set! 0 2.0).toList} {((FloatArray.mk #[1.0, 2.0]).set! 1 (-0.0)).toList}"
  IO.println s!"{(Array.range 0)} {(Array.replicate 0 'a')} {(Array.replicate 3 "q")} {(List.replicate 2 (2^64)).toArray}"
  IO.println s!"{(#[3,1,2] : Array Nat).qsort (· < ·)} {(#[] : Array Nat).qsort (· < ·)} {(#[5] : Array Nat).qsort (· < ·)}"
end DArrEdge

namespace DGrow
-- from rv7/rtdata/DGrow.lean
-- Growth past block-size steps with snapshots kept and then updated:
-- capacity bookkeeping of tagged Nat/Int arrays, generic arrays, byte
-- arrays, float arrays and strings.
def digN (a : Array Nat) : UInt64 := a.foldl (fun h x => mixHash h (hash x)) 7
def digI (a : Array Int) : UInt64 := a.foldl (fun h x => mixHash h (hash x)) 7
def digS (a : Array String) : UInt64 := a.foldl (fun h x => mixHash h (hash x)) 7
def digB (a : ByteArray) : UInt64 := a.hash
def digF (a : FloatArray) : UInt64 := a.foldl (fun h x => mixHash h x.toBits) 7

def main : IO Unit := do
  let mut an : Array Nat := #[]
  let mut ai : Array Int := Array.emptyWithCapacity 3
  let mut as : Array String := #[]
  let mut ab : ByteArray := ByteArray.empty
  let mut af : FloatArray := FloatArray.empty
  let mut st : String := ""
  let mut snN : Array (Array Nat) := #[]
  let mut snI : Array (Array Int) := #[]
  let mut snS : Array (Array String) := #[]
  let mut snB : Array ByteArray := #[]
  let mut snF : Array FloatArray := #[]
  let mut snT : Array String := #[]
  for i in [0:70000] do
    let big := i % 97 == 0
    an := an.push (if big then 2^64 + i else i)
    ai := ai.push (if big then -(2^63 : Int) - i else (i : Int) - 5)
    if i % 7 == 0 then as := as.push s!"v{i}"
    ab := ab.push i.toUInt8
    if i % 3 == 0 then af := af.push i.toFloat
    st := st.push (if i % 5 == 0 then 'é' else 'a')
    if i == 1 || i == 3 || i == 4 || i == 5 || i == 8 || i == 63 || i == 64 || i == 500 || i == 511 || i == 512 || i == 513 || i == 4095 || i == 8191 || i == 65535 then
      snN := snN.push an; snI := snI.push ai; snS := snS.push as; snB := snB.push ab; snF := snF.push af; snT := snT.push st
  IO.println s!"final {digN an} {digI ai} {digS as} {digB ab} {digF af} {hash st} {st.length}"
  -- update every snapshot (copy-on-write), then the originals in place
  for k in [0:snN.size] do
    let a := (snN[k]!.set! 0 12345).push 77 |>.pop |>.push (2^70)
    let b := (snI[k]!.set! 0 (-12345)).push (-77)
    let c := (snS[k]!.push "x").modify 0 (· ++ "!")
    let d := (snB[k]!.set! 0 9).push 1
    let e := (snF[k]!.push 0.5)
    let f := (snT[k]!.push '😀').set ⟨0⟩ 'Z'
    IO.println s!"{k} {a.size} {digN a} {digN snN[k]!} {b.size} {digI b} {digI snI[k]!} {digS c} {digS snS[k]!} {digB d} {digB snB[k]!} {digF e} {digF snF[k]!} {hash f} {hash snT[k]!} {f.length}"
  -- shrink and regrow in place
  for _ in [0:40000] do
    an := an.pop; ai := ai.pop; ab := ab.extract 0 (ab.size - 1)
  for i in [0:50000] do
    an := an.push i; ai := ai.push (-(i : Int))
  IO.println s!"after {an.size} {digN an} {ai.size} {digI ai} {ab.size} {digB ab}"
  let r := an.reverse
  let e := an.extract 100 70000
  let q := an ++ r
  IO.println s!"{digN r} {digN e} {q.size} {digN q} {(ai.extract 5 9)} {an.extract 9 5}"
end DGrow

namespace DConstMut
-- from rv7/rtdata/DConstMut.lean
-- Top-level constants and literals of every container kind, updated by
-- callers: the constant must never change.
def cNat : Array Nat := #[1, 2, 3, 2^70]
def cInt : Array Int := #[-1, 2, -(2^70)]
def cStr : Array String := #["a", "b"]
def cFlt : Array Float := #[1.5, 2.5]
def cU8 : Array UInt8 := #[1, 2, 3]
def cBytes : ByteArray := ByteArray.mk #[1, 2, 3]
def cFA : FloatArray := ⟨#[1.0, 2.0]⟩
def cS : String := "héllo"
def cNest : Array (Array Nat) := #[#[1], #[2, 3]]
def cPair : Array (Nat × String) := #[(1, "x"), (2, "y")]
def cOpt : Array (Option Nat) := #[some 1, none]
def cEnum : Array Ordering := #[.lt, .gt]

@[noinline] def bump (a : Array Nat) (i : Nat) : Array Nat := (a.set! i (a[i]! + 100)).push i
@[noinline] def bumpI (a : Array Int) (i : Nat) : Array Int := (a.set! i (a[i]! - 100)).push (-i)
@[noinline] def bumpS (a : Array String) (i : Nat) : Array String := (a.modify i (· ++ "!")).push "z"
@[noinline] def bumpF (a : Array Float) (i : Nat) : Array Float := (a.modify i (· * 2)).swapIfInBounds 0 1
@[noinline] def bumpU (a : Array UInt8) (i : Nat) : Array UInt8 := (a.set! i 99).reverse
@[noinline] def bumpB (a : ByteArray) (i : Nat) : ByteArray := (a.set! i 77).push 5
@[noinline] def bumpFA (a : FloatArray) (i : Nat) : FloatArray := (a.set! i 9.5).push 3.5
@[noinline] def bumpStr (s : String) (i : Nat) : String := (String.Pos.Raw.set s ⟨i⟩ 'X').push '!'
@[noinline] def bumpN (a : Array (Array Nat)) (i : Nat) : Array (Array Nat) := a.modify i (·.push 7)
@[noinline] def bumpP (a : Array (Nat × String)) (i : Nat) : Array (Nat × String) := (a.modify i (fun (n, s) => (n + 1, s ++ "?"))).pop
@[noinline] def bumpO (a : Array (Option Nat)) (i : Nat) : Array (Option Nat) := a.set! i (some 42)
@[noinline] def bumpE (a : Array Ordering) (i : Nat) : Array Ordering := a.set! i .eq

def main : IO Unit := do
  for i in [0:2] do
    IO.println s!"{bump cNat i} {bumpI cInt i} {bumpS cStr i} {bumpF cFlt i} {bumpU cU8 i} {(bumpB cBytes i).toList} {(bumpFA cFA i).toList} {bumpStr cS i} {bumpN cNest i} {bumpP cPair i} {bumpO cOpt i} {(bumpE cEnum i).map (·.ctorIdx)}"
    let lit := #[10, 20, 30]
    let x := lit.push 40
    let y := lit.push 50
    let lit2 : Array String := #["p", "q"]
    let z := lit2.set! 0 "P"
    IO.println s!"{x} {y} {lit} {z} {lit2}"
  IO.println s!"{cNat} {cInt} {cStr} {cFlt} {cU8} {cBytes.toList} {cFA.toList} {cS} {cNest} {cPair} {cOpt} {cEnum.map (·.ctorIdx)}"
  -- a loop that updates a copy of a constant in place many times
  let mut a := cNat
  let mut s := cS
  let mut b := cBytes
  for k in [0:1000] do
    a := a.set! (k % 4) k
    s := s.push 'x'
    b := b.set! (k % 3) k.toUInt8
  IO.println s!"{a} {s.length} {b.toList} {cNat} {cS} {cBytes.toList}"
end DConstMut

def main : IO Unit := do
  IO.println "=== DArrEdge"
  DArrEdge.main
  IO.println "=== DGrow"
  DGrow.main
  IO.println "=== DConstMut"
  DConstMut.main
