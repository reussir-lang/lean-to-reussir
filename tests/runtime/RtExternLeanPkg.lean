import Lean

/-!
A program extern re-declaring, with the same type, an extern of the `Lean`
package (`Lean.Level.mkData`, Lean's C++, which lean2rr's runtime does not
implement): an extern of the program is never bound to Lean's runtime, so
its own Lean definition runs (natively Lean's C++ runs; the definition
computes the same word). Review RV8E-05.
-/

@[extern "lean_level_mk_data"]
def myLevelData (h : UInt64) (depth : Nat := 0) (hasMVar hasParam : Bool := false) : Lean.Level.Data :=
  h.toUInt32.toUInt64 + hasMVar.toUInt64 <<< 32 + hasParam.toUInt64 <<< 33 + depth.toUInt64 <<< 40

def main : IO Unit := do
  let d : UInt64 := myLevelData 5 3 true false
  IO.println d
  let d2 : UInt64 := myLevelData 0xFFFFFFFFFF 7 false true
  IO.println d2
