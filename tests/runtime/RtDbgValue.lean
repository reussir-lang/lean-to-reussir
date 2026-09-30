/-! Runtime test: externs implemented by generic Reussir functions of the
prelude (`dbgTrace`, `dbgTraceIfShared`, `dbgSleep`, `panic`) at value
types, including those that runtime containers store in a wrapper (`Nat`,
`Int`, an enumeration, a closure): `Nat`, big `Nat`, `Int`, `Float`,
`UInt64`, `Bool`, an enumeration, a closure, a structure, `Option`,
`Unit`. -/

inductive Color | red | green | blue
  deriving Repr, Inhabited

structure P where
  a : Nat
  b : String
  deriving Repr, Inhabited

@[noinline] def slp (n : Nat) : Nat := dbgSleep 1 fun _ => n + 1
@[noinline] def slpI (n : Nat) : Int := dbgSleep 1 fun _ => Int.ofNat n - 10
@[noinline] def slpF (n : Nat) : Float := dbgSleep 1 fun _ => n.toFloat / 4
@[noinline] def slpFn (n : Nat) : Nat → Nat := dbgSleep 1 fun _ => fun x => x * n
@[noinline] def trC (n : Nat) : Color := dbgTrace s!"color {n}" fun _ => if n == 0 then .green else .blue
@[noinline] def trB (n : Nat) : Bool := dbgTrace "bool" fun _ => n == 0
@[noinline] def trU (n : Nat) : UInt64 := dbgTrace "u64" fun _ => n.toUInt64 + 7
@[noinline] def trBig (n : Nat) : Nat := dbgTrace "big" fun _ => 2 ^ 80 + n
@[noinline] def trP (n : Nat) : P := dbgTrace "struct" fun _ => ⟨n, s!"p{n}"⟩
@[noinline] def trO (n : Nat) : Option Nat := dbgTrace "option" fun _ => if n > 5 then none else some n
@[noinline] def trFn (n : Nat) : Nat → Nat := dbgTrace "closure" fun _ => fun x => x + n
@[noinline] def trUnit (n : Nat) : Unit := dbgTrace s!"unit {n}" fun _ => ()
@[noinline] def shared (n : Nat) : Nat := dbgTraceIfShared "shared nat" (n + 1)
@[noinline] def sharedP (p : P) : P := dbgTraceIfShared "shared struct" p
@[noinline] def pan (n : Nat) : Nat := if n > 100 then n else panic! "nat panic"
@[noinline] def panI (n : Nat) : Int := if n > 100 then 1 else panic! "int panic"
@[noinline] def panC (n : Nat) : Color := if n > 100 then .red else panic! "color panic"
@[noinline] def panP (n : Nat) : P := if n > 100 then default else panic! "struct panic"
@[noinline] def panFn (n : Nat) : Nat → Nat := if n > 100 then id else panic! "closure panic"

def main (args : List String) : IO Unit := do
  let n := args.length
  IO.println s!"sleep {slp n} {slpI n} {slpF n} {slpFn n 3}"
  IO.println s!"trace {repr (trC n)} {trB n} {trU n} {trBig n} {repr (trP n)} {trO n} {trFn n 5}"
  let _ := trUnit n
  IO.println s!"shared {shared n} {repr (sharedP ⟨n, "q"⟩)}"
  IO.println s!"panic {pan n} {panI n} {repr (panC n)} {repr (panP n)} {panFn n 4}"
