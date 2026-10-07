/-! Runtime test: reads and updates of arrays whose elements are boxed in a
heap cell (`Float`, a `UInt64` from 2^63, and one-field structures over
them, which lean2rr represents as their field) allocate no more than native
Lean (adversarial review of the dependent-type branch, finding 2).

- The default of `a[i]!` is a constant (`instInhabitedFloat`, a structure's
  `Inhabited` instance). Natively it is boxed once (`_boxed_const`); boxed
  at every read, it was a new 16-byte cell per read (n reads, n cells).
- `Array.modify` stores `unsafeCast ()` in the slot it updates, natively
  `box(0)`. Lowered as `0.0` and boxed, it was a second cell per update.
- A named constant or closed term (`pushu`), or a `UInt64` literal
  (`pushl`), pushed n times is boxed once natively. A `Float` literal
  written in the loop (`pushc`, `a.push 0.25`) is computed there, natively
  too, and boxed at each push: one cell per push on both sides.

Modes (each prints a checksum): `get` (`a[i]!` on an `Array Float`),
`getd` (`a.getD i 0.0`), `modify` (`a.modify i (· + 1.0)`), `set`
(`a.set! i (a[i]! + 1.0)`), `getw` (`a[i]!` on an array of a one-field
structure over `Float`), `getu` (`a[i]!` on an array of a one-field
structure over `UInt64`, whose default is from 2^63), `modw` (`modify` on
the `Float` structure), `pushc` (the literal `0.25` pushed n times: a
cell per push, as natively),
`pushu` (a constant `UInt64` from 2^63 pushed n times), `pushl` (a
`UInt64` literal from 2^63 pushed n times), `oob` (reads out
of bounds: the default, boxed once, is returned; each read panics), `zero`
(`unsafeCast ()` stored where Lean stores `box(0)`, read back at `Nat`,
`Bool`, `Option Nat` and `UInt32`: their zeros). Arguments: MODE N
(default: every mode, N = 100). The allocations of each mode at
two sizes are checked by tests/runtime/alloc-check.sh
(RtDepFloatArrayAlloc.alloc). -/

structure W where
  x : Float
  deriving Inhabited

structure U where
  v : UInt64

instance : Inhabited U := ⟨⟨(2 : UInt64) ^ 63 + 5⟩⟩

@[noinline] def fget (n : Nat) : Float := Id.run do
  let a : Array Float := Array.replicate n 0.5
  let mut s := 0.0
  for _ in [0:4] do
    for i in [0:n] do
      s := s + a[i]!
  return s

@[noinline] def fgetd (n : Nat) : Float := Id.run do
  let a : Array Float := Array.replicate n 0.5
  let mut s := 0.0
  for _ in [0:4] do
    for i in [0:n] do
      s := s + a.getD i 0.0
  return s

@[noinline] def fmodify (n : Nat) : Float := Id.run do
  let mut a : Array Float := Array.replicate n 0.5
  for _ in [0:4] do
    for i in [0:n] do
      a := a.modify i (· + 1.0)
  return a.foldl (· + ·) 0.0

@[noinline] def fset (n : Nat) : Float := Id.run do
  let mut a : Array Float := Array.replicate n 0.5
  for _ in [0:4] do
    for i in [0:n] do
      a := a.set! i (a[i]! + 1.0)
  return a.foldl (· + ·) 0.0

@[noinline] def getw (n : Nat) : Float := Id.run do
  let a : Array W := Array.replicate n ⟨0.5⟩
  let mut s := 0.0
  for _ in [0:4] do
    for i in [0:n] do
      s := s + a[i]!.x
  return s

@[noinline] def getu (n : Nat) : UInt64 := Id.run do
  let a : Array U := Array.replicate n ⟨7⟩
  let mut s : UInt64 := 0
  for _ in [0:4] do
    for i in [0:n] do
      s := s + a[i]!.v
  return s

@[noinline] def modw (n : Nat) : Float := Id.run do
  let mut a : Array W := Array.replicate n ⟨0.5⟩
  for _ in [0:4] do
    for i in [0:n] do
      a := a.modify i (fun w => ⟨w.x + 1.0⟩)
  return a.foldl (fun s w => s + w.x) 0.0

@[noinline] def pushc (n : Nat) : Float := Id.run do
  let mut a : Array Float := #[]
  for _ in [0:n] do
    a := a.push 0.25
  return a.foldl (· + ·) 0.0

@[noinline] def pushu (n : Nat) : UInt64 := Id.run do
  let mut a : Array UInt64 := #[]
  for _ in [0:n] do
    a := a.push ((2 : UInt64) ^ 63 + 3)
  return a.foldl (· + ·) 0

@[noinline] def pushl (n : Nat) : UInt64 := Id.run do
  let mut a : Array UInt64 := #[]
  for _ in [0:n] do
    a := a.push 9223372036854775811
  return a.foldl (· + ·) 0

/-- Reads past the end: each panics and gives the default. -/
@[noinline] def oob (n : Nat) : String := Id.run do
  let a : Array Float := Array.replicate n 0.5
  let w : Array W := Array.replicate n ⟨0.5⟩
  let u : Array U := Array.replicate n ⟨7⟩
  let mut s := 0.0
  let mut t : UInt64 := 0
  for i in [n:n + 3] do
    s := s + a[i]! + w[i]!.x
    t := t + u[i]!.v
  return s!"{s} {t}"

/-- `unsafeCast ()`: natively `box(0)` at the type. -/
unsafe def unitAsU {α : Type} [Inhabited α] : α := unsafeCast ()
@[implemented_by unitAsU, noinline] opaque unitAs {α : Type} [Inhabited α] : α

/-- Store a value in a generic array and read it back. -/
@[noinline] def viaArray {α : Type} [Inhabited α] (x : α) : α := (#[x] : Array α)[0]!

@[noinline] def zero (n : Nat) : String :=
  let a : Nat := viaArray (unitAs : Nat)
  let b : Bool := viaArray (unitAs : Bool)
  let c : Option Nat := viaArray (unitAs : Option Nat)
  let d : UInt32 := viaArray (unitAs : UInt32)
  s!"{a + n} {b} {c} {d}"

def run (mode : String) (n : Nat) : IO Unit :=
  match mode with
  | "get" => IO.println s!"get {fget n}"
  | "getd" => IO.println s!"getd {fgetd n}"
  | "modify" => IO.println s!"modify {fmodify n}"
  | "set" => IO.println s!"set {fset n}"
  | "getw" => IO.println s!"getw {getw n}"
  | "getu" => IO.println s!"getu {getu n}"
  | "modw" => IO.println s!"modw {modw n}"
  | "pushc" => IO.println s!"pushc {pushc n}"
  | "pushu" => IO.println s!"pushu {pushu n}"
  | "pushl" => IO.println s!"pushl {pushl n}"
  | "oob" => IO.println s!"oob {oob n}"
  | "zero" => IO.println s!"zero {zero n}"
  | _ => IO.println s!"unknown mode {mode}"

def main (args : List String) : IO Unit := do
  match args with
  | [mode, n] => run mode n.toNat!
  | _ =>
    for m in ["get", "getd", "modify", "set", "getw", "getu", "modw", "pushc", "pushu", "pushl", "oob", "zero"] do
      run m 100
