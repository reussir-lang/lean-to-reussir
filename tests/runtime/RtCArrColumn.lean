/-! Runtime test (compact scalar arrays, plan "Tests": the dependent column
stays boxed): a column `data : Array ty.denote` whose element type
depends on a value, for every storage kind (as RtUniformUpdates does for
`Nat`, `String`, an enum and `Float`). In Lean's compiled code the field is
an `Array lcAny`; each branch of a match on `ty` uses it at one scalar type.
Per step: `push`, a read and a write of one element, `pop`, a swap; then a
`map` within the kind and a map to another kind (a column of `u8` becomes
one of `f64`, `u64` one of `u8`), folds, `extract`, `++`, `reverse`.
Beside the columns: typed arrays of the same kinds, one put into a column
(`ofTyped`) and one taken out of a column by a match and then updated by
typed code (`toTypedU64`, `toTypedF64`); typed arrays that never meet a
column. Under the plan the arrays that flow into or out of a column are
boxed and the others compact; the values must be the same. -/

inductive Col | r | g | b deriving Repr, BEq, Inhabited

inductive Ty | u8 | bool | col | u16 | u32 | char | u64 | usize | f32 | f64
  deriving BEq, Repr

@[reducible] def Ty.denote : Ty → Type
  | .u8 => UInt8 | .bool => Bool | .col => Col | .u16 => UInt16 | .u32 => UInt32
  | .char => Char | .u64 => UInt64 | .usize => USize | .f32 => Float32 | .f64 => Float

structure Column where
  ty : Ty
  data : Array ty.denote

instance : Inhabited Column := ⟨⟨.u8, #[]⟩⟩

def mix (h x : UInt64) : UInt64 := (h ^^^ x) * 1099511628211
def colIdx : Col → UInt64 | .r => 0 | .g => 1 | .b => 2

def Ty.bits : (t : Ty) → t.denote → UInt64
  | .u8, x => x.toUInt64
  | .bool, x => if x then 1 else 2
  | .col, x => colIdx x
  | .u16, x => x.toUInt64
  | .u32, x => x.toUInt64
  | .char, x => x.val.toUInt64
  | .u64, x => x
  | .usize, x => x.toUInt64
  | .f32, x => x.toBits.toUInt64
  | .f64, x => x.toBits

def Ty.show : (t : Ty) → t.denote → String
  | .u8, x => toString x
  | .bool, x => toString x
  | .col, x => reprStr x
  | .u16, x => toString x
  | .u32, x => toString x
  | .char, x => toString x.toNat
  | .u64, x => toString x
  | .usize, x => toString x
  | .f32, x => toString x
  | .f64, x => toString x

def Column.push (c : Column) (i : Nat) : Column :=
  match c with
  | ⟨.u8, d⟩ => ⟨.u8, d.push (i * 37 + 1).toUInt8⟩
  | ⟨.bool, d⟩ => ⟨.bool, d.push (i % 3 == 0)⟩
  | ⟨.col, d⟩ => ⟨.col, d.push (if i % 3 == 0 then .r else if i % 3 == 1 then .g else .b)⟩
  | ⟨.u16, d⟩ => ⟨.u16, d.push (i * 7919).toUInt16⟩
  | ⟨.u32, d⟩ => ⟨.u32, d.push (i * 2654435761).toUInt32⟩
  | ⟨.char, d⟩ => ⟨.char, d.push (Char.ofNat (0x1F600 + i % 80))⟩
  | ⟨.u64, d⟩ => ⟨.u64, d.push (i.toUInt64 * 0x9E3779B97F4A7C15 ||| 0x8000000000000000)⟩
  | ⟨.usize, d⟩ => ⟨.usize, d.push (i * 0x9E3779B97F4A7C15).toUSize⟩
  | ⟨.f32, d⟩ => ⟨.f32, d.push (if i % 11 == 3 then Float32.ofBits 0x7FC00000 else (i.toFloat / 3.0).toFloat32)⟩
  | ⟨.f64, d⟩ => ⟨.f64, d.push (if i % 13 == 2 then -0.0 else if i % 13 == 5 then 1.0 / 0.0 else i.toFloat / 7.0)⟩

-- A read and a write of one element, a pop and a swap per step.
def Column.touch (c : Column) (i : Nat) : Column :=
  match c with
  | ⟨.u8, d⟩ => ⟨.u8, (d.set! (i % d.size) (d[i % d.size]! + 1)).swapIfInBounds 0 1⟩
  | ⟨.bool, d⟩ => ⟨.bool, d.set! (i % d.size) (!d[i % d.size]!)⟩
  | ⟨.col, d⟩ => ⟨.col, (d.push d[i % d.size]!).pop⟩
  | ⟨.u16, d⟩ => ⟨.u16, d.set! (i % d.size) (d[(i + 1) % d.size]! * 3)⟩
  | ⟨.u32, d⟩ => ⟨.u32, (d.set! (i % d.size) (d[i % d.size]! ^^^ 0xFFFF0000)).swapIfInBounds (i % d.size) 0⟩
  | ⟨.char, d⟩ => ⟨.char, d.set! (i % d.size) (Char.ofNat (d[i % d.size]!.toNat + 1))⟩
  | ⟨.u64, d⟩ => ⟨.u64, d.set! (i % d.size) (d[i % d.size]! + 0x8000000000000000)⟩
  | ⟨.usize, d⟩ => ⟨.usize, (d.push (d[i % d.size]! * 3)).pop⟩
  | ⟨.f32, d⟩ => ⟨.f32, d.set! (i % d.size) (d[i % d.size]! * 2)⟩
  | ⟨.f64, d⟩ => ⟨.f64, d.set! (i % d.size) (d[i % d.size]! - 1.0)⟩

-- Maps within the kind, and to another kind for three kinds.
def Column.remap (c : Column) : Column :=
  match c with
  | ⟨.u8, d⟩ => ⟨.f64, d.map (·.toFloat / 2.0)⟩
  | ⟨.u64, d⟩ => ⟨.u8, d.map (·.toUInt8)⟩
  | ⟨.f64, d⟩ => ⟨.u64, d.map Float.toBits⟩
  | ⟨.bool, d⟩ => ⟨.bool, d.map not⟩
  | ⟨.u16, d⟩ => ⟨.u16, d.map (· + 1)⟩
  | ⟨.f32, d⟩ => ⟨.f32, d.map (fun x => -x)⟩
  | c => { c with data := c.data.reverse }

def Column.digest (c : Column) : UInt64 := c.data.foldl (fun h x => mix h (c.ty.bits x)) 7

def Column.summary (c : Column) : String :=
  s!"{reprStr c.ty} {c.data.size} {c.digest} {(c.data.toList.take 3).map c.ty.show} {(c.data.back?).map c.ty.show}"

def Column.extras (c : Column) : String :=
  let e := c.data.extract 1 4
  let both := c.data ++ e
  s!"{e.size} {both.size} {(⟨c.ty, both.reverse⟩ : Column).digest} {c.data.foldr (fun x h => mix h (c.ty.bits x)) 3}"

def ofTyped (a : Array UInt64) : Column := ⟨.u64, a⟩

def toTypedU64 (c : Column) : Array UInt64 :=
  match c with
  | ⟨.u64, d⟩ => d
  | _ => #[]

def toTypedF64 (c : Column) : Array Float :=
  match c with
  | ⟨.f64, d⟩ => d
  | _ => #[]

def dU64 (a : Array UInt64) : UInt64 := a.foldl mix 7
def dF (a : Array Float) : UInt64 := a.foldl (fun h x => mix h x.toBits) 7
-- digests of the arrays that never meet a column (no parameter shared with the others)
def aloneD8 (a : Array UInt8) : UInt64 := a.foldl (fun h x => mix h x.toUInt64) 11
def aloneDF (a : Array Float) : UInt64 := a.foldl (fun h x => mix h x.toBits) 11

def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 300
  let tys := #[Ty.u8, .bool, .col, .u16, .u32, .char, .u64, .usize, .f32, .f64]
  let mut cols : Array Column := tys.map fun t => ⟨t, #[]⟩
  for i in [0:n] do
    cols := cols.map (·.push i)
  for i in [0:n] do
    cols := cols.map (·.touch i)
  for c in cols do
    IO.println s!"col {c.summary}"
  for c in cols do
    IO.println s!"extras {reprStr c.ty} {c.extras}"
  let remapped := cols.map Column.remap
  for c in remapped do
    IO.println s!"remap {c.summary}"
  -- typed arrays beside the columns
  let typed : Array UInt64 := (Array.range n).map fun i => i.toUInt64 * 3 + 0xF000000000000000
  let fromTyped := (ofTyped typed).push n
  let back := toTypedU64 fromTyped
  let back2 := (back.push 1).map (· * 5)
  let fl := toTypedF64 cols[9]!
  let fl2 := (fl.map (· + 0.5)).push (0.0 / 0.0)
  let fl3 := toTypedF64 cols[0]!
  IO.println s!"typed {dU64 typed} {fromTyped.summary} {dU64 back} {dU64 back2} {dF fl} {dF fl2} {fl3.size}"
  -- typed arrays that never meet a column
  let mut alone8 : Array UInt8 := #[]
  let mut aloneF : Array Float := #[]
  for i in [0:n] do
    alone8 := alone8.push (i * 37 + 1).toUInt8
    aloneF := aloneF.push (i.toFloat / 7.0)
  IO.println s!"alone {aloneD8 alone8} {aloneDF aloneF} {aloneD8 (alone8.map (· + 3))} {aloneDF (aloneF.map (· * 2))}"
