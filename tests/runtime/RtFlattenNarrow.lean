/-! Runtime test: optimization `flatten-structs` with narrow fields. The
tuple of a flattened result keeps a `Bool`, `UInt8`, `UInt16`, `UInt32` or
`Char` in a whole word and has no member for a `Unit` (`tupleMemberTy` in
LowerBase.lean): every value comes back unchanged, the largest ones too,
through results that a recursive function returns again as they are
(`walk`, `check`, `grow`) or rebuilds (`walk`'s `{ r with n := … }`). -/
structure Narrow where
  n : Nat
  b : Bool
  u8 : UInt8
  u16 : UInt16
  u32 : UInt32
  c : Char
  u : Unit

@[noinline] def leaf (k : Nat) : Option Narrow :=
  if k % 7 == 3 then none
  else some { n := k, b := k % 2 == 0, u8 := k.toUInt8 + 250, u16 := k.toUInt16 + 65530,
              u32 := k.toUInt32 + 4294967290, c := Char.ofNat (0x10FFFF - k), u := () }

@[noinline] def walk : Nat → Nat → Option Narrow
  | 0, k => leaf k
  | i + 1, k =>
    match walk i (k + 1) with
    | some r => if r.n > 4 then some r else some { r with n := r.n + 10, b := !r.b }
    | none => none

/-- Not a tail call: the result of the call is returned as it is. -/
@[noinline] def check : List Nat → Except String Unit
  | [] => .ok ()
  | x :: xs => do
    if x > 1000 then throw s!"big {x}"
    let r ← check xs
    pure r

/-- A state and an error together (the shape of Unionfind's monad): the
result is an `Except` with a `Bool` and the state. -/
@[noinline] def grow : Nat → Array UInt8 → Except String Bool × Array UInt8
  | 0, a => (.ok (a.size % 2 == 0), a)
  | i + 1, a =>
    if a.size > 300 then (.error "full", a)
    else
      match grow i (a.push (255 - i.toUInt8)) with
      | (.ok b, a') => if i % 3 == 0 then (.ok (!b), a') else (.ok b, a')
      | r => r

/-- A structure result, returned again as it is or rebuilt. -/
@[noinline] def bump : Nat → Narrow → Narrow
  | 0, r => r
  | i + 1, r =>
    let r' := bump i { r with n := r.n + 1 }
    if i % 2 == 0 then r' else { r' with b := !r'.b, u8 := r'.u8 + 1, u16 := r'.u16 - 1, c := 'é' }

structure Pk where
  c : Char
  w : UInt16
  x : UInt8
  y : UInt32
  t : Bool

/-- A structure result read field by field, returned again as it is. -/
@[noinline] def pk : Nat → Pk
  | 0 => { c := Char.ofNat 0x10FFFF, w := 65535, x := 255, y := 4294967295, t := true }
  | i + 1 =>
    let p := pk i
    if i % 2 == 0 then p
    else { c := Char.ofNat (p.c.toNat - 1), w := p.w - 1, x := p.x - 1, y := p.y - 1, t := !p.t }

def render (o : Option Narrow) : String :=
  match o with
  | some r => s!"some n={r.n} b={r.b} u8={r.u8} u16={r.u16} u32={r.u32} c={r.c.toNat} u={r.u == ()}"
  | none => "none"

def main (args : List String) : IO Unit := do
  let k := (args.head?.bind String.toNat?).getD 0
  for i in [0:6] do
    IO.println s!"walk {i} {k}: {render (walk i k)}"
  for i in [0:4] do
    match leaf (k + i) with
    | some r => IO.println s!"bump {i}: {render (some (bump i r))}"
    | none => IO.println s!"bump {i}: none"
  for i in [0:5] do
    let p := pk (i + k)
    IO.println s!"pk {i}: {p.c.toNat} {p.w} {p.x} {p.y} {p.t}"
  for xs in [[1, 2, 3], [5, 2000, 7], []] do
    IO.println s!"check {xs}: {match check xs with | .ok () => "ok" | .error e => e}"
  for n in [0, 5, 6, 400] do
    let (r, a) := grow n #[]
    IO.println s!"grow {n}: {match r with | .ok b => s!"ok {b}" | .error e => e} size={a.size} last={a.back?}"
