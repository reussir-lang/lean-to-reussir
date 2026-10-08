/-! Runtime test (compact scalar arrays, plan "Tests": unique arrays): a
unique array of 1000 elements of one storage kind updated n times in place
by `set!`, `uget`/`uset` (a read of the element before its write), a
swap, a `push` followed by a `pop`, and every 50 steps a same-kind `map`.
Natively none of these copies the array; `RtCArrInPlace.alloc` checks
that lean2rr's allocations and bytes grow no faster than native's from
n = 2000 to n = 8000 for each kind (a copy per step would add 8000 bytes
or more per step). The values are made by fixed-width arithmetic, not by
big `Nat`s (whose allocations are not what this test measures).
Arguments: a kind (`u8`, `bool`, `u16`, `u32`, `char`, `u64`, `usize`,
`f32`, `f64`, or `all`) and n. -/

def mix (h x : UInt64) : UInt64 := (h ^^^ x) * 1099511628211

@[inline] def steps {α : Type} [Inhabited α] (mk : Nat → α) (f : α → α) (bits : α → UInt64)
    (n : Nat) : UInt64 := Id.run do
  let mut a : Array α := (Array.range 1000).map mk
  for i in [0:n] do
    let j := i % a.size
    a := a.set! j (mk i)
    if h : j.toUSize.toNat < a.size then
      a := a.uset j.toUSize (f (a.uget j.toUSize h)) h
    a := a.swapIfInBounds j (a.size - 1 - j)
    a := (a.push (mk (i + 1))).pop
    if i % 50 == 0 then
      a := a.map f
  return a.foldl (fun h x => mix h (bits x)) a.size.toUInt64

def run (kind : String) (n : Nat) : Option UInt64 :=
  match kind with
  | "u8" => some <| steps (fun i => (i * 37 + 1).toUInt8) (· + 3) (·.toUInt64) n
  | "bool" => some <| steps (fun i => i % 3 == 1) not (fun b => if b then 1 else 0) n
  | "u16" => some <| steps (fun i => (i * 7919).toUInt16) (· * 5) (·.toUInt64) n
  | "u32" => some <| steps (fun i => (i * 2654435761).toUInt32) (· + 0x80000000) (·.toUInt64) n
  | "char" => some <| steps (fun i => Char.ofNat (0x4E00 + i % 1000)) (fun c => Char.ofNat (c.toNat ^^^ 1))
      (·.val.toUInt64) n
  | "u64" => some <| steps (fun i => i.toUInt64 * 0x9E3779B97F4A7C15 ||| 0x8000000000000000) (· * 3) id n
  | "usize" => some <| steps (fun i => i.toUSize * 0x9E3779B97F4A7C15) (· + 7) (·.toUInt64) n
  | "f32" => some <| steps (fun i => (i.toFloat / 9.0).toFloat32) (· * 1.5) (·.toBits.toUInt64) n
  | "f64" => some <| steps (fun i => i.toFloat / 9.0 - 3.0) (fun x => x * 1.5 - 1.0) Float.toBits n
  | _ => none

def main (args : List String) : IO Unit := do
  let kind := args.head?.getD "all"
  let n := (args[1]? >>= String.toNat?).getD 3000
  let kinds := if kind == "all" then ["u8", "bool", "u16", "u32", "char", "u64", "usize", "f32", "f64"] else [kind]
  for k in kinds do
    match run k n with
    | some d => IO.println s!"{k} {n} {d}"
    | none => IO.println s!"unknown kind {k}"
