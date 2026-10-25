/-! Runtime test (typed references, clean step B2: values only the cell
holds): a reference of one cell kind updated n times by `modify` and
`modifyGet` (each `take`, then `set`), with a `get`, a `swap` and a `set`
every 100 steps. The value the cell holds is unique, so the update runs in
place natively: an array grows by `push` in place, a string by `push`, a
record's cell is reused for the new record. `RtTRefInPlace.alloc` checks
that lean2rr's allocations and bytes grow no faster than native's from
n = 2000 to n = 8000 for each kind (a copy of the array or string per step
would add n elements per step). Kinds: an array of `Nat` (`arr`), an array
of records (`arrpt`), a string (`str`), a structure (`pt`), a `List Nat`
(`list`), a `Nat` (`nat`), a `UInt32` (`u32`). Arguments: a kind or `all`,
and n. -/

structure Pt where
  n : Nat
  s : String
  deriving Inhabited

def mix (h x : UInt64) : UInt64 := (h ^^^ x) * 1099511628211

@[inline] def steps {α : Type} (init : α) (f : Nat → α → α) (bits : α → UInt64) (n : Nat) :
    IO UInt64 := do
  let r ← IO.mkRef init
  let mut h : UInt64 := 7
  for i in [0:n] do
    r.modify (f i)
    let b ← r.modifyGet fun x => (bits x, f (i + 1) x)
    h := mix h b
    if i % 100 == 0 then
      h := mix h (bits (← r.get))
      let old ← r.swap init
      r.set (f i old)
  return mix h (bits (← r.get))

def run (kind : String) (n : Nat) : IO (Option UInt64) :=
  match kind with
  | "arr" => some <$> steps (#[] : Array Nat) (fun i a => a.push i) (fun a => a.size.toUInt64) n
  | "arrpt" => some <$> steps (#[] : Array Pt) (fun i a => a.push ⟨i, "p"⟩)
      (fun a => ((a.back?.map Pt.n).getD 0).toUInt64) n
  | "str" => some <$> steps "" (fun i s => s.push (Char.ofNat (97 + i % 26))) (fun s => s.length.toUInt64) n
  | "pt" => some <$> steps ({ n := 0, s := "" } : Pt) (fun i p => { p with n := p.n + i })
      (fun p => p.n.toUInt64) n
  | "list" => some <$> steps ([] : List Nat) (fun i l => if l.length > 8 then [i] else i :: l)
      (fun l => l.foldl (fun h x => mix h x.toUInt64) 3) n
  | "nat" => some <$> steps 0 (fun i x => x + i * 2 ^ 40) (fun x => (x % 1000003).toUInt64) n
  | "u32" => some <$> steps (0 : UInt32) (fun i x => x * 31 + i.toUInt32) (·.toUInt64) n
  | _ => pure none

def main (args : List String) : IO Unit := do
  let kind := args.head?.getD "all"
  let n := (args[1]? >>= String.toNat?).getD 3000
  let kinds := if kind == "all" then ["arr", "arrpt", "str", "pt", "list", "nat", "u32"] else [kind]
  for k in kinds do
    match ← run k n with
    | some d => IO.println s!"{k} {n} {d}"
    | none => IO.println s!"unknown kind {k}"
