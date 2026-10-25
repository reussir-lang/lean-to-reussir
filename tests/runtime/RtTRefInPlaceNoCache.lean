/-! Runtime test (typed references, clean step B2): `RtTRefInPlace` with
the optional pass `placeholder-cache` off (`RtTRefInPlaceNoCache.opts`).
A typed cell's `take` stores a placeholder of the element type; where that
placeholder would allocate (a record without a field-less constructor, an
array, a string outside the literal cache), typed cells build it once in
their own once-cell (`cellZero`), so the update stays in place and
allocates nothing per step also without `placeholder-cache`.
`RtTRefInPlaceNoCache.alloc` checks that lean2rr's allocations and bytes
grow no faster than native's from n = 2000 to n = 8000 for each kind (a
placeholder built at each `take` added one allocation per step: arr +12058
and pt +12060 allocations against native's +60). Arguments: a kind or
`all`, and n. -/

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
