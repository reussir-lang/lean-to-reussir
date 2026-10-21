/-! Runtime test (typed arrays, clean step B1: unique arrays): a unique
array of 1000 elements of one pointer kind updated n times in place by
`set!`, `uget`/`uset` (a read of the element before its write), a swap, a
`push` followed by a `pop`, a `modify`, and every 50 steps a same-type
`map`. Natively none of these copies the array; `RtTArrInPlace.alloc`
checks that lean2rr's allocations and bytes grow no faster than native's
from n = 2000 to n = 8000 for each kind (a copy per step would add 8000
bytes or more per step). Kinds: a structure (`pt`), an inductive with a
nullary constructor (`shape`), `Nat` (`nat`), `String` (`str`),
`Array Nat` (`arr`), `List Nat` (`list`). Arguments: a kind or `all`, and
n. -/

structure Pt where
  n : Nat
  f : Float
  deriving Inhabited

inductive Shape where
  | none
  | circle (r : Nat)
  | rect (w h : Nat)
  deriving Inhabited

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
    a := a.modify ((j * 7) % a.size) f
    if i % 50 == 0 then
      a := a.map f
  return a.foldl (fun h x => mix h (bits x)) a.size.toUInt64

def run (kind : String) (n : Nat) : Option UInt64 :=
  match kind with
  | "pt" => some <| steps (fun i => Pt.mk (i % 1000) (i.toFloat / 8.0)) (fun p => { p with n := p.n + 1 })
      (fun p => mix p.n.toUInt64 p.f.toBits) n
  | "shape" => some <| steps (fun i => if i % 3 == 0 then Shape.none else .circle (i % 997))
      (fun | .circle r => .rect r 2 | .rect w _ => .circle w | .none => .none)
      (fun | .none => 1 | .circle r => r.toUInt64 | .rect w h => mix w.toUInt64 h.toUInt64) n
  | "nat" => some <| steps (fun i => i * 7919) (· + 3) (·.toUInt64) n
  | "str" => some <| steps (fun i => if i % 2 == 0 then "even" else "odd") (fun s => if s.length > 5 then "x" else s ++ "!")
      (fun s => s.length.toUInt64) n
  | "arr" => some <| steps (fun i => #[i % 10]) (fun a => if a.size > 3 then #[a[0]!] else a.push 1)
      (fun a => a.foldl (fun h x => mix h x.toUInt64) 3) n
  | "list" => some <| steps (fun i => [i % 10]) (fun l => if l.length > 3 then [l.head!] else 1 :: l)
      (fun l => l.foldl (fun h x => mix h x.toUInt64) 3) n
  | _ => none

def main (args : List String) : IO Unit := do
  let kind := args.head?.getD "all"
  let n := (args[1]? >>= String.toNat?).getD 3000
  let kinds := if kind == "all" then ["pt", "shape", "nat", "str", "arr", "list"] else [kind]
  for k in kinds do
    match run k n with
    | some d => IO.println s!"{k} {n} {d}"
    | none => IO.println s!"unknown kind {k}"
