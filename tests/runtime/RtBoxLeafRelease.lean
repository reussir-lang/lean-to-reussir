/-! Runtime test (review of the runtime's speed items): leaf payloads
(records and enums of scalars, `any::LEAF_BIT`: released directly, also
inside a free) and other payloads in boxes, released outside a free (an
array set, a pop, a reference set) and inside one (a list freed). -/

structure P where
  x : UInt64
  y : Float
  z : UInt8
  deriving Inhabited

inductive E where
  | a (n : UInt32)
  | b (f : Float) (g : UInt16)
  | c

structure Q (α : Type) where
  p : α
  n : Nat

@[noinline] def mkP (i : Nat) : P := ⟨i.toUInt64 * 7, i.toFloat, i.toUInt8⟩
@[noinline] def mkE (i : Nat) : E := if i % 3 == 0 then .a i.toUInt32 else if i % 3 == 1 then .b i.toFloat i.toUInt16 else .c

def main (args : List String) : IO Unit := do
  let n := args.head!.toNat!
  let mut acc : UInt64 := 0
  -- Array P: set (last ref of old element outside a free), pop
  let mut arr : Array P := #[]
  for i in [0:n] do arr := arr.push (mkP i)
  for i in [0:n] do arr := arr.set! i (mkP (i + 1))
  for _ in [0:n / 2] do
    acc := acc + arr.back!.x
    arr := arr.pop
  -- List E freed as a whole (inside Reussir's free)
  let l : List E := (List.range n).map mkE
  acc := acc + l.length.toUInt64
  -- Option (Q P) through a reference
  let r ← IO.mkRef (none : Option (Q P))
  for i in [0:n] do
    r.set (some ⟨mkP i, i⟩)
  acc := acc + ((← r.get).map (·.p.x)).getD 0
  -- List (Q E) built and dropped per round
  for i in [0:10] do
    let qs : List (Q E) := (List.range n).map fun j => ⟨mkE (i + j), j⟩
    acc := acc + qs.length.toUInt64
  IO.println s!"acc {acc} {arr.size}"
