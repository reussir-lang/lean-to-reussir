/-! Runtime test: big `Nat`s
(above 2^61, rcgmp's immediate range, and above 2^63) in a
closed term (`big`, a once-cell constant) and in a typed `Array Nat` (built
by `push`, read by `get!`), read again after other allocations. Both
cross generic prelude textures at `T = Nat` (`l2r_once_put/get`,
`l2r_array_push`, `l2r_view_take`), where Reussir renders a built-in
integer as its owned handle (local patch R2); with the raw handle and no
guard in lean2rr, the counts were wrong and the sums silently different
(review R1-01 of step D).
-/
def big : Nat := 2^70

def loop : Nat → Nat → Nat
  | 0, acc => acc
  | n+1, acc => loop n (acc + (big + n))

@[noinline] def mk (n : Nat) : Nat := 2^70 + n

def build : Nat → Array Nat → Array Nat
  | 0, a => a
  | n+1, a => build n (a.push (mk n))

def sumA (a : Array Nat) : Nat → Nat → Nat
  | 0, acc => acc
  | i+1, acc => sumA a i (acc + a[i]!)

def main : IO Unit := do
  IO.println (toString (loop 10000 0))
  let a := build 1000 #[]
  IO.println (toString (sumA a a.size 0))
  IO.println (toString (loop 1000 0))
  IO.println (toString (sumA a a.size 0))
