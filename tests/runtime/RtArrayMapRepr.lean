/-! Runtime test: `Array.map`, `mapM`, `mapIdx` and `mapFinIdx` whose
element representation changes (`Nat` to `Bool`, `UInt64` to `Nat`, `Nat`
to structures, options, closures, arrays, ...). lean2rr runs such a loop
over a source array and a new result array (translation plan §2.7). The
input is shared or unique, mapped in place or not, the mapping function
updates the element it receives, the monad exits early or throws. -/

structure P where
  a : Nat
  b : String
deriving Repr

inductive Dir | n | e | s | w deriving Repr, BEq

def ioMap (a : Array Nat) : IO (Array Bool) :=
  a.mapM fun i => do
    if i == 7 then IO.println "seven"
    if i == 1000 then throw (IO.userError "too big")
    return i % 2 == 0

def exMap (a : Array Nat) : Except String (Array UInt64) :=
  a.mapM fun i => if i > 100 then throw s!"big {i}" else pure (i.toUInt64 * 2)

def stMap (a : Array UInt64) : StateM Nat (Array Nat) :=
  a.mapM fun i => do modify (· + 1); return i.toNat + (← get)

def optMap (a : Array Nat) : Option (Array String) :=
  a.mapM fun i => if i == 13 then none else some (toString i)

/-- A generic map, instantiated at several pairs of types. -/
def gmap {α β : Type} (f : α → β) (a : Array α) : Array β := a.map f

def main (args : List String) : IO Unit := do
  let n := args.length + 12
  let a := Array.range n
  -- unique input, mapped to other scalar types
  IO.println (a.map (fun i => i % 3 == 0))
  IO.println ((Array.range n).map (fun i => (i * 7).toUInt8))
  IO.println ((Array.range n).map (fun i => i.toFloat / 2.0))
  -- shared input (still used afterwards)
  let b := a.map (fun i => P.mk i (toString (i * i)))
  IO.println (repr b)
  IO.println a
  IO.println (repr (a.map some))
  IO.println ((a.map (fun i => if i % 2 == 0 then Dir.n else Dir.w)).map (· == Dir.n))
  IO.println (a.mapIdx (fun j i => (i * j).toUInt16))
  IO.println (a.mapFinIdx (fun j i _ => s!"{j}:{i}"))
  -- big numbers through representation changes
  let big := (Array.range 5).map (fun i => 2 ^ (64 + i) + i)
  IO.println (big.map (fun x => (x % 1000).toUInt64))
  IO.println ((big.map (fun x => x.toUInt64)).map (fun u => u.toNat + 2 ^ 70))
  -- the mapping function updates the element it receives (unshared)
  let rows := (Array.range 4).map (fun i => Array.replicate i i)
  IO.println (rows.map (fun r => (r.push 1).size))
  IO.println (rows.map (fun r => (r.push 7).foldl (· + ·) 0 |>.toUInt8))
  -- closures and arrays as results
  let fs := a.map (fun i => fun (x : Nat) => x + i)
  IO.println ((fs.map (· 100)).foldl (· + ·) 0)
  IO.println ((a.map (fun i => #[i, i])).map Array.size)
  -- empty arrays
  IO.println ((#[] : Array Nat).map (· == 1))
  IO.println ((#[] : Array UInt64).map (·.toNat))
  -- monadic maps: IO (with output and an error), Except, StateM, Option
  IO.println (← ioMap a)
  try
    IO.println (← ioMap #[1, 7, 1000, 2])
  catch e => IO.println s!"caught {e}"
  IO.println (repr (exMap a))
  IO.println (repr (exMap #[1, 200, 3]))
  IO.println ((stMap (a.map (·.toUInt64))).run 5)
  IO.println (optMap a)
  IO.println (optMap #[1, 13, 2])
  -- generic code at several types
  IO.println (gmap (fun (i : Nat) => i.toUInt32) a)
  IO.println (gmap (fun (s : String) => s.length) #["a", "bb", "ccc"])
  IO.println (gmap (fun (u : UInt8) => u.toNat * 1000) #[1, 2, 255])
  -- maps in a loop, alternating representations
  let mut acc : Array Nat := Array.range 6
  for k in [0:50] do
    let bs := acc.map (fun x => (x + k) % 5 == 0)
    acc := bs.map (fun t => if t then k else 1)
  IO.println acc
