import Std.Data.HashMap
import Std.Data.HashSet
/-! Runtime test: `Std.HashMap`/`Std.HashSet` (their iteration order follows
Lean's exact hash functions) and `hash` on common types. -/

structure P where
  x : Nat
  name : String
deriving Repr, BEq, Hashable

def main (args : List String) : IO Unit := do
  let k := args.length + 200
  let m : Std.HashMap String Nat := (List.range k).foldl (fun m i => m.insert s!"key{i}" (i * i)) {}
  let hm : Std.HashMap Nat String := (List.range 50).foldl (fun m i => m.insert (i * 1000003) (toString i)) {}
  let hp : Std.HashMap P Nat := (List.range 20).foldl (fun m i => m.insert { x := i, name := s!"n{i % 3}" } i) {}
  let s : Std.HashSet Int := Std.HashSet.ofList [3, -1, 4, -1, 5, -9, 2, 6, 5, 3, 5]
  IO.println s!"hashmap size {m.size} get {m.get? "key7"} {m.get? "nokey"} {m.getD "key199" 0} contains {m.contains "key5"}"
  IO.println s!"hashmap toList {m.toList.take 12}"
  IO.println s!"hashmap fold {m.fold (fun acc _ v => acc + v) 0} keys {m.keys.take 8}"
  IO.println s!"erase {(m.erase "key7" |>.erase "key8").size} {(m.erase "key7").get? "key7"}"
  IO.println s!"nat keys {hm.toList.take 10}"
  IO.println s!"struct keys {hp.toList.map (fun (p, v) => (p.x, p.name, v)) |>.take 10}"
  IO.println s!"hashset {s.size} {s.contains (-9)} {s.toList}"
  IO.println s!"hashes {hash "abc"} {hash ""} {hash "a longer string with more than eight bytes"} {hash 'x'} {hash (1, "x")} {hash [1, 2, 3]} {hash (some 5)} {hash #[1, 2]}"
  IO.println s!"more hashes {hash (-5 : Int)} {hash (2^70 : Int)} {hash (-(2^70) : Int)} {hash (2^64 : Nat)} {hash true} {hash ()} {hash (3.5 : Float).toBits}"
