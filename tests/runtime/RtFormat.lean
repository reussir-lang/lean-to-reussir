/-! Runtime test: formatting and the list/option library: `Repr` of derived
structures and inductives (Std.Format layout at widths), `toString` of
standard containers, sorting, thunks, tasks, closures. -/

inductive Tree where
  | leaf
  | node (l : Tree) (k : Nat) (v : String) (r : Tree)
deriving Repr, Inhabited

def Tree.insert : Tree → Nat → String → Tree
  | .leaf, k, v => .node .leaf k v .leaf
  | .node l k' v' r, k, v =>
    if k < k' then .node (l.insert k v) k' v' r
    else if k' < k then .node l k' v' (r.insert k v)
    else .node l k v r

def Tree.toList : Tree → List (Nat × String)
  | .leaf => []
  | .node l k v r => l.toList ++ [(k, v)] ++ r.toList

structure Point where
  x : Int
  y : Float
  tag : Option String
  items : List Nat
deriving Repr

inductive Shape where
  | circle (r : Float)
  | rect (w h : Nat)
  | named (n : String) (s : Shape)
deriving Repr

def main (args : List String) : IO Unit := do
  let k := args.length + 30
  let t := (List.range k).foldl (fun t i => t.insert ((i * 17) % 31) s!"v{i}") Tree.leaf
  IO.println s!"tree {t.toList.take 8}"
  IO.println (repr (Tree.leaf.insert 2 "b" |>.insert 1 "a" |>.insert 3 "c"))
  let p : Point := { x := -3, y := 2.5, tag := some "hi", items := List.range 12 }
  IO.println (repr p)
  IO.println ((repr p).pretty 20)
  IO.println ((repr (List.range 40)).pretty 30)
  IO.println (repr [Shape.circle 1.0, .rect 2 3, .named "big" (.named "inner" (.rect 100 200))])
  IO.println s!"{(1, "a", 'c')} {(some (some 3) : Option (Option Nat))} {(none : Option Nat)} {[some 1, none]}"
  IO.println s!"{(Except.ok 5 : Except String Nat)} {(Except.error "bad" : Except String Nat)} {repr (Sum.inl 3 : Sum Nat String)}"
  IO.println s!"{#[[1], [2, 3]]} {[#[1.5]]} {repr 'x'} {repr "q\"uote\n\t"} {repr (3 : Int)} {repr (-3 : Int)} {repr [(-1 : Int)]}"
  let xs : List Nat := (List.range 50).map fun i => (i * 7919) % 97
  IO.println s!"mergeSort {xs.mergeSort} take {xs.take 10}"
  IO.println s!"list ops {xs.reverse.take 5} {xs.filter (· > 50) |>.length} {xs.filterMap (fun x => if x % 3 == 0 then some (x / 3) else none) |>.take 5}"
  IO.println s!"{xs.foldr (· + ·) 0} {xs.max?} {xs.min?} {xs.eraseDups.length} {xs.zip (List.range 3)} {List.replicate 3 'z'}"
  IO.println s!"{[(1, "a"), (2, "b")].lookup 2} {xs.find? (· > 90)} {xs.partition (· < 40) |>.1.length} {xs.span (· < 40) |>.1}"
  IO.println s!"{[1, 2, 3].flatMap fun x => [x, x * 10]} {[[1], [2, 3]].flatten} {List.range' 5 3} {(List.range 10).splitBy (fun a b => a / 3 == b / 3)}"
  IO.println s!"{"a-b-c".splitOn "-" |>.map String.length} {String.intercalate ", " ["x", "y", "z"]} {"abc".toList.map Char.toNat}"
  -- closures and partial application
  let adders := (List.range 5).map fun i => (· + i * 100)
  IO.println s!"closures {adders.map (· 1)} {(List.range 5).map (Nat.add 7)} {[Nat.succ, (· * 2)].map (· 21)}"
  let compose := fun (f g : Nat → Nat) x => f (g x)
  IO.println s!"compose {compose (· + 1) (· * 3) 5} {Function.comp (· - 1) (· * 2) 10}"
  -- thunks and tasks (pure)
  let th : Thunk Nat := Thunk.mk fun _ => (List.range 1000).foldl (· + ·) 0
  IO.println s!"thunk {th.get} {th.get} {(Thunk.pure 5).get}"
  let tasks := (List.range 4).map fun i => Task.spawn fun _ => (List.range (1000 * (i + 1))).foldl (· + ·) 0
  IO.println s!"tasks {tasks.map Task.get} {(Task.pure 7).get} {((Task.pure 3).map (· * 2)).get} {((Task.pure 3).bind fun x => Task.pure (x + 1)).get}"
  IO.println s!"nat formats {Nat.toDigits 2 37} {(255 : Nat).toSubscriptString} {(3 : Nat).toSuperscriptString} {String.ofList (Nat.toDigits 16 48879)}"
  IO.println s!"fixed-width {(-7 : Int8)} {(200 : UInt8)} {(65535 : UInt16)} {(-1 : Int64)} {(123 : USize)} {(3.25 : Float32)}"
