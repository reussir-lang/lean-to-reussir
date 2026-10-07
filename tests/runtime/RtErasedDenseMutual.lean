/-! Runtime test (review of d8027f5): a dense mutual block of eight
inductives, each with a constructor per member taking `Tj → List Tj →
Option Tj → Ti`, no function field, values pushed into arrays. Rule 4's
flow analysis asks whether such a type can hold a function value
(`mayHoldFn`); a search along every simple path through the block took
exponential time (over 10 minutes at eight members), a reachability with
one visited set is linear. -/
mutual
inductive T0 where
  | leaf : Nat → T0
  | c0 : T0 → List T0 → Option T0 → T0
  | c1 : T1 → List T1 → Option T1 → T0
  | c2 : T2 → List T2 → Option T2 → T0
  | c3 : T3 → List T3 → Option T3 → T0
  | c4 : T4 → List T4 → Option T4 → T0
  | c5 : T5 → List T5 → Option T5 → T0
  | c6 : T6 → List T6 → Option T6 → T0
  | c7 : T7 → List T7 → Option T7 → T0
inductive T1 where
  | leaf : Nat → T1
  | c0 : T0 → List T0 → Option T0 → T1
  | c1 : T1 → List T1 → Option T1 → T1
  | c2 : T2 → List T2 → Option T2 → T1
  | c3 : T3 → List T3 → Option T3 → T1
  | c4 : T4 → List T4 → Option T4 → T1
  | c5 : T5 → List T5 → Option T5 → T1
  | c6 : T6 → List T6 → Option T6 → T1
  | c7 : T7 → List T7 → Option T7 → T1
inductive T2 where
  | leaf : Nat → T2
  | c0 : T0 → List T0 → Option T0 → T2
  | c1 : T1 → List T1 → Option T1 → T2
  | c2 : T2 → List T2 → Option T2 → T2
  | c3 : T3 → List T3 → Option T3 → T2
  | c4 : T4 → List T4 → Option T4 → T2
  | c5 : T5 → List T5 → Option T5 → T2
  | c6 : T6 → List T6 → Option T6 → T2
  | c7 : T7 → List T7 → Option T7 → T2
inductive T3 where
  | leaf : Nat → T3
  | c0 : T0 → List T0 → Option T0 → T3
  | c1 : T1 → List T1 → Option T1 → T3
  | c2 : T2 → List T2 → Option T2 → T3
  | c3 : T3 → List T3 → Option T3 → T3
  | c4 : T4 → List T4 → Option T4 → T3
  | c5 : T5 → List T5 → Option T5 → T3
  | c6 : T6 → List T6 → Option T6 → T3
  | c7 : T7 → List T7 → Option T7 → T3
inductive T4 where
  | leaf : Nat → T4
  | c0 : T0 → List T0 → Option T0 → T4
  | c1 : T1 → List T1 → Option T1 → T4
  | c2 : T2 → List T2 → Option T2 → T4
  | c3 : T3 → List T3 → Option T3 → T4
  | c4 : T4 → List T4 → Option T4 → T4
  | c5 : T5 → List T5 → Option T5 → T4
  | c6 : T6 → List T6 → Option T6 → T4
  | c7 : T7 → List T7 → Option T7 → T4
inductive T5 where
  | leaf : Nat → T5
  | c0 : T0 → List T0 → Option T0 → T5
  | c1 : T1 → List T1 → Option T1 → T5
  | c2 : T2 → List T2 → Option T2 → T5
  | c3 : T3 → List T3 → Option T3 → T5
  | c4 : T4 → List T4 → Option T4 → T5
  | c5 : T5 → List T5 → Option T5 → T5
  | c6 : T6 → List T6 → Option T6 → T5
  | c7 : T7 → List T7 → Option T7 → T5
inductive T6 where
  | leaf : Nat → T6
  | c0 : T0 → List T0 → Option T0 → T6
  | c1 : T1 → List T1 → Option T1 → T6
  | c2 : T2 → List T2 → Option T2 → T6
  | c3 : T3 → List T3 → Option T3 → T6
  | c4 : T4 → List T4 → Option T4 → T6
  | c5 : T5 → List T5 → Option T5 → T6
  | c6 : T6 → List T6 → Option T6 → T6
  | c7 : T7 → List T7 → Option T7 → T6
inductive T7 where
  | leaf : Nat → T7
  | c0 : T0 → List T0 → Option T0 → T7
  | c1 : T1 → List T1 → Option T1 → T7
  | c2 : T2 → List T2 → Option T2 → T7
  | c3 : T3 → List T3 → Option T3 → T7
  | c4 : T4 → List T4 → Option T4 → T7
  | c5 : T5 → List T5 → Option T5 → T7
  | c6 : T6 → List T6 → Option T6 → T7
  | c7 : T7 → List T7 → Option T7 → T7
end

def T0.size : T0 → Nat
  | .leaf n => n
  | _ => 1
def T1.size : T1 → Nat
  | .leaf n => n
  | _ => 1
def T2.size : T2 → Nat
  | .leaf n => n
  | _ => 1
def T3.size : T3 → Nat
  | .leaf n => n
  | _ => 1
def T4.size : T4 → Nat
  | .leaf n => n
  | _ => 1
def T5.size : T5 → Nat
  | .leaf n => n
  | _ => 1
def T6.size : T6 → Nat
  | .leaf n => n
  | _ => 1
def T7.size : T7 → Nat
  | .leaf n => n
  | _ => 1

def main (args : List String) : IO Unit := do
  let n := args.length
  let a0 : Array T0 := #[(.leaf n : T0), .c1 (.leaf 1) [] none]
  IO.println (a0.foldl (fun acc x => acc + x.size) 0)
  let a1 : Array T1 := #[(.leaf n : T1), .c2 (.leaf 1) [] none]
  IO.println (a1.foldl (fun acc x => acc + x.size) 0)
  let a2 : Array T2 := #[(.leaf n : T2), .c3 (.leaf 1) [] none]
  IO.println (a2.foldl (fun acc x => acc + x.size) 0)
  let a3 : Array T3 := #[(.leaf n : T3), .c4 (.leaf 1) [] none]
  IO.println (a3.foldl (fun acc x => acc + x.size) 0)
  let a4 : Array T4 := #[(.leaf n : T4), .c5 (.leaf 1) [] none]
  IO.println (a4.foldl (fun acc x => acc + x.size) 0)
  let a5 : Array T5 := #[(.leaf n : T5), .c6 (.leaf 1) [] none]
  IO.println (a5.foldl (fun acc x => acc + x.size) 0)
  let a6 : Array T6 := #[(.leaf n : T6), .c7 (.leaf 1) [] none]
  IO.println (a6.foldl (fun acc x => acc + x.size) 0)
  let a7 : Array T7 := #[(.leaf n : T7), .c0 (.leaf 1) [] none]
  IO.println (a7.foldl (fun acc x => acc + x.size) 0)
