/-! Runtime test: a task, a thunk or a closure captures a value (a list, an
array, a structure with an array, a string), and its creator then updates the
same value where an update of a unique value happens in place (`map`, `set!`,
`push`, `modify`, a structure update, `String.set`). The capturer runs
afterwards (lean2rr runs a task when it is needed, plan §5.14) and must still
see the old value. Also `Task.map` over a captured array, and four tasks
sharing one list.
A coverage test from Crane's test corpus (Bloomberg's Rocq-to-C++ extractor,
whose regression tests document shapes that broke a typed, reference-counted
code generator); the code is new, the shapes are those of Crane's
tests/regression/nonatomic_rc_thread_race; tests/monadic/thread, parallel,
mutable_vector.
From the round-9 review, area crane (rv9/crane), program CrTask. -/

namespace RtTaskCaptureUpdate

@[noinline] def bumpAll (l : List Nat) : List Nat := l.map (· + 1000)
@[noinline] def sumL (l : List Nat) : Nat := l.foldl (· + ·) 0
structure S where
  a : Nat
  b : String
  c : Array Nat

def main (args : List String) : IO Unit := do
  let k := args.length
  let l := List.range (5 + k)
  let t := Task.spawn fun _ => sumL l
  let l2 := bumpAll l
  IO.println s!"listTask: {sumL l2} {t.get}"
  let arr := Array.range (6 + k)
  let ta := Task.spawn fun _ => arr.foldl (· + ·) 0
  let arr2 := (arr.set! 0 999).push 7
  IO.println s!"arrayTask: {arr2} {ta.get}"
  let s : S := ⟨k, "str", #[1, 2, 3]⟩
  let ts ← IO.asTask (pure s!"{s.a} {s.b} {s.c}")
  let s2 := { s with a := 77, b := s.b ++ "!", c := s.c.modify 1 (· * 50) }
  IO.println s!"structTask: {s2.a} {s2.b} {s2.c} {match ts.get with | .ok v => v | .error _ => "err"}"
  let str := String.mk ['a', 'b', 'c']
  let tstr := Task.spawn fun _ => str.length + (str.get 0).toNat
  let str2 := str.set 0 'Z' |>.push 'q'
  IO.println s!"stringTask: {str2} {tstr.get}"
  let arr3 := Array.range (4 + k)
  let th : Thunk Nat := Thunk.mk fun _ => arr3.foldl (· + ·) 0
  let arr4 := arr3.modify 0 (· + 100)
  IO.println s!"thunk: {arr4} {th.get}"
  let arr5 := Array.range (3 + k)
  let f := fun (i : Nat) => arr5[i]! * 10
  let arr6 := arr5.set! 1 55
  IO.println s!"closure: {arr6} {f 1}"
  let tm := t.map fun v => v + (arr.foldl (· + ·) 0)
  let arr7 := arr.set! 2 123
  IO.println s!"taskMap: {arr7} {tm.get}"
  let shared := List.range (50 + k)
  let workers := (List.range 4).map fun w => Task.spawn fun _ => Id.run do
    let mut s := 0
    for i in [0:2000] do s := s + sumL ((i + w) :: shared)
    return s
  IO.println s!"shared: {workers.map Task.get} {sumL shared}"

end RtTaskCaptureUpdate

def main (args : List String) : IO Unit := RtTaskCaptureUpdate.main args
