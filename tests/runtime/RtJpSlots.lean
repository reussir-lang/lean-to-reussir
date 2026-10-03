/-! Runtime test: loops through outlined join points (J4 state machines)
whose join points carry values of many types: with the optional pass
`state-machines`, the values a jump carries go in parameter slots of the
state machine's function and the other slots get placeholders. An array
updated in place stays unshared across the jumps (`dbgTraceIfShared` prints
nothing); a type whose placeholder would not be a finite value (`W`, whose
first constructor holds an `Empty`) is still carried correctly; strings,
structures, closures, floats, characters and options travel through the
loop. -/

inductive W where
  | bad (e : Empty)
  | ok (n : Nat)

@[noinline] def wv : W → Nat
  | .ok n => n
  | .bad e => nomatch e

structure Tally where
  s : String
  k : Nat

@[noinline] partial def loop (i n : Nat) (arr : Array Nat) (s : String) (w : W) (f : Nat → Nat)
    (acc : Tally) (fl : Float) (c : Char) (o : Option String) : IO (Array Nat × String × Nat × Float × Option String) := do
  if i ≥ n then return (arr, s, wv w + acc.k, fl, o)
  let mut arr := arr
  let mut s := s
  if i % 3 == 0 then IO.print (if s.length > 1000 then "!" else "")
  let a1 := dbgTraceIfShared "arr shared 1" arr
  arr := a1.set! (i % a1.size) i
  if i % 5 == 0 then IO.print (if acc.s.length > 100000 then "!" else "")
  s := s.push c
  if i % 7 == 0 then IO.print (if fl < 0 then "!" else "")
  let w := match w with
    | .ok m => W.ok (m + 1)
    | .bad e => nomatch e
  if (i * 3) % 11 == 4 then
    return ← loop (i + 1) n arr (if s.length > 20 then "" else s) w f { acc with k := f acc.k } (fl + 0.5) c
      (if i % 2 == 0 then some s else o)
  if i % 4 == 1 then IO.print (if c == 'q' then "!" else "")
  let a2 := dbgTraceIfShared "arr shared 2" arr
  arr := a2.set! ((i + 1) % a2.size) (f i)
  if i % 9 == 2 then IO.print (match o with | some t => if t.length > 1000 then "!" else "" | none => "")
  let acc := if i % 13 == 0 then { acc with s := acc.s ++ "x" } else acc
  loop (i + 1) n arr (if s.length > 30 then "" else s) w f acc (fl * 1.0001) c o

def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 100000
  let arr := Array.range (n % 7 + 10)
  let (a, s, k, fl, o) ← loop 0 n arr "" (.ok 3) (· * 3 % 1000) { s := "", k := 1 } 1.0 'z' none
  IO.println s!"{a} {s} {k} {fl} {o}"
