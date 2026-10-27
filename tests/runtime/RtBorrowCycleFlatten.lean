/-! Runtime test: cycles of tail calls that pass a new closure, thunk, task or
value of a type parameter (`lcAny` in mono code), which the callee stores in
a structure that a helper reads only partly, in a program that makes
resources (it opens a file), where lean2rr emulates Lean's borrowed
parameters. Natively the parameter is owned (a constructor's argument:
Lean's `ownArgsIfParam`), so each call is a tail call, and 10^6 steps run on
an 8 MB stack (`.pipe`). flatten-structs splits the helper (the structure
holds no resource), so in lean2rr's code the constructor is gone and Lean's
inference, run on that code, takes the parameter borrowed; keeping the
argument until the call returned (decided by type: a closure, thunk, task or
`lcAny` may hold a resource) made each call a call, and the stack overflowed
(review of the borrow emulation of closures; the `lcAny` cycle overflowed
before too). Now the borrow emulation keeps an argument only where the flow
analysis that guards flatten-structs finds that the parameter may hold a
resource (`keepsAt`, Lower/Borrow), and each cycle is a state machine. -/

structure S where
  c : Nat → Nat
  k : Nat

@[noinline] def g (s : S) : Nat := s.k + 1

mutual
@[noinline] partial def ping (c : Nat → Nat) (n : Nat) : Nat :=
  if n == 0 then g ⟨c, n⟩ else pong (fun x => x + n) (n - 1)
@[noinline] partial def pong (c : Nat → Nat) (n : Nat) : Nat :=
  if n == 0 then g ⟨c, n⟩ else ping (fun x => x + n) (n - 1)
end

structure T where
  t : Thunk Nat
  k : Nat

@[noinline] def gt (s : T) : Nat := s.k + 2

mutual
@[noinline] partial def tping (t : Thunk Nat) (n : Nat) : Nat :=
  if n == 0 then gt ⟨t, n⟩ else tpong (Thunk.mk fun _ => n) (n - 1)
@[noinline] partial def tpong (t : Thunk Nat) (n : Nat) : Nat :=
  if n == 0 then gt ⟨t, n⟩ else tping (Thunk.mk fun _ => n + 1) (n - 1)
end

structure K where
  t : Task Nat
  k : Nat

@[noinline] def gk (s : K) : Nat := s.k + 3

mutual
@[noinline] partial def kping (t : Task Nat) (n : Nat) : Nat :=
  if n == 0 then gk ⟨t, n⟩ else kpong (Task.pure n) (n - 1)
@[noinline] partial def kpong (t : Task Nat) (n : Nat) : Nat :=
  if n == 0 then gk ⟨t, n⟩ else kping (Task.pure (n + 1)) (n - 1)
end

/-- A type that depends on a value: a value of it is `lcAny` in mono code. -/
def F : Bool → Type
  | true => Nat
  | false => String

structure A where
  b : Bool
  c : F b
  k : Nat

@[noinline] def ga (s : A) : Nat := s.k + 4

mutual
@[noinline] partial def aping (b : Bool) (c : F b) (n : Nat) : Nat :=
  if n == 0 then ga ⟨b, c, n⟩ else apong true (show F true from n * 2) (n - 1)
@[noinline] partial def apong (b : Bool) (c : F b) (n : Nat) : Nat :=
  if n == 0 then ga ⟨b, c, n⟩ else aping true (show F true from n + 1) (n - 1)
end

def main : IO Unit := do
  let p : System.FilePath := "rtbcf.txt"
  let h ← IO.FS.Handle.mk p .write
  let n := 1000000
  h.putStrLn s!"closure {ping id n}"
  h.putStrLn s!"thunk {tping (Thunk.pure 0) n}"
  h.putStrLn s!"task {kping (Task.pure 0) n}"
  h.putStrLn s!"lcAny {aping false (show F false from "s") n}"
  h.flush
  IO.print (← IO.FS.readFile p)
  IO.FS.removeFile p
