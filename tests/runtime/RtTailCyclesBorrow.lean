/-! Runtime test: a tail call between the declarations of a cycle of tail
calls (one state machine, translation plan §5.6) that passes an owned file
handle to a parameter the callee borrows, in a program that creates
resources (plan §5.8, "Borrowing"). Natively the caller releases the handle
after the call returns (Lean's borrow inference keeps tail calls only for a
declaration's calls of itself), so the call is no tail call, and every
handle stays open, its line in its buffer, until the chain returns: each
read of the file sees nothing. A tail call that re-entered the state
machine instead would release the handle at its last use inside the
callee, and the later reads would see the lines. From the review of
fix-sm-mutual (2026-10-21).
- `xa`/`xb`: a cycle of two, each passing a new handle;
- `za`/`zb`/`zc`: a cycle of three;
- `pa`/`pb`: a cycle of two whose every other call passes on the handle
  it borrows (a tail call, natively too, which enters the state machine),
  so that in the state machine's arms, of both declarations, a call that
  passes a new handle stays a call. -/

mutual
@[noinline] partial def xa (h : IO.FS.Handle) (path : System.FilePath) (n : Nat) : IO Nat := do
  h.putStrLn s!"a {n}"
  let s ← IO.FS.readFile path
  IO.println s!"xa {n} sees {s.length}"
  if n == 0 then return s.length
  let h2 ← IO.FS.Handle.mk path .append
  xb h2 path (n - 1)
@[noinline] partial def xb (h : IO.FS.Handle) (path : System.FilePath) (n : Nat) : IO Nat := do
  h.putStrLn s!"b {n}"
  let s ← IO.FS.readFile path
  IO.println s!"xb {n} sees {s.length}"
  if n == 0 then return s.length
  let h2 ← IO.FS.Handle.mk path .append
  xa h2 path (n - 1)
end

mutual
@[noinline] partial def za (h : IO.FS.Handle) (path : System.FilePath) (n : Nat) : IO Nat := do
  h.putStrLn s!"a {n}"
  let s ← IO.FS.readFile path
  IO.println s!"za {n} sees {s.length}"
  if n == 0 then return s.length
  let h2 ← IO.FS.Handle.mk path .append
  if n % 2 == 0 then zb h2 path (n - 1) else zc h2 path (n - 1)
@[noinline] partial def zb (h : IO.FS.Handle) (path : System.FilePath) (n : Nat) : IO Nat := do
  h.putStrLn s!"b {n}"
  let s ← IO.FS.readFile path
  IO.println s!"zb {n} sees {s.length}"
  if n == 0 then return s.length
  let h2 ← IO.FS.Handle.mk path .append
  zc h2 path (n - 1)
@[noinline] partial def zc (h : IO.FS.Handle) (path : System.FilePath) (n : Nat) : IO Nat := do
  h.putStrLn s!"c {n}"
  let s ← IO.FS.readFile path
  IO.println s!"zc {n} sees {s.length}"
  if n == 0 then return s.length
  let h2 ← IO.FS.Handle.mk path .append
  if n % 3 == 0 then za h2 path (n - 1) else zb h2 path (n - 1)
end

mutual
@[noinline] partial def pa (h : IO.FS.Handle) (path : System.FilePath) (n : Nat) (fresh : Bool) : IO Nat := do
  h.putStrLn s!"a {n}"
  let s ← IO.FS.readFile path
  IO.println s!"pa {n} sees {s.length}"
  if n == 0 then return s.length
  if fresh then
    let h2 ← IO.FS.Handle.mk path .append
    pb h2 path (n - 1) false
  else pb h path (n - 1) true
@[noinline] partial def pb (h : IO.FS.Handle) (path : System.FilePath) (n : Nat) (fresh : Bool) : IO Nat := do
  h.putStrLn s!"b {n}"
  let s ← IO.FS.readFile path
  IO.println s!"pb {n} sees {s.length}"
  if n == 0 then return s.length
  if fresh then
    let h2 ← IO.FS.Handle.mk path .append
    pa h2 path (n - 1) false
  else pa h path (n - 1) true
end

def main : IO Unit := do
  let px : System.FilePath := "rttailcyclesborrow-x.txt"
  IO.FS.writeFile px ""
  let h ← IO.FS.Handle.mk px .append
  let r ← xa h px 4
  IO.println s!"x {r}, the file afterwards: {(← IO.FS.readFile px).length} bytes"
  let pz : System.FilePath := "rttailcyclesborrow-z.txt"
  IO.FS.writeFile pz ""
  let h ← IO.FS.Handle.mk pz .append
  let r ← za h pz 7
  IO.println s!"z {r}, the file afterwards: {(← IO.FS.readFile pz).length} bytes"
  for (name, start) in [("pa", true), ("pb", false)] do
    let pp : System.FilePath := s!"rttailcyclesborrow-{name}.txt"
    IO.FS.writeFile pp ""
    let h ← IO.FS.Handle.mk pp .append
    let r ← if start then pa h pp 6 false else pb h pp 6 false
    IO.println s!"{name} {r}, the file afterwards: {(← IO.FS.readFile pp).length} bytes"
