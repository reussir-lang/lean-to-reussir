/-! Runtime test (a bug hunt of the names lean2rr recognizes, 2026-10-27):
an enumeration named `Foo._l2r_ptrkind` next to an inductive `Foo`, both in
arrays. The whole-program check of the compact and typed arrays keeps the
storage kinds and the pointer kinds in one cache: storage kinds by the
inductive's name, pointer kinds by `ArrayKinds.ptrKindCacheKey`, which was
`Foo._l2r_ptrkind`, the program's enumeration's name, so the two shared an
entry: with the enumeration's storage kind (`u8`) cached first (here
`main` makes the enumeration's array first), `Foo` got the pointer kind
`u8`, and `Array Foo` lost its
typed kind `I:Foo` (stored as an array of boxes; the output was still
native's). Now the key ends in a number, which no declared name does; the
`.l2r-debug` file checks that `I:Foo` is on. -/

inductive Foo where
  | a (n : Nat)
  | b (s : String)

inductive Foo._l2r_ptrkind where
  | x | y | z

def Foo.show : Foo → String
  | .a n => s!"a{n}"
  | .b s => s!"b{s}"

def k2s : Foo._l2r_ptrkind → String
  | .x => "x"
  | .y => "y"
  | .z => "z"

@[noinline] def mkFoos (n : Nat) : Array Foo := Id.run do
  let mut arr := #[]
  for i in [0:n] do
    arr := arr.push (if i % 2 == 0 then .a i else .b (toString (i * 3)))
  return arr

@[noinline] def mkKs (n : Nat) : Array Foo._l2r_ptrkind := Id.run do
  let mut arr := #[]
  for i in [0:n] do
    arr := arr.push (match i % 3 with | 0 => .x | 1 => .y | _ => .z)
  return arr

def main (args : List String) : IO Unit := do
  let n := args.length + 6
  let ks := mkKs n
  let fs := mkFoos n
  IO.println (fs.foldl (fun acc f => acc ++ f.show ++ ",") "")
  IO.println (ks.foldl (fun acc k => acc ++ k2s k) "")
  IO.println s!"{fs.size} {ks.size}"
