/-!
The externs of the program and the functions their C symbols name
(translation plan §5.8, "Externs of the program"):
- The `@[export]` of another declaration: an extern binds to it (natively
  the very function its call is linked to) when its type is an instance of
  the definition's (the definition's universe parameters instantiated, and
  its result type, only, taken as `toMono` takes it: a trivial structure is
  its single relevant field) and the two have one compiled signature (an
  owned argument may meet a borrowed parameter, not the reverse): `triple`
  binds to `tripleImpl`, the `opaque` `mk1 : Nat → Nat` to `mkPos`, which
  returns a `{m : Nat // m > 0}`. `tripleB` borrows its argument, which the
  `@[export]` function takes owned, and `pos1` takes a `Nat` where
  `posImpl` takes a `{n : Nat // n > 0}` (no identification on a
  parameter): their bindings fail, their bodies run (lean2rr warns,
  `RtExternStub`).
- A symbol of Lean's runtime library: an extern of the program is never
  bound to Lean's runtime (the owner's decision of 2026-10-04); its Lean
  definition runs (without one it is refused, naming the library's
  declaration to call instead, `RtExternRefused`). Natively the runtime's
  function runs; the definitions here compute the same: `myAddBody`
  (`lean_nat_add`, also as a function value), `pushB` (`@&` where
  `String.push` takes the string owned), `pushCode` (a `UInt32` for the
  `Char`), `sizeNat`, `getNat` and `pushNat2` (polymorphic runtime
  functions at `Array Nat`), `sizeWrap` (a one-field structure around the
  array), `addT` (`@[tagged_return]`), `pushStr`; `sizeList` and `sizeTwo`
  only on a path that does not run (natively the C call reads a `List` or
  a two-field structure as an array).
`RtExternBind.l2r-log` checks which run their Lean definition.
-/

@[extern "lean_nat_add"]
def myAddBody (a b : Nat) : Nat := a + b

@[extern "lean_string_push"]
def pushB (s : @& String) (c : Char) : String := s.push c

@[extern "lean_string_push"]
def pushCode (s : String) (c : UInt32) : String := s.push (Char.ofNat c.toNat)

@[export rt_bind_triple]
def tripleImpl (n : Nat) : Nat := 3 * n

@[extern "rt_bind_triple"]
opaque triple : Nat → Nat

@[extern "rt_bind_triple"]
def tripleB (n : @& Nat) : Nat := 3 * n

@[extern "lean_array_get_size"]
def sizeNat (a : @& Array Nat) : Nat := a.size

@[extern "lean_array_get"]
def getNat [Inhabited Nat] (a : @& Array Nat) (i : @& Nat) : Nat := a[i]!

@[extern "lean_array_push"]
def pushNat2 (a : Array Nat) (v : Nat) : Array Nat := a.push v

@[extern "lean_array_get_size"]
def sizeList (l : @& List Nat) : Nat := l.length

@[extern "lean_nat_add", tagged_return]
def addT (a b : Nat) : Nat := a + b

@[extern "lean_array_push"]
def pushStr (a : Array String) (v : String) : Array String := a.push v

structure Wrap where
  val : Array Nat

structure Two where
  val : Array Nat
  tag : Nat

@[extern "lean_array_get_size"]
def sizeWrap (w : @& Wrap) : Nat := w.val.size

@[extern "lean_array_get_size"]
def sizeTwo (t : @& Two) : Nat := t.val.size + t.tag

@[export rt_bind_pos]
def posImpl (n : {n : Nat // n > 0}) : Nat := n.val + 1

@[extern "rt_bind_pos"]
def pos1 (n : Nat) : Nat := n + 1

@[export rt_bind_mk]
def mkPos (n : Nat) : {m : Nat // m > 0} := ⟨n + 1, by omega⟩

@[extern "rt_bind_mk"]
opaque mk1 : Nat → Nat

def main (args : List String) : IO Unit := do
  IO.println (myAddBody 2 3, myAddBody (2 ^ 64) 1, [1, 2].map (myAddBody 10))
  IO.println (pushB "a" 'b')
  IO.println (pushCode "a" 98, ["x", "y"].map (pushCode · 33))
  IO.println (triple 5, tripleB 5, [1, 2].map triple)
  IO.println (sizeNat #[1, 2, 3], sizeNat #[], [#[7], #[8, 9]].map sizeNat)
  IO.println (getNat #[5, 6] 1, getNat #[5, 6] 7, [0, 1].map (getNat #[10, 20]))
  IO.println (pushNat2 #[1] 2, [#[3], #[]].map (pushNat2 · (2 ^ 70)))
  IO.println (addT 2 3, pushStr #["x"] "y")
  IO.println (sizeWrap ⟨#[1, 2, 3]⟩, [Wrap.mk #[], ⟨#[4]⟩].map sizeWrap, pos1 41, [1, 2].map pos1)
  IO.println (mk1 41, [1, 2].map mk1)
  if args.length > 100 then IO.println (sizeList [1, 2], sizeTwo ⟨#[1], 2⟩)
