/-!
Externs of the program whose C symbols are names lean2rr knows otherwise
(review RV8E-01, RV8E-02, RV8E-05, RV8E-06):
- words of lean2rr's prelude that are not prelude functions (`swap`,
  `hash`, `reverse`), a `lean_` symbol whose `l2r_` twin is a prelude
  function (`lean_sleep_ms`), a C function that only the prelude's Rust
  code declares (`gettid`): no extern of Lean's library has these symbols,
  so their Lean definitions run (natively the C code in
  `RtExternNames.ffi.c` runs);
- symbols of externs of Lean's runtime library, of the same type up to
  universes (`Array.mk`, `Array.toList`, `ST.Prim.Ref.get`,
  `IO.getStdout`, `Array.push`, `Nat.add` through a type alias), an
  instance of it (`pushNat`, `sizeStr`) or another type (`pushCode` with a
  `UInt32`): an extern of the program is never bound to Lean's runtime (the
  owner's decision of 2026-10-04), so their Lean definitions run, even
  where the prelude has a function of that symbol (also at `Array Nat`).
  Natively the runtime's functions run; the definitions compute the same.
-/

@[extern "swap"]
def swapPair (p : Nat × Nat) : Nat × Nat := (p.2, p.1)

@[extern "hash"]
def myHash (x : UInt64) : UInt64 := x * 31 + 7

@[extern "reverse"]
def rev (s : @& String) : String := String.ofList s.toList.reverse

@[extern "ctl_twice"]
def twice (n : Nat) : Nat := 2 * n

@[extern "lean_sleep_ms"]
def clampMs (n : UInt32) : UInt32 := if n > 1000 then 1000 else n

@[extern "gettid"]
def threadId (u : Unit) : UInt32 := 0

@[extern "lean_array_mk"]
def listToArr {α : Type} (l : List α) : Array α := l.toArray

@[extern "lean_array_to_list"]
def arrToList {α : Type} (a : Array α) : List α := a.toList

@[extern "lean_st_ref_get"]
def readRef {σ α : Type} (r : @& ST.Ref σ α) : ST σ α := r.get

@[extern "lean_get_stdout"]
def myStdout : BaseIO IO.FS.Stream := IO.getStdout

@[extern "lean_array_push"]
def pushNat (a : Array Nat) (v : Nat) : Array Nat := a.push v

@[extern "lean_array_get_size"]
def sizeStr (a : @& Array String) : Nat := a.size

@[extern "lean_array_push"]
def push0 {α : Type} (a : Array α) (v : α) : Array α := a.push v

@[extern "lean_string_push"]
def pushCode (s : String) (c : UInt32) : String := s.push (Char.ofNat c.toNat)

def MyNat := Nat
@[extern "lean_nat_add"]
def addM (a b : @& MyNat) : MyNat := Nat.add a b

def main : IO Unit := do
  IO.println (swapPair (1, 2))
  IO.println (myHash 5)
  IO.println (rev "abc")
  IO.println (twice 21)
  IO.println (clampMs 5000)
  IO.println (threadId () == 0 || true)
  IO.println (listToArr ["a", "b"])
  IO.println (arrToList #["x", "y"])
  IO.println (listToArr [1, 2, 3])
  IO.println (arrToList #[4, 5])
  let r ← IO.mkRef 7
  let v ← (readRef r : BaseIO Nat)
  IO.println v
  let out ← myStdout
  out.putStrLn "via my stdout"
  IO.println (pushNat #[1, 2] 3)
  IO.println (sizeStr #["a", "b", "c"])
  IO.println (push0 #[1, 2] 3)
  IO.println (push0 #["x"] "y")
  IO.println (pushCode "ab" 99)
  let r2 : Nat := addM (2 : Nat) (3 : Nat)
  IO.println r2
