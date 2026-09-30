/-! Runtime test: thunks are memoized (`Thunk.get` runs the closure once, on
first use; `dbgTrace` shows when) at many value types: `Nat`, big `Nat`,
`Int`, `String`, `Float`, `Bool`, `UInt8`, `Unit`, closures, `Option`,
`Array`, thunks of thunks, thunks in structures, arrays and recursive
types (a lazy list), and at a type that is not statically known (an
existential, stored as `Box`); `Thunk.pure`, `map`, `bind`, `default`. -/

@[noinline] def mk (tag : String) (v : Nat) : Thunk Nat :=
  Thunk.mk fun _ => dbgTrace s!"force {tag}" fun _ => v * 2

structure Holder where
  name : String
  th : Thunk Nat

inductive LazyList where
  | nil
  | cons (hd : Nat) (tl : Thunk LazyList)

instance : Inhabited LazyList := ⟨.nil⟩

@[noinline] partial def nats (n : Nat) : LazyList :=
  .cons n (Thunk.mk fun _ => dbgTrace s!"step {n}" fun _ => nats (n + 1))

def LazyList.take : Nat → LazyList → List Nat
  | 0, _ => []
  | _, .nil => []
  | k + 1, .cons h t => h :: LazyList.take k t.get

structure Pack where
  α : Type
  t : Thunk α
  shw : α → String

@[noinline] def packs (n : Nat) : List Pack :=
  [⟨Nat, Thunk.mk (fun _ => dbgTrace "pack nat" fun _ => n + 1), toString⟩,
   ⟨String, Thunk.mk (fun _ => dbgTrace "pack str" fun _ => s!"s{n}"), id⟩,
   ⟨Int, .pure (Int.ofNat n - 5), toString⟩]

@[noinline] def fnThunk (k : Nat) : Thunk (Nat → Nat) :=
  Thunk.mk fun _ => dbgTrace "fn thunk" fun _ => fun x => x + k

@[noinline] def unitThunk (s : String) : Thunk Unit :=
  Thunk.mk fun _ => dbgTrace s fun _ => ()

@[noinline] def floatThunk (x : Float) : Thunk Float := Thunk.mk fun _ => dbgTrace "float" fun _ => x * 2.5

@[noinline] def boolThunk (b : Bool) : Thunk Bool := Thunk.mk fun _ => dbgTrace "bool" fun _ => !b

@[noinline] def u8Thunk (b : UInt8) : Thunk UInt8 := Thunk.mk fun _ => dbgTrace "u8" fun _ => b + 200

@[noinline] def optThunk (n : Nat) : Thunk (Option Nat) := Thunk.mk fun _ => dbgTrace "opt" fun _ => if n > 100 then none else some n

@[noinline] def arrThunk (n : Nat) : Thunk (Array Nat) := Thunk.mk fun _ => dbgTrace "arr" fun _ => Array.range n

@[noinline] def bigThunk (n : Nat) : Thunk Nat := Thunk.mk fun _ => dbgTrace "big" fun _ => 2 ^ (70 + n)

@[noinline] def chain (t : Thunk Nat) : Thunk Nat := t.map (· + 1) |>.bind fun x => Thunk.mk fun _ => dbgTrace s!"bind {x}" fun _ => x * 10

@[noinline] def useTwice (t : Thunk Nat) : Nat := t.get + t.get

def main (args : List String) : IO Unit := do
  let n := args.length
  let a := mk "a" (n + 3)
  IO.println s!"before get"
  IO.println s!"a {a.get} {a.get} twice {useTwice a}"
  let h : Holder := ⟨"h", mk "h" 10⟩
  let hs := [h, h, h]
  IO.println s!"holders {hs.map (·.th.get)}"
  IO.println s!"lazy {(nats n).take 4}"
  let l := nats 100
  IO.println s!"lazy again {l.take 3} {l.take 3}"
  for p in packs n do
    IO.println s!"pack {p.shw p.t.get} {p.shw p.t.get}"
  let f := fnThunk n
  IO.println s!"fn {f.get 1} {f.get 2}"
  let u := unitThunk "unit forced"
  let _ := u.get
  IO.println s!"unit {u.get == ()} {u.get == ()}"
  IO.println s!"float {(floatThunk 1.5).get} bool {(boolThunk false).get} u8 {(u8Thunk 100).get}"
  let o := optThunk n
  IO.println s!"opt {o.get} {o.get}"
  let ar := arrThunk (n + 4)
  IO.println s!"arr {ar.get} {ar.get.size}"
  let b := bigThunk n
  IO.println s!"big {b.get} {b.get % 7}"
  let c := chain (mk "c" n)
  IO.println s!"chain {c.get} {c.get}"
  let d : Thunk Nat := default
  IO.println s!"default {d.get}"
  let p := Thunk.pure (n + 42)
  IO.println s!"pure {p.get}"
  let nested : Thunk (Thunk Nat) := Thunk.mk fun _ => dbgTrace "outer" fun _ => mk "inner" 7
  IO.println s!"nested {nested.get.get} {nested.get.get}"
  let arrOfThunks := #[mk "x0" 1, mk "x1" 2, mk "x2" 3]
  IO.println s!"arr thunks {arrOfThunks[1]!.get} {arrOfThunks.map (·.get)}"
  for i in [0:3] do
    IO.println s!"loop {i} {a.get}"
