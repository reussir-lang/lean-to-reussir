/-! Runtime test: values made of objects boxed and read back. Each value goes,
at its own type, through the routes of RtDepPayloadScalars (an identity
over any type stored in a structure field, an existential package and a
copy of it made by code over the unknown type, a thunk, a task, an
`IO.Ref`, an `Array α`, an `Option α`, a dependent pair), and every read
must print the same as the value itself. Kinds: `String`, `ByteArray`,
`FloatArray`, and an `Array` of each scalar kind and of these; structures
whose fields are all scalars, mixed, or one relevant field and a proof;
`Subtype` and `Fin` (also `Fin (2^70)`); closures (a partial application
of a top-level function, a closure applied to more arguments than it
takes, closures that capture a boxed value, a `Float` and a `UInt64`);
recursive, mutual and nested inductives (`Rose` with an `Array Rose`); an
inductive with a computed field; `Prod`, `Sum`, `Option` and `Except` of
scalars. Native Lean prints one line per value, the printout and `true`
for each route. -/

structure Poly where
  run : {α : Type} → α → α

@[noinline] def poly : Poly := ⟨fun x => x⟩

structure Pk where
  α : Type
  v : α
  sh : α → String

@[noinline] def Pk.str (p : Pk) : String := p.sh p.v

@[noinline] def Pk.dup (p : Pk) : Pk × Pk := (p, ⟨p.α, poly.run p.v, p.sh⟩)

inductive Tag | a | b

@[reducible] def Tag.denote (α : Type) : Tag → Type
  | .a => α
  | .b => Nat

@[noinline] def viaSigma {α : Type} (v : α) : (t : Tag) × t.denote α := ⟨.a, v⟩

@[noinline] def check {α : Type} (sh : α → String) (name : String) (v : α) : IO Unit := do
  let s := sh v
  let r1 := sh (poly.run v) == s
  let r2 := Pk.str ⟨α, v, sh⟩ == s
  let (p1, p2) := Pk.dup ⟨α, v, sh⟩
  let r3 := p1.str == s && p2.str == s
  let th : Thunk α := Thunk.mk fun _ => poly.run v
  let r4 := sh th.get == s
  let t := Task.spawn fun _ => poly.run v
  let r5 := sh t.get == s
  let ref ← IO.mkRef v
  ref.modify poly.run
  let r6 := sh (← ref.get) == s
  let arr : Array α := #[v, poly.run v]
  let r7 := arr.size == 2 && arr.all (sh · == s)
  let o : Option α := poly.run (some v)
  let r8 := (o.map sh) == some s
  let r9 := match viaSigma v with
    | ⟨.a, w⟩ => sh w == s
    | ⟨.b, _⟩ => false
  IO.println s!"{name} {s.take 160} {r1} {r2} {r3} {r4} {r5} {r6} {r7} {r8} {r9}"

def f64 (x : Float) : String := s!"{x.toBits}"

structure AllScalar where
  a : UInt64
  b : Float
  c : UInt8
  d : Bool
  e : UInt32

structure Mixed where
  n : Nat
  f : Float
  s : String
  u : UInt16
  l : List Nat

structure OneField where
  x : Nat
  h : x < 1000

inductive Tree where
  | leaf
  | node (l : Tree) (v : UInt64) (r : Tree)

def Tree.show : Tree → String
  | .leaf => "."
  | .node l v r => s!"({l.show} {v} {r.show})"

mutual
inductive Ev where
  | zero (tag : String)
  | succ (o : Od)
inductive Od where
  | succ (e : Ev) (w : Float)
end

mutual
def Ev.show : Ev → String
  | .zero t => t
  | .succ o => "E" ++ o.show
def Od.show : Od → String
  | .succ e w => "O" ++ toString w ++ e.show
end

inductive Rose where
  | node (x : Nat) (kids : Array Rose)

partial def Rose.show : Rose → String
  | .node x ks => s!"{x}[{ks.foldl (fun s k => s ++ k.show) ""}]"

inductive Expr where
  | num (n : Nat)
  | add (a b : Expr)
with
  @[computed_field] size : Expr → Nat
    | .num _ => 1
    | .add a b => a.size + b.size + 1

def Expr.show : Expr → String
  | .num n => toString n
  | .add a b => s!"({a.show}+{b.show})"

@[noinline] def adder (a b c : Nat) : Nat := a * 100 + b * 10 + c

/-- A closure whose result is a function: applied to two arguments at once. -/
@[noinline] def curried (k : Nat) : Nat → Nat → Nat := fun x => fun y => k + x * y

@[noinline] def capture {α : Type} (v : α) (sh : α → String) : Nat → String := fun i => s!"{i}:{sh v}"

def main : IO Unit := do
  -- strings and byte and float arrays
  check id "string" ""
  check id "string" "héllo, wörld ✓"
  check id "string" (String.mk (List.replicate 300 'z'))
  check (fun (b : ByteArray) => toString b.toList) "bytes" ⟨#[0, 255, 7, 128]⟩
  check (fun (b : ByteArray) => toString b.size) "bytes" ByteArray.empty
  check (fun (b : FloatArray) => toString (b.toList.map Float.toBits)) "floats" ⟨#[1.5, -0.0, Float.ofBits 1]⟩
  -- arrays of each kind
  check (fun (a : Array Bool) => toString a) "arr bool" #[true, false, true]
  check (fun (a : Array UInt8) => toString a) "arr u8" #[0, 255, 3]
  check (fun (a : Array UInt64) => toString a) "arr u64" #[0, 9223372036854775808, 18446744073709551615]
  check (fun (a : Array USize) => toString a) "arr usize" #[1, 9223372036854775808]
  check (fun (a : Array Float) => toString (a.map Float.toBits)) "arr float" #[0.5, -0.0, 1e300]
  check (fun (a : Array Float32) => toString (a.map Float32.toBits)) "arr float32" #[0.5, -0.0]
  check (fun (a : Array Char) => toString (a.map Char.toNat)) "arr char" #['a', Char.ofNat 0x10FFFF]
  check (fun (a : Array Nat) => toString a) "arr nat" #[0, 2 ^ 63, 2 ^ 64, 10 ^ 40]
  check (fun (a : Array Int) => toString a) "arr int" #[-1, -2147483649, -(2 ^ 63), 2 ^ 70]
  check (fun (a : Array String) => toString a) "arr string" #["a", "", "bc"]
  check (fun (a : Array ByteArray) => toString (a.map (·.toList))) "arr bytes" #[⟨#[1, 2]⟩, ⟨#[]⟩]
  check (fun (a : Array FloatArray) => toString (a.map fun f => f.toList.map Float.toBits)) "arr floats" #[⟨#[2.0]⟩]
  check (fun (a : Array Unit) => toString a.size) "arr unit" #[(), (), ()]
  check (fun (a : Array (Array Nat)) => toString a) "arr arr" #[#[1], #[], #[2, 3]]
  -- structures, Subtype, Fin
  check (fun (s : AllScalar) => s!"{s.a} {s.b.toBits} {s.c} {s.d} {s.e}") "allscalar"
    ⟨18446744073709551615, -0.0, 200, true, 4000000000⟩
  check (fun (s : Mixed) => s!"{s.n} {s.f} {s.s} {s.u} {s.l}") "mixed" ⟨2 ^ 65, 2.5, "m", 65535, [1, 2]⟩
  check (fun (s : OneField) => s!"{s.x}") "onefield" ⟨999, by decide⟩
  check (fun (s : { x : Nat // x > 5 }) => s!"{s.val}") "subtype" ⟨2 ^ 64 + 1, by decide⟩
  check (fun (s : { x : UInt64 // x > 5 }) => s!"{s.val}") "subtype u64" ⟨18446744073709551615, by decide⟩
  check (fun (f : Fin 10) => s!"{f}") "fin" (7 : Fin 10)
  check (fun (f : Fin (2 ^ 70)) => s!"{f}") "fin big" ⟨2 ^ 69 + 3, by decide⟩
  -- closures
  check (fun (f : Nat → Nat) => s!"{f 3}") "partial" (adder 4 5)
  check (fun (f : Nat → Nat → Nat) => s!"{f 3 4}") "partial2" (adder 7)
  check (fun (f : Nat → Nat → Nat) => s!"{f 3 4}") "over" (curried 5)
  check (fun (f : Nat → String) => f 1) "capture box" (capture (2 ^ 64 : Nat) toString)
  check (fun (f : Nat → String) => f 2) "capture float" (capture (Float.ofBits 1) f64)
  check (fun (f : Nat → String) => f 3) "capture u64" (capture (18446744073709551615 : UInt64) toString)
  check (fun (f : UInt64 → Float → UInt64) => s!"{f 1 2.5}") "scalar fn" (fun u x => u + x.toUInt64)
  -- inductives
  check Tree.show "tree" (.node (.node .leaf 18446744073709551615 .leaf) 3 .leaf)
  check Ev.show "mutual" (.succ (.succ (.succ (.succ (.zero "z") 1.5)) (-0.0)))
  check Rose.show "rose" (.node 1 #[.node 2 #[], .node 3 #[.node 4 #[]]])
  let e : Expr := .add (.num 1) (.add (.num 2) (.num 3))
  check (fun (e : Expr) => s!"{e.show} {e.size}") "computed" e
  -- library sums and products of scalars
  check (fun (p : UInt64 × UInt64) => s!"{p}") "prod u64" (18446744073709551615, 1)
  check (fun (p : Float × Nat) => s!"{p.1.toBits} {p.2}") "prod float" (-0.0, 2 ^ 64)
  check (fun (s : Sum UInt8 String) => match s with | .inl u => s!"l{u}" | .inr t => t) "sum" (.inl 255)
  check (fun (o : Option UInt64) => s!"{o}") "option u64" (some 18446744073709551615)
  check (fun (e : Except String Float) => match e with | .ok f => s!"{f.toBits}" | .error m => m) "except" (.ok (-0.0))
