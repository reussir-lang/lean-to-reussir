/-! Runtime test: cases of the shared dependent-type corpus (programs built
by another translator's team and checked against native Lean), combined:
each case keeps its code in a namespace named after its case id, and `main`
runs each with that case's arguments in this order, printing `-- <id>`
before it (and `exit <code>` after a `main : IO UInt32`). The cases, with
what each checks:
- `A765Ref`: The closure of Lean's debugging aids reaches its row whatever
  its spelling. Mode "ref".
- `A765Shared`: The closure of Lean's debugging aids reaches its row
  whatever its spelling. Mode "shared".
- `A769`: A `@[noinline]` generic identity applied to a `String` literal
  inside a closed term.
- `A796`: T15 step 4 (vi)'s split nesting bounded by the use's argument
  count, each fixed point run to its end: a generic `len5` called on five
  keyed lists `mk b n : List (Ty b)` splits on all five arguments, ...
- `A797`: T15 step 2 (b): a type parameter its own component instantiates at
  a type containing it (polymorphic recursion) is site-keyed, and a type
  holding the union itself under a pointer is a recursive variant (`List
  U_G`), ...
- `A798`: T15 step 2 (b)'s recursive variant: polymorphic recursion `g n
  [x]` at `Nat` and through a generic caller `wrapG (x : β)`
- `A799`: T15 step 3 (d) with T8: a function value injected into a union
  whose variants are arrows (a dependent `ToString` instance, a `Handler`
  with `run : Ty2 tag → Nat`) takes the class's pointer kind at its ...
- `A801`: T15 step 2a: a refused coercion whose own position is an
  existential instance (`Ex`'s T7 slot for its type-valued field `α`) marks
  that slot dynamic, so `Ex` is `Cons(Dyn, Link<Ex>)` and each field value
  is injected ...
- `A802`: T15 step 2 (a): an IO action's result is keyed at its value,
  `IO.Ref (Ty b)` is keyed as the whole cell (an inductive-headed key), and
  `EST.Out` is in T3's by-value list, so its rebuild covers both ...
- `A805`: T15 step 2 (c) rule (1) across a call: a specialization's
  parameter (no kernel type) carries its caller's family key `fun b => List
  (Ty b)`, and a split `cases` coerces its constructor fields per variant.
- `A806`: T15 step 2 (c) rule (1) across a call: the specialization
  `List.foldl._at_.sumAll.spec_0` takes the caller's key `fun b => Ty b` at
  the sigma's second component. -/

namespace A765Ref

structure Tracer where
  tag : String
  body : Unit → List String

structure Step where
  g : Nat → Nat

@[noinline] def mkTracer (n : Nat) : Tracer := { tag := s!"t{n}", body := fun _ => [toString n, "x"] }
@[noinline] def viaField (t : Tracer) : List String := dbgTrace t.tag t.body
@[noinline] def sleepField (t : Tracer) : List String := dbgSleep 1 t.body
@[noinline] def inOp (n : Nat) : Nat := n + dbgTrace "op" (fun _ => n + 1)
@[noinline] def sharedField (s : Step) (n : Nat) : Nat := (dbgTraceIfShared "shared" s.g) n
@[noinline] def viaRef (n : Nat) : IO Nat := do
  let r ← IO.mkRef (fun (_ : Unit) => n * 7)
  let g ← r.get
  let h ← r.get
  return dbgTrace "ref" g + dbgSleep 1 h

def caseMain (args : List String) : IO UInt32 := do
  let n := (args.drop 1).headD "3" |>.toNat!
  match args.headD "" with
  | "field" => IO.println (viaField (mkTracer n))
  | "sleep" => IO.println (sleepField (mkTracer n))
  | "op" => IO.println (inOp n)
  | "ref" => IO.println (← viaRef n)
  | "shared" => IO.println (sharedField { g := (· + n) } n)
  | _ => IO.println "none"
  return 0
end A765Ref

namespace A765Shared

structure Tracer where
  tag : String
  body : Unit → List String

structure Step where
  g : Nat → Nat

@[noinline] def mkTracer (n : Nat) : Tracer := { tag := s!"t{n}", body := fun _ => [toString n, "x"] }
@[noinline] def viaField (t : Tracer) : List String := dbgTrace t.tag t.body
@[noinline] def sleepField (t : Tracer) : List String := dbgSleep 1 t.body
@[noinline] def inOp (n : Nat) : Nat := n + dbgTrace "op" (fun _ => n + 1)
@[noinline] def sharedField (s : Step) (n : Nat) : Nat := (dbgTraceIfShared "shared" s.g) n
@[noinline] def viaRef (n : Nat) : IO Nat := do
  let r ← IO.mkRef (fun (_ : Unit) => n * 7)
  let g ← r.get
  let h ← r.get
  return dbgTrace "ref" g + dbgSleep 1 h

def caseMain (args : List String) : IO UInt32 := do
  let n := (args.drop 1).headD "3" |>.toNat!
  match args.headD "" with
  | "field" => IO.println (viaField (mkTracer n))
  | "sleep" => IO.println (sleepField (mkTracer n))
  | "op" => IO.println (inOp n)
  | "ref" => IO.println (← viaRef n)
  | "shared" => IO.println (sharedField { g := (· + n) } n)
  | _ => IO.println "none"
  return 0
end A765Shared

namespace A769
@[noinline] def Bench.pin (x : α) : BaseIO α := pure x

/-! Chapter 06 A4 fixture A769: a `@[noinline]` generic identity applied to a `String` literal inside a
closed term (the unsafe-cast tester's `qsafe`). The closed term `gid "q"` is a `LocalLazy<Rc<Str>>`
static, and `gid` returns a reference to its argument, so chapter 03 K7 binds the literal just before
the call; chapter 04 T8 builds it at the parameter's type at that call, the static's `Rc<Str>`:
`let t1 = Rc::new(Str::lit("q")); gid(&t1).clone()` (it was bound as `Str::lit("q")`, whose clone is a
`Str`, rustc's E0308). -/

namespace Bench.A769
structure Wrap where
  val : Nat

-- an unsafe declaration before `qsafe` (never reached): Lean's closed-term cache numbers `qsafe`'s
-- closed terms after its own, so the replayed `qsafe._closed_N` has no persisted twin to evaluate at
-- translation time and stays a static
@[noinline] unsafe def gcast {α β : Type} (x : α) : β := unsafeCast x
unsafe def qcheck (n : Nat) : Nat :=
  (gcast n : Nat) + (toString (gcast "q" : String) ++ toString n).length + (gcast (Wrap.mk n) : Nat)

@[noinline] def gid {α : Type} (x : α) : α := x

def build (n : Nat) : Nat := n

def qsafe (n : Nat) : Nat :=
  (gid n : Nat) + (toString (gid "q" : String) ++ toString n).length + (gid (Wrap.mk n)).val

def qpair (n : Nat) : String × Nat :=
  (gid "pair" ++ toString n, (gid "pp").length + n)

def kernel (n : Nat) : List String :=
  [toString (qsafe n), toString (qpair n), toString [gid "a", gid "bc", toString n]]

def render (xs : List String) : String := "|".intercalate xs
end Bench.A769

def caseMain (args : List String) : IO UInt32 := do
  match args with
  | [n] =>
    let input ← Bench.pin (Bench.A769.build n.toNat!)
    let out ← Bench.pin (Bench.A769.kernel input)
    IO.println (Bench.A769.render out)
    return 0
  | _ => IO.eprintln "usage: <prog> SIZE"; return 2
end A769

namespace A796

namespace Jy
def Ty : Bool → Type | true => Nat | false => String
@[noinline] def mk (b : Bool) (n : Nat) : List (Ty b) :=
  match b with | true => List.replicate n n | false => List.replicate (n+1) "s"
@[noinline] def len5 {α β γ δ ε : Type} (a : List α) (b : List β) (c : List γ) (d : List δ) (e : List ε) : Nat :=
  a.length + 10 * b.length + 100 * c.length + 1000 * d.length + 10000 * e.length
@[noinline] def go (b1 b2 b3 b4 b5 : Bool) (n : Nat) : Nat :=
  len5 (mk b1 n) (mk b2 n) (mk b3 n) (mk b4 n) (mk b5 n)
def build (n : Nat) : Nat := n
def kernel (n : Nat) : List Nat :=
  [go true true true true true n, go false false false false false n, go true false true false false n]
def render (r : List Nat) : String := toString r
end Jy

def caseMain (args : List String) : IO Unit := IO.println (Jy.render (Jy.kernel (args.length + 3)))
end A796

namespace A797

namespace Jz
@[noinline] def g : Nat → α → Nat | 0, _ => 0 | n+1, x => g n (List.replicate 1 x)
@[noinline] def h : Nat → α → Nat | 0, _ => 0 | n+1, x => h n (some x)
def build (n : Nat) : Nat := n
def kernel (n : Nat) : List Nat := [g n (5 : Nat), h n "s"]
def render (r : List Nat) : String := toString r
end Jz

def caseMain (args : List String) : IO Unit := IO.println (Jz.render (Jz.kernel (args.length + 3)))
end A797

namespace A798

@[noinline] def g : Nat → α → Nat | 0, _ => 0 | n+1, x => g n [x]
@[noinline] def wrapG (n : Nat) (x : β) : Nat := g n x
def caseMain (args : List String) : IO Unit :=
  IO.println s!"{g (100000 + args.length) (5 : Nat)} {g 3 "s"} {wrapG (100000 + args.length) (5 : Nat)} {wrapG 3 "s"}"
end A798

namespace A799

def Ty : Bool → Type | true => Nat | false => Bool
instance instDep : (b : Bool) → ToString (Ty b)
  | true => inferInstanceAs (ToString Nat)
  | false => inferInstanceAs (ToString Bool)
def pick : (b : Bool) → Nat → Ty b | true, n => n * 2 | false, n => n % 2 == 0
@[noinline] def showIt (b : Bool) (n : Nat) : String := toString (pick b n)
def Ty2 : Bool → Type | true => Nat | false => String
structure Handler where
  tag : Bool
  run : Ty2 tag → Nat
  val : Ty2 tag
@[noinline] def fire (h : Handler) : Nat := h.run h.val
@[noinline] def fireAll (h : Handler) (xs : List Nat) : Nat := match h with
  | ⟨true, run, v⟩ => (xs.map run).foldl (· + ·) (run v)
  | ⟨false, run, v⟩ => run v
@[noinline] def mkH (b : Bool) (s : String) : Handler := match b with
  | true => ⟨true, (fun (n : Nat) => n + 1), s.length⟩
  | false => ⟨false, String.length, s⟩
@[noinline] def wrapH (h : Handler) : Handler := ⟨h.tag, fun v => h.run v + 1, h.val⟩
@[noinline] def wrapN (n : Nat) (h : Handler) : Handler := match n with
  | 0 => h
  | n+1 => ⟨h.tag, fun v => h.run v + fire (wrapN n h), h.val⟩
def caseMain (args : List String) : IO Unit := do
  let z := args.length
  IO.println s!"{showIt true (3 + z)} {showIt false 3} {showIt false 4}"
  IO.println s!"{fire (mkH true "ab")} {fire (mkH false "abc")} {fire (wrapH (mkH true "ab")) + fire (wrapH (wrapH (mkH false "abc")))}"
  IO.println s!"{fire (wrapN 1 (mkH true "ab")) + fire (wrapN 2 (mkH false "abc"))} {fireAll (wrapN 1 (mkH true "ab")) [1, 2]} {fireAll (mkH false "xyz") [1, 2]}"
end A799

namespace A801

inductive Ex where
  | nil
  | cons : (α : Type) → α → Ex → Ex
@[noinline] def Ex.len : Ex → Nat | .nil => 0 | .cons _ _ t => 1 + t.len
def caseMain (args : List String) : IO Unit := IO.println s!"{(Ex.cons Nat (3 + args.length) (Ex.cons String "s" (Ex.cons (List Nat) [1] .nil))).len}"
end A801

namespace A802

def Ty : Bool → Type | true => Nat | false => String
@[noinline] def refOf (b : Bool) (v : Ty b) : IO (IO.Ref (Ty b)) := IO.mkRef v
@[noinline] def readRef (b : Bool) (r : IO.Ref (Ty b)) : IO Nat := match b with
  | true => do let v ← r.get; let n : Nat := v; pure n
  | false => do let v ← r.get; let s : String := v; pure s.length
def caseMain (args : List String) : IO Unit := do
  let r1 ← refOf true (7 + args.length : Nat)
  let r2 ← refOf false "abcd"
  IO.println s!"{← readRef true r1} {← readRef false r2}"
end A802

namespace A805

@[reducible] def Ty : Bool → Type | true => Nat | false => String
instance instTy : (b : Bool) → ToString (Ty b)
  | true => inferInstanceAs (ToString Nat)
  | false => inferInstanceAs (ToString String)
instance instBEqTy : (b : Bool) → BEq (Ty b)
  | true => inferInstanceAs (BEq Nat)
  | false => inferInstanceAs (BEq String)
def mk : (b : Bool) → Nat → Ty b
  | true, n => n
  | false, n => s!"#{n}"
def describe (b : Bool) (x : Ty b) : String := s!"<{x}>"
def same (b : Bool) (x y : Ty b) : Bool := x == y
class Sized (α : Type) where size : α → Nat
instance : Sized Nat := ⟨id⟩
instance : Sized String := ⟨String.length⟩
instance instSizedTy : (b : Bool) → Sized (Ty b)
  | true => inferInstanceAs (Sized Nat)
  | false => inferInstanceAs (Sized String)
def total (b : Bool) (xs : List (Ty b)) : Nat := xs.foldl (fun a x => a + Sized.size x) 0
def caseMain (args : List String) : IO UInt32 := do
  let n := args.length
  let b := n % 2 == 0
  IO.println s!"{total b [mk b n, mk b (n+1)]}"
  return 0
end A805

namespace A806

@[reducible] def Ty : Bool → Type | true => Nat | false => String
@[noinline] def sumAll (xs : List ((b : Bool) × Ty b)) : Nat := xs.foldl (fun acc p => match p with
  | ⟨true, n⟩ => acc + n
  | ⟨false, s⟩ => acc + s.length) 0
def caseMain (args : List String) : IO UInt32 := do
  IO.println s!"{sumAll [⟨true, 5⟩, ⟨false, "abc"⟩]}"
  return 0
end A806

def main : IO Unit := do
  IO.println "-- A765Ref"
  let c ← A765Ref.caseMain ["ref"]
  IO.println s!"exit {c}"
  IO.println "-- A765Shared"
  let c ← A765Shared.caseMain ["shared"]
  IO.println s!"exit {c}"
  IO.println "-- A769"
  let c ← A769.caseMain ["5"]
  IO.println s!"exit {c}"
  IO.println "-- A796"
  A796.caseMain ["a", "b", "c"]
  IO.println "-- A797"
  A797.caseMain ["a", "b", "c"]
  IO.println "-- A798"
  A798.caseMain ["a", "b", "c"]
  IO.println "-- A799"
  A799.caseMain ["a", "b", "c"]
  IO.println "-- A801"
  A801.caseMain ["a", "b", "c"]
  IO.println "-- A802"
  A802.caseMain ["a", "b", "c"]
  IO.println "-- A805"
  let c ← A805.caseMain ["a", "b", "c"]
  IO.println s!"exit {c}"
  IO.println "-- A806"
  let c ← A806.caseMain ["a", "b", "c"]
  IO.println s!"exit {c}"
