/-! Runtime test: 40 existential packages stepped in uniform code (the payload
is a `Box`): every integer width, Float/Float32, Char, Bool, Unit, an enum,
big Nat/Int, String, Array UInt64/Float/Nat/Bool/enum/Unit, ByteArray,
FloatArray, List Float, Option UInt8, an 8-field mixed structure, value
structures of Float/UInt8/function, functions of 1 and 3 arguments, Thunk,
Float × UInt8, Subtype, Fin, Except, Sum, Sigma.
From the round-6 adversarial reviewers, area types (adv6/types), check
Ty6Exist. -/

-- Existential packages holding every representation, stepped through uniform code
structure Pkg where
  α : Type
  v : α
  sh : α → String
  step : α → α

@[noinline] def run (p : Pkg) (n : Nat) : String :=
  let rec go : Nat → p.α → p.α
    | 0, x => x
    | k + 1, x => go k (p.step x)
  p.sh (go n p.v)

@[noinline] def runAll (ps : List Pkg) (n : Nat) : List String := ps.map (run · n)

inductive Col | r | g | b deriving Repr, BEq
def Col.next : Col → Col | .r => .g | .g => .b | .b => .r

structure Mixed where
  a : UInt8
  b : Float
  c : Bool
  d : Nat
  e : String
  f : UInt64
  g : Float32
  h : Int16
  deriving Repr

structure FW where fval : Float deriving Repr
structure FnW where fn : Nat → Nat
structure UW where u : UInt8 deriving Repr

def mixedStep (m : Mixed) : Mixed :=
  { m with a := m.a + 101, b := m.b * 1.5, c := !m.c, d := m.d * 3, e := m.e ++ "x", f := m.f * 3 + 1, g := m.g + 0.25, h := m.h - 1000 }

def pkgs : List Pkg := [
  ⟨Float, 1.5, toString, (· * 2.0)⟩,
  ⟨Float32, 1.5, toString, (· * 3.0)⟩,
  ⟨UInt8, 7, toString, (· * 7)⟩,
  ⟨UInt16, 7, toString, (· * 77)⟩,
  ⟨UInt32, 7, toString, (· * 777)⟩,
  ⟨UInt64, 7, toString, (· * 7777777)⟩,
  ⟨USize, 7, toString, (· * 77)⟩,
  ⟨Int8, -7, toString, (· * 3)⟩,
  ⟨Int64, -7, toString, (· * 1000003)⟩,
  ⟨Char, 'a', toString, fun c => Char.ofNat (c.toNat + 1)⟩,
  ⟨Bool, true, toString, (!·)⟩,
  ⟨Unit, (), fun _ => "unit", id⟩,
  ⟨Col, .r, fun c => reprStr c, Col.next⟩,
  ⟨Nat, 3, toString, (· * 1000000007)⟩,
  ⟨Int, -3, toString, (· * (-1000000007))⟩,
  ⟨String, "s", id, (· ++ "s")⟩,
  ⟨Array UInt64, #[1], toString, fun a => a.push (a.back! * 3)⟩,
  ⟨Array Float, #[0.5], toString, fun a => a.map (· + 1.0) |>.push 0.0⟩,
  ⟨Array Nat, #[1], toString, fun a => a.push (a.size * 100)⟩,
  ⟨Array Bool, #[], toString, fun a => a.push (a.size % 2 == 0)⟩,
  ⟨Array Col, #[], fun a => toString (a.map reprStr), fun a => a.push (if a.size % 2 == 0 then .b else .g)⟩,
  ⟨Array Unit, #[], fun a => toString a.size, fun a => a.push ()⟩,
  ⟨ByteArray, .empty, fun a => toString a.toList, fun a => a.push a.size.toUInt8⟩,
  ⟨FloatArray, .empty, fun a => toString a.toList, fun a => a.push a.size.toFloat⟩,
  ⟨List Float, [], toString, fun l => 0.5 :: l⟩,
  ⟨Option UInt8, none, toString, fun o => some ((o.getD 0) + 9)⟩,
  ⟨Mixed, ⟨1, 1.0, false, 1, "", 1, 1.0, 0⟩, fun m => reprStr m, mixedStep⟩,
  ⟨FW, ⟨2.0⟩, fun w => reprStr w, fun w => ⟨w.fval * w.fval⟩⟩,
  ⟨UW, ⟨2⟩, fun w => reprStr w, fun w => ⟨w.u * w.u⟩⟩,
  ⟨FnW, ⟨id⟩, fun w => toString (w.fn 1), fun w => ⟨fun n => w.fn n + n + 1⟩⟩,
  ⟨Nat → Nat, id, fun f => toString (f 2), fun f => fun n => f (f n) + 1⟩,
  ⟨Float → Float, id, fun f => toString (f 2.0), fun f => fun x => f x * x⟩,
  ⟨Nat → String → Bool → String, fun n s b => s!"{n}{s}{b}", fun f => f 0 "" true,
     fun f => fun n s b => f (n + 1) (s ++ "a") (!b)⟩,
  ⟨Thunk Nat, Thunk.pure 1, fun t => toString t.get, fun t => Thunk.mk fun _ => t.get * 2⟩,
  ⟨Float × UInt8, (1.0, 1), fun p => s!"{p.1},{p.2}", fun p => (p.1 + 0.5, p.2 + 100)⟩,
  ⟨{ n : Nat // n > 0 }, ⟨1, by decide⟩, fun s => toString s.val, fun s => ⟨s.val * 2, by have := s.property; omega⟩⟩,
  ⟨Fin 10, 3, toString, (· + 4)⟩,
  ⟨Except String UInt8, .ok 1, fun e => match e with | .ok v => s!"ok {v}" | .error s => s!"err {s}",
     fun e => match e with | .ok v => if v > 100 then .error "big" else .ok (v * 5) | .error s => .error (s ++ "!")⟩,
  ⟨Sum Float String, .inl 1.0, fun s => match s with | .inl f => s!"L{f}" | .inr t => s!"R{t}",
     fun s => match s with | .inl f => if f > 4.0 then .inr "big" else .inl (f * 2.0) | .inr t => .inr (t ++ "+")⟩,
  ⟨(n : Nat) × Fin (n + 1), ⟨0, 0⟩, fun s => s!"{s.1}/{s.2}", fun s => ⟨s.1 + 1, s.2.succ⟩⟩
]

def main : IO Unit := do
  for (s, i) in (runAll pkgs 0).zipIdx do IO.println s!"0.{i} {s}"
  for (s, i) in (runAll pkgs 1).zipIdx do IO.println s!"1.{i} {s}"
  for (s, i) in (runAll pkgs 5).zipIdx do IO.println s!"5.{i} {s}"

