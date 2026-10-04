/-! Runtime test: function types computed from a list of argument kinds (a
typed printf, `FnTy : List K → Type`). The closures are built in uniform code
and applied by typed callers one argument at a time, all at once, partially
and from lists, with arguments of 14 representations (UInt8, UInt64, Float,
Float32, Char, Bool, String, big Nat, big Int, Unit, a function, a pair of
scalars, Int8, USize); uniform code feeds them too. The uncurried form over a
computed tuple (`Args`), curry and uncurry between the two, and a `ToString`
dictionary chosen by the kind.
A coverage test from Crane's test corpus (Bloomberg's Rocq-to-C++ extractor,
whose regression tests document shapes that broke a typed, reference-counted
code generator); the code is new, the shapes are those of Crane's
tests/regression/type_level_fun_apply, type_level_fixpoint_call,
type_level_fixpoint_arity, dependent_if_type_branches,
sigt_branch_type_mismatch, sigt_erased_fn_param, existential_fn_projection,
erased_pair_fn_call.
From the round-9 review, area crane (rv9/crane), program CrPrintf. -/

namespace RtComputedFnTypes

inductive K | u8 | u64 | f64 | f32 | chr | bool | str | nat | int | unit | fn | pair | i8 | usize
  deriving Repr, DecidableEq, Inhabited

def K.ty : K → Type
  | .u8 => UInt8 | .u64 => UInt64 | .f64 => Float | .f32 => Float32 | .chr => Char
  | .bool => Bool | .str => String | .nat => Nat | .int => Int | .unit => Unit
  | .fn => (Nat → Nat) | .pair => (UInt8 × Float) | .i8 => Int8 | .usize => USize

def K.show : (k : K) → k.ty → String
  | .u8, (x : UInt8) => s!"u8:{x}"
  | .u64, (x : UInt64) => s!"u64:{x}"
  | .f64, (x : Float) => s!"f:{x}"
  | .f32, (x : Float32) => s!"f32:{x}"
  | .chr, (x : Char) => s!"c:{x}"
  | .bool, (x : Bool) => s!"b:{x}"
  | .str, (x : String) => s!"s:{x}"
  | .nat, (x : Nat) => s!"n:{x}"
  | .int, (x : Int) => s!"i:{x}"
  | .unit, (_ : Unit) => "()"
  | .fn, (f : Nat → Nat) => s!"fn:{f 10}"
  | .pair, (p : UInt8 × Float) => s!"p:{p.1}/{p.2}"
  | .i8, (x : Int8) => s!"i8:{x}"
  | .usize, (x : USize) => s!"us:{x}"

def K.dflt : (k : K) → k.ty
  | .u8 => (250 : UInt8) | .u64 => (0xFFFFFFFFFFFFFFFF : UInt64) | .f64 => (2.5 : Float) | .f32 => (0.25 : Float32)
  | .chr => 'λ' | .bool => true | .str => "dd" | .nat => (2^70 : Nat) | .int => (-(2^65) : Int) | .unit => ()
  | .fn => ((· * 3) : Nat → Nat) | .pair => ((7 : UInt8), (0.5 : Float)) | .i8 => (-128 : Int8) | .usize => (12345 : USize)

def K.step : (k : K) → k.ty → k.ty
  | .u8, (x : UInt8) => x + 7 | .u64, (x : UInt64) => x * 3 | .f64, (x : Float) => x / 2
  | .f32, (x : Float32) => x * 4 | .chr, (c : Char) => Char.ofNat (c.toNat + 1) | .bool, (b : Bool) => !b
  | .str, (s : String) => s ++ "+" | .nat, (n : Nat) => n * n | .int, (i : Int) => i - 1 | .unit, () => ()
  | .fn, (f : Nat → Nat) => f ∘ f | .pair, (p : UInt8 × Float) => (p.1 + 1, p.2 * 3)
  | .i8, (x : Int8) => x - 1 | .usize, (x : USize) => x * 2

-- the curried function type and a printf over it
def FnTy : List K → Type
  | [] => String
  | k :: ks => k.ty → FnTy ks

def printfAux : (ks : List K) → String → FnTy ks
  | [], acc => acc
  | k :: ks, acc => fun x => printfAux ks (acc ++ k.show x ++ ";")
@[noinline] def printf (ks : List K) : FnTy ks := printfAux ks ""

-- feeding a curried function its arguments in uniform code
def feed : (ks : List K) → FnTy ks → String
  | [], s => s
  | k :: ks, f => feed ks (f (k.step (K.dflt k)))

-- the uncurried form over a computed tuple, and the conversions
def Args : List K → Type
  | [] => Unit
  | k :: ks => k.ty × Args ks
def sprintf : (ks : List K) → Args ks → String
  | [], () => "."
  | k :: ks, (x, r) => k.show x ++ "|" ++ sprintf ks r
def dflts : (ks : List K) → Args ks
  | [] => ()
  | k :: ks => (k.dflt, dflts ks)
def curry : (ks : List K) → (Args ks → String) → FnTy ks
  | [], f => f ()
  | _ :: ks, f => fun x => curry ks (fun r => f (x, r))
def uncurry : (ks : List K) → FnTy ks → Args ks → String
  | [], s, () => s
  | _ :: ks, f, (x, r) => uncurry ks (f x) r
def mapArgs : (ks : List K) → Args ks → Args ks
  | [], () => ()
  | k :: ks, (x, r) => (k.step x, mapArgs ks r)

-- a dictionary chosen by the kind
def K.inst : (k : K) → ToString k.ty
  | .u8 => inferInstanceAs (ToString UInt8) | .u64 => inferInstanceAs (ToString UInt64)
  | .f64 => inferInstanceAs (ToString Float) | .f32 => inferInstanceAs (ToString Float32)
  | .chr => inferInstanceAs (ToString Char) | .bool => inferInstanceAs (ToString Bool)
  | .str => inferInstanceAs (ToString String) | .nat => inferInstanceAs (ToString Nat)
  | .int => inferInstanceAs (ToString Int) | .unit => inferInstanceAs (ToString Unit)
  | .fn => ⟨fun f => s!"<fn {f 1}>"⟩ | .pair => inferInstanceAs (ToString (UInt8 × Float))
  | .i8 => inferInstanceAs (ToString Int8) | .usize => inferInstanceAs (ToString USize)
def showAll : (ks : List K) → Args ks → List String
  | [], () => []
  | k :: ks, (x, r) => @toString _ k.inst x :: showAll ks r

-- a package of a kind list and a function over it, kept in a list
structure Fmt where
  ks : List K
  f : FnTy ks

def asStr (s : String) : String := s

def kindsOf (n : Nat) : List K :=
  let all := [K.u8, .u64, .f64, .f32, .chr, .bool, .str, .nat, .int, .unit, .fn, .pair, .i8, .usize]
  (List.range n).map fun i => all[(i * 5 + n) % all.length]!

def main (args : List String) : IO Unit := do
  let k := args.length
  -- typed callers: the type reduces at the call
  IO.println (asStr (printf [.u8, .str, .f64] (7 + k.toUInt8) "x" (1.5 : Float)))
  IO.println (asStr (printf [.f32, .chr, .bool, .u64] (0.5 : Float32) 'z' false (k.toUInt64 + 99)))
  IO.println (asStr (printf [.fn, .pair, .unit, .int] ((· + k) : Nat → Nat) (((3 : UInt8), (2.0 : Float)) : UInt8 × Float) () (-5 : Int)))
  IO.println (asStr (printf [.i8, .usize, .nat] (-3 : Int8) (77 : USize) (2^64 + k : Nat)))
  let p : UInt8 → Float32 → Char → String := printf [.u8, .f32, .chr]
  let q := p (200 + k.toUInt8)
  let r := q 1.25
  IO.println s!"{r 'a'} {r 'b'} {q 0.0 'c'}"
  let partials : List (Char → String) := [r, q 9.5, p 1 2]
  IO.println (partials.map (· 'Q'))
  -- uniform callers
  for n in [0, 1, 3, 5, 9, 14] do
    let ks := kindsOf (n + k)
    IO.println s!"feed {n}: {feed ks (printf ks)}"
    IO.println s!"sprintf {n}: {sprintf ks (dflts ks)}"
    IO.println s!"curry {n}: {feed ks (curry ks (sprintf ks))}"
    IO.println s!"uncurry {n}: {uncurry ks (printf ks) (mapArgs ks (dflts ks))}"
    IO.println s!"showAll {n}: {showAll ks (mapArgs ks (mapArgs ks (dflts ks)))}"
  let fmts : List Fmt := [⟨[.u8], printf [.u8]⟩, ⟨[.f64, .f64], curry [.f64, .f64] (sprintf _)⟩,
    ⟨[.chr, .fn], fun (c : Char) (g : Nat → Nat) => s!"{c}{g 2}"⟩, ⟨[], ("empty" : String)⟩, ⟨kindsOf 6, printf (kindsOf 6)⟩]
  IO.println (fmts.map fun f => feed f.ks f.f)

end RtComputedFnTypes

def main (args : List String) : IO Unit := RtComputedFnTypes.main args
