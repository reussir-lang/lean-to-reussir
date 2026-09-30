/-! Runtime test: panics that continue with the default value (`panic!`,
`get!` on arrays, lists, options, strings, bytes), their messages on stderr,
and ordering with regular output. -/

def safeDiv (a b : Nat) : Nat :=
  if b == 0 then panic! s!"division of {a} by zero" else a / b

def firstChar (s : String) : Char :=
  if s.isEmpty then panic! "empty string" else s.front

structure Cfg where
  name : String := "default"
  level : Nat := 3
deriving Repr, Inhabited

def findCfg (xs : List Cfg) (n : String) : Cfg :=
  match xs.find? (·.name == n) with
  | some c => c
  | none => panic! s!"no config {n}"

def main (args : List String) : IO Unit := do
  let k := args.length
  IO.println s!"safeDiv {safeDiv 10 2} {safeDiv 7 k}"
  IO.println s!"firstChar {firstChar "abc"} {repr (firstChar "")}"
  IO.println s!"cfg {repr (findCfg [{ name := "a" }] "a")} {repr (findCfg [] "b")}"
  let a := #[1, 2, 3]
  IO.println s!"array {a[k + 5]!} {(#["x"] : Array String)[k + 1]!} {(#[1.5] : Array Float)[k + 2]!}"
  IO.println s!"list {[1, 2, 3][k + 7]!} {([] : List Nat).head!} {([] : List String).getLast!} {([] : List Nat).tail!}"
  IO.println s!"option {(none : Option Nat).get!} {(some 4 : Option Nat).get!} {(none : Option String).get!}"
  IO.println s!"string get! {repr ("héllo".get! ⟨2⟩)} {repr ("abc".get! ⟨10⟩)} {repr ("abc".get! ⟨1⟩)}"
  IO.println s!"bytes {(ByteArray.mk #[1, 2]).get! 5} floats {(FloatArray.mk #[1.0]).get! 3}"
  IO.println s!"set! {(a.set! 10 0).toList} {(#[] : Array Nat).back!}"
  IO.println s!"toNat! {"12x".toNat!} {"-5".toInt!} {"99".toNat!}"
  IO.eprintln "between panics"
  IO.println s!"after {safeDiv 1 0 + safeDiv 2 0}"
