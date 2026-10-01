/-! Runtime test: startup order of declarations that share a source range.
Every declaration made by one macro expansion has the macro call's range,
and so have the instances of one `deriving instance … for A, B` command;
natively they still start in the order they were made. Also: the
auxiliary constants of several `unsafe` parts of one declaration
(`c._unsafe_1`, `_4`, `_7`, `_10`, …) start in that order. -/

@[specialize] def gen {m : Type → Type} [Monad m] (f : Nat → m Nat) : m Nat := f 1

def t (s : String) (n : Nat) : Nat := dbgTrace s fun _ => n

def first : Nat := t "first" 0

-- Two constants from one macro: source order, not name order.
macro "mk2" a:ident b:ident : command => `(def $a : Nat := t "zz (first in the macro)" 1
  def $b : Nat := t "aa (second in the macro)" 2)
mk2 zz aa

-- `foo` and `foo.bar` from one macro: two commands, not a declaration and
-- its `where` helper.
macro "mkp" a:ident b:ident : command => `(def $a : Nat := t "foo" 3
  def $b : Nat := t "foo.bar" 4)
mkp foo foo.bar

-- A hygienic helper and a user declaration with a specialization.
macro "mkh" n:ident : command => `(def helper : Nat := t "hygienic helper" 5
  def $n : Nat := t "mkh user" (helper + Id.run (gen (m := Id) (fun i => dbgTrace "spec in mkh user" fun _ => pure i))))
mkh userA

-- Two `initialize` constants from one macro, the second reading the first
-- (it must be set already).
macro "mkinit" a:ident b:ident : command => `(initialize $a : Nat ← do IO.eprintln "init zi"; pure 41
  initialize $b : Nat ← do IO.eprintln s!"init ai reads zi = {$a}"; pure ($a + 1))
mkinit zi ai

-- Two derived instances from one command, tracing through a function
-- instance and a field default.
structure Wrap (α : Type) where
  v : α

instance [Inhabited α] : Inhabited (Wrap α) := ⟨dbgTrace "Wrap default" fun _ => ⟨default⟩⟩

structure Zed where
  w : Wrap Nat
  tag : String := dbgTrace "Zed.tag default" fun _ => "z"

structure Abe where
  w : Wrap String
  tag : String := dbgTrace "Abe.tag default" fun _ => "a"

deriving instance Inhabited for Zed, Abe

-- Twelve `unsafe` parts: aux constants `c._unsafe_1`, `_4`, …, `_34`.
def c : Nat :=
  (unsafe t "u1" 1) + (unsafe t "u2" 2) + (unsafe t "u3" 3) + (unsafe t "u4" 4) +
  (unsafe t "u5" 5) + (unsafe t "u6" 6) + (unsafe t "u7" 7) + (unsafe t "u8" 8) +
  (unsafe t "u9" 9) + (unsafe t "u10" 10) + (unsafe t "u11" 11) + (unsafe t "u12" 12)

def last : Nat := t "last" 9

def main : IO Unit := do
  IO.eprintln "main"
  IO.println s!"{first} {zz} {aa} {foo} {foo.bar} {userA} {zi} {ai} {(default : Zed).tag} {(default : Abe).tag} {c} {last}"
