/-! Runtime test: startup order of the declarations of one macro expansion
whose names the macro makes up (hygienic names). They all have the macro
call's position and, from one quotation, the same macro scopes; natively
they start in the order the macro wrote them, which lean2rr reads from the
order in which Lean compiled them (the module's IR-only declarations, such
as their closed terms, are recorded newest first). Also: a constant that
calls no function (no IR-only declaration) but reads a traced constant
starts after it. -/

def t (s : String) (n : Nat) : Nat := dbgTrace s fun _ => n

-- One quotation, three made-up names, in non-alphabetical order.
macro "mk3" : command => `(
  def zz : Nat := t "mk3 zz" 1
  def aa : Nat := t "mk3 aa" 2
  def mm : Nat := t "mk3 mm" 3)
mk3

-- A name from the argument first, then a made-up one.
macro "mkU" n:ident : command => `(
  def $n : Nat := t "mkU user" 10
  def helper : Nat := t "mkU helper" 11)
mkU userA

-- A made-up name first, then one from the argument that uses it.
macro "mkH" n:ident : command => `(
  def helper : Nat := t "mkH helper" 20
  def $n : Nat := t "mkH user" (helper + 1))
mkH userB

-- Nested expansions: each `one` gets fresh macro scopes.
syntax "many" num* : command
macro_rules
  | `(many) => `(section end)
  | `(many $n $ns*) => `(
      def made : Nat := t s!"many {$n}" $n
      many $ns*)
many 5 3 9 1

-- `initialize` declarations with made-up names, the second reading the first.
macro "mkInit" rb:ident : command => `(
  initialize zi : Nat ← do IO.eprintln "init zi"; pure 41
  initialize ai : Nat ← do IO.eprintln s!"init ai reads zi = {zi}"; pure (zi + 1)
  def $rb : Nat := zi + ai)
mkInit readBoth

-- `aa` and `cc` call no function: they start after `bb` and `zz`.
macro "mkR" : command => `(
  def zz : Nat := t "mkR zz" 2
  def bb : Nat := t "mkR bb" 1
  def aa : Nat := bb
  def cc : Nat × Nat := (bb, zz))
mkR

def last : Nat := t "last" 99

def main : IO Unit := do
  IO.eprintln "main"
  IO.println s!"{userA} {userB} {last} {readBoth}"
