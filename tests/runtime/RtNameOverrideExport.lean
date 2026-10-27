/-! Runtime test (a bug hunt of the names lean2rr recognizes, 2026-10-27):
a program's `@[export]` symbol in the form of lean2rr's shim overrides,
`l2r_override_<mangled name>`. Natively the attribute only names a C
symbol. lean2rr replaced every call of `Nat.toDigitsCore` with the
program's definition (`42` for `1234`): `Mono.redirectTarget` looked the
symbol up among every module's exports. Now only the shim's modules
(`L2RShim.*`) replace a definition (`Mono.overrideMap`). The program's
definition is still called by its own name. -/

@[export l2r_override_Nat_toDigitsCore]
def myDigits (_base _fuel _n : Nat) (_acc : List Char) : List Char := ['4', '2']

@[export l2r_override_List_reverse]
def myReverse (l : List Nat) : List Nat := l

def main (args : List String) : IO Unit := do
  let n := args.length + 1234
  IO.println (String.ofList (Nat.toDigitsCore 10 (n + 1) n []))
  IO.println (toString (n + 1))
  IO.println (String.ofList (myDigits 10 1 n []))
  IO.println s!"{(List.range (n % 7)).reverse} {myReverse (List.range (n % 5))}"
