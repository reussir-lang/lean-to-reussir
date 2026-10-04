import Lean.Shell

/-!
An `opaque` re-declaration of `lean_decode_lossy_utf8`, the runtime's
function of `Lean.decodeLossyUTF8`, which is a private declaration of
`Lean.Shell` (module system): an extern of the program is never bound to
Lean's runtime, and a program can call that declaration only from a
`module` file that imports it with `import all Lean.Shell`; lean2rr refuses
the extern saying so, by the declaration's user-facing name, and advises
no call (reviews REB-10, REB-12; before, it advised calling
`_private.Lean.Shell.0.Lean.decodeLossyUTF8`). The same for
`lean_io_eprintln`, only the `@[export]` of a private definition of Init
(`IO.eprintlnAux` of `Init.System.IO`; review REB-18: the refusal named it
`_private.Init.System.IO.0.IO.eprintlnAux` and advised calling it). Native
Lean compiles the program (`lean -c`).
-/

@[extern "lean_decode_lossy_utf8"]
opaque decodeLossy : @& ByteArray → String

@[extern "lean_io_eprintln"]
opaque myEp : @& String → BaseIO Unit

def main : IO Unit := do
  IO.println (decodeLossy "a".toUTF8)
  myEp "x"
