/-!
Runtime test of the optimization `unread-fields` (off by default; this
test turns it on, `RtUnreadFieldsExternFn.enable-opts`): an extern used
as a function value. `String.Slice.hash` is passed to `applyTo` and
applied there; the runtime's glue reads the slice's fields. Every field of
a type that an extern takes counts as read, also when no `let` applies the
extern to that argument (review of the pass, F1), and a parameter of a
declaration that is data (`mkSl`'s `String`) is never replaced (F2).
Before the fix the slice's string became a placeholder and the hash was
that of an empty slice.
-/

@[noinline] def mkSl (s : String) : String.Slice := s.toSlice

@[noinline] def applyTo (f : String.Slice → UInt64) (s : String.Slice) : UInt64 := f s

structure S where
  name : String
  count : Nat
  tag : String

@[noinline] def mk (n : Nat) (t : String) (name : String) : S := { name, count := n, tag := t }

def main (args : List String) : IO Unit := do
  let s := s!"hello{args.length}"
  IO.println (applyTo String.Slice.hash (mkSl s))
  let n := args.length + 41
  IO.println s!"name: {(mk n s!"tag{n}" "x").name}"
