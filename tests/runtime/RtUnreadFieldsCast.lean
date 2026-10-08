/-!
Runtime test of the optimization `unread-fields` (off by default; this
test turns it on, `RtUnreadFieldsCast.enable-opts`): a callback read only
through `unsafeCast`. `Hook.run` is never projected or matched; `main`
reads the hooks as `Other`, a structure of the same layout, and calls its
field `call`, which natively is the hook's `run`. A program that can read
a value as another type (`programCasts`: here an `unsafe` declaration of
the program) keeps every field, so the callbacks run as natively.
-/

structure Hook where
  name : String
  run : Nat → String

structure Other where
  label : String
  call : Nat → String
deriving Inhabited

initialize hooksRef : IO.Ref (Array Hook) ← IO.mkRef #[]

initialize hooksRef.modify (·.push { name := "a", run := fun n => s!"a ran with {n}" })
initialize hooksRef.modify (·.push { name := "b", run := fun n => s!"b ran with {n * 10}" })

unsafe def asOtherImpl (h : Hook) : Other := unsafeCast h

@[implemented_by asOtherImpl] opaque asOther (h : Hook) : Other

def main (args : List String) : IO Unit := do
  for h in (← hooksRef.get) do
    let o := asOther h
    IO.println s!"{o.label}: {o.call (args.length + 3)}"
