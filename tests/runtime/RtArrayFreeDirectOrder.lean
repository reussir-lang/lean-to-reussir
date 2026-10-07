/-! Runtime test (leanrt-perf-1): the array free calls a boxed payload's
release where the pending stack would pop it next, and the closes come out
in native Lean's order.
- `steps`: an array of `Item`s whose last references the array holds, freed
  outside a free (a reference set gives it up) and inside one (a field of a
  structure that a reference set gives up). Its second pass calls each
  kept payload's release in its step (`any::release_last_in_step`): a
  `num` cell pushes nothing, so the step goes on, and a `two` cell pushes
  its handles, which are closed before the elements before it. Natively
  `lean_del` pops the elements last first: `fedcba`.
- `one`: an array whose other elements are shared (the caller keeps them)
  or `none`, so that it keeps exactly one element of its own; freed outside
  a free, the runtime frees the block and then that element without a step
  (`drop::ReleaseElems::free_single`): a `two` (closed `ba`) and a list
  (closed `edc`), as natively (the cell's fields popped last first).
Each handle's buffered tag reaches the file when the handle is closed. -/

def path : System.FilePath := "afd-tmp.txt"

@[noinline] def openW (tag : String) : IO IO.FS.Handle := do
  let h ← IO.FS.Handle.mk path .append
  h.putStr tag
  pure h

@[noinline] def report (name : String) : IO Unit := do
  IO.println s!"{name} {← IO.FS.readFile path}"
  IO.FS.writeFile path ""

inductive Item where
  | two (a b : IO.FS.Handle)
  | num (x y : UInt64)

/-- Seven elements, each held only by the array (the `num` cells made from
a value read at run time, so that none is a shared constant). -/
@[noinline] def buildSteps : IO (Array Item) := do
  let k := (← IO.monoNanosNow).toUInt64
  let a ← openW "a"; let b ← openW "b"; let c ← openW "c"
  let d ← openW "d"; let e ← openW "e"; let f ← openW "f"
  pure #[.two a b, .num k 2, .num k 4, .two c d, .num k 6, .two e f, .num k 8]

structure Holder (α : Type) where
  n : Nat
  xs : Array α

/-- `[s, own, none, s]`: the caller keeps `s`; `own` is the array's own. -/
@[noinline] def withShared {α : Type} (s own : Option α) : Array (Option α) :=
  #[s, own, none, s]

def main : IO Unit := do
  IO.FS.writeFile path ""
  let r ← IO.mkRef (#[] : Array Item)
  r.set (← buildSteps)
  IO.println s!"steps size {(← r.get).size}"
  r.set #[]
  report "steps"
  let r2 ← IO.mkRef (some (Holder.mk 0 (#[] : Array Item)))
  r2.set (some ⟨1, ← buildSteps⟩)
  IO.println s!"steps in free {(← r2.get).map (·.xs.size)}"
  r2.set none
  report "steps in free"
  let x ← openW "x"; let y ← openW "y"
  let s : Option Item := some (.two x y)
  -- `s` and `sl` stay shared while the arrays are freed: these references
  -- hold them until the end.
  let keep ← IO.mkRef s
  let r3 ← IO.mkRef (#[] : Array (Option Item))
  r3.set (withShared s (some (.two (← openW "a") (← openW "b"))))
  IO.println s!"one size {(← r3.get).size}"
  r3.set #[]
  report "one"
  let p ← openW "p"
  let sl : Option (List IO.FS.Handle) := some [p]
  let keepL ← IO.mkRef sl
  let r4 ← IO.mkRef (#[] : Array (Option (List IO.FS.Handle)))
  r4.set (withShared sl (some [← openW "c", ← openW "d", ← openW "e"]))
  IO.println s!"one list size {(← r4.get).size}"
  r4.set #[]
  report "one list"
  IO.println s!"kept {(← keep.get).isSome} {(← keepL.get).map (·.length)}"
  IO.FS.removeFile path
