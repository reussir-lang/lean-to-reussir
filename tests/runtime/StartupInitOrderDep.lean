prelude
import Init.System.IO

/-! Companion module of RtStartupInitOrder (`RtStartupInitOrder.deps`): a
`prelude` module, so it does not import `Init.Data.Random`. Its initializer
prints, then takes every free descriptor and keeps them. -/

partial def fill (acc : Array IO.FS.Handle) : IO (Array IO.FS.Handle) := do
  match ← (IO.FS.Handle.mk "/dev/null" .read).toBaseIO with
  | .ok h => if acc.size < 1000 then fill (acc.push h) else return acc
  | .error _ => return acc

initialize held : Array IO.FS.Handle ← do
  IO.println "companion initializer"
  fill #[]
