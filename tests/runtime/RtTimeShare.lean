import Std.Time
import Std.Sync.Mutex

/-! Externs that lean2rr's shim implements in Lean (`L2RShim`):
`Std.Time.Timestamp.now`, the Windows-only time zone functions (an error
elsewhere), `ShareCommon.Object.eq`/`hash`; and an extern applied to a value
cast from `()` (`unsafeCast ()` becomes a match on a constructor, which the
printer must parenthesize: `match (L2RBox::b0{x}) {`), built but not run. -/

open Std.Time

/-- Locks a mutex conjured from `()`: only built, never called. -/
unsafe def conjuredLock : BaseIO Unit := Std.BaseMutex.lock (unsafeCast ())

unsafe def main : IO Unit := do
  -- The clock: after 2024-01-01 and before 2100-01-01.
  let t ← Timestamp.now
  let s := t.toSecondsSinceUnixEpoch.val
  IO.println s!"now in range: {decide (1704067200 < s ∧ s < 4102444800)}"
  let t2 ← Timestamp.now
  IO.println s!"monotone enough: {decide (t.toSecondsSinceUnixEpoch.val ≤ t2.toSecondsSinceUnixEpoch.val)}"
  -- Windows only: the same errors as natively on other systems.
  try
    let r ← Database.Windows.getNextTransition "UTC" 0 false
    IO.println s!"transition: {r.isSome}"
  catch e => IO.println s!"getNextTransition: {e}"
  try
    let id ← Database.Windows.getLocalTimeZoneIdentifierAt 0
    IO.println s!"zone: {id}"
  catch e => IO.println s!"getLocalTimeZoneIdentifierAt: {e}"
  -- ShareCommon's object comparison, on one object.
  let xs : Array Nat := #[1, 2, 3]
  let o : ShareCommon.Object := unsafeCast xs
  IO.println s!"eq self: {ShareCommon.Object.eq o o}"
  IO.println s!"hash stable: {ShareCommon.Object.hash o == ShareCommon.Object.hash o}"
  if (← IO.getEnv "L2R_TEST_NEVER_SET_RTTIMESHARE").isSome then conjuredLock
  IO.println "done"
