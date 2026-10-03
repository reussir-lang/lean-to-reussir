/-! Runtime test: the old value of an overwritten reference is released as
native `lean_st_ref_set` does (`lean_dec`): what it holds goes last
first, through lists, tuples, structures, options and arrays, so the
`sync` dependents of the promises it drops run in that order, before the
next statement. -/

structure Two where
  a : IO.Promise Unit
  b : IO.Promise Unit

def dep (log : IO.Ref (Array String)) (tag : String) : IO (IO.Promise Unit) := do
  let p ← IO.Promise.new
  let _ ← BaseIO.mapTask (sync := true) (t := p.result?) fun _ => log.modify (·.push tag)
  pure p

def main : IO Unit := do
  let log ← IO.mkRef (#[] : Array String)
  -- a list in a ref
  let rl ← IO.mkRef ([] : List (IO.Promise Unit))
  let l ← [0, 1, 2, 3].mapM fun i => dep log s!"L{i}"
  rl.set l
  rl.set []
  IO.println s!"list: {← log.swap #[]}"
  -- a tuple in a ref
  let p0 ← dep log "T0"
  let p1 ← dep log "T1"
  let rt ← IO.mkRef (p0, p1)
  let q ← IO.Promise.new
  rt.set (q, q)
  IO.println s!"tuple: {← log.swap #[]}"
  -- a structure in a ref
  let s0 ← dep log "S0"
  let s1 ← dep log "S1"
  let rs ← IO.mkRef ({ a := s0, b := s1 } : Two)
  let q2 ← IO.Promise.new
  rs.set { a := q2, b := q2 }
  IO.println s!"structure: {← log.swap #[]}"
  -- an Option of a list
  let rol ← IO.mkRef (none : Option (List (IO.Promise Unit)))
  let l2 ← [0, 1, 2].mapM fun i => dep log s!"O{i}"
  rol.set (some l2)
  rol.set none
  IO.println s!"option of a list: {← log.swap #[]}"
  -- an array of lists
  let ra ← IO.mkRef (#[] : Array (List (IO.Promise Unit)))
  let a0 ← [0, 1].mapM fun i => dep log s!"A0.{i}"
  let a1 ← [0, 1].mapM fun i => dep log s!"A1.{i}"
  ra.set #[a0, a1]
  ra.set #[]
  IO.println s!"array of lists: {← log.swap #[]}"
