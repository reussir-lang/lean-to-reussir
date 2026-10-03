/-! Runtime test: file handles held by the old value of an overwritten
reference are closed (each close flushes its buffer at its own offset) in
native `lean_st_ref_set`'s order (`lean_dec`: the last held first), which
shows in the file's contents: one handle, an array, a structure in an
`Option`, a list, a tuple, an array and a list in a tuple. -/

structure Two where
  a : IO.FS.Handle
  b : IO.FS.Handle

def openW (p : String) (s : String) : IO IO.FS.Handle := do
  let h ← IO.FS.Handle.mk p .write
  h.putStr s
  pure h

def showF (lbl p : String) : IO Unit := do
  IO.println s!"{lbl}: {← IO.FS.readFile p}"

def main : IO Unit := do
  let d := "/tmp/rtrefsetfiles-" ++ toString (← IO.monoNanosNow)
  IO.FS.createDirAll d
  let r ← IO.mkRef (← openW s!"{d}/one" "AAAA")
  r.set (← openW s!"{d}/two" "BB")
  showF "1 one handle" s!"{d}/one"
  let f2 := s!"{d}/arr"
  let a1 ← openW f2 "11111111"
  let a2 ← IO.FS.Handle.mk f2 .readWrite
  a2.putStr "22"
  let ra ← IO.mkRef #[a1, a2]
  ra.set #[]
  showF "2 array" f2
  let f3 := s!"{d}/struct"
  let h1 ← openW f3 "33333333"
  let h2 ← IO.FS.Handle.mk f3 .readWrite
  h2.putStr "44"
  let rs ← IO.mkRef (some ({ a := h1, b := h2 } : Two))
  rs.set none
  showF "3 structure" f3
  let f4 := s!"{d}/list"
  let g1 ← openW f4 "55555555"
  let g2 ← IO.FS.Handle.mk f4 .readWrite
  g2.putStr "666"
  let g3 ← IO.FS.Handle.mk f4 .readWrite
  g3.putStr "7"
  let rl ← IO.mkRef [g1, g2, g3]
  rl.set []
  showF "4 list" f4
  let f5 := s!"{d}/tuple"
  let k1 ← openW f5 "88888888"
  let k2 ← IO.FS.Handle.mk f5 .readWrite
  k2.putStr "99"
  let rt ← IO.mkRef (k1, k2)
  let k3 ← IO.FS.Handle.mk s!"{d}/other" .write
  rt.set (k3, k3)
  showF "5 tuple" f5
  let f6 := s!"{d}/nested"
  let m1 ← openW f6 "aaaaaaaa"
  let m2 ← IO.FS.Handle.mk f6 .readWrite
  m2.putStr "bb"
  let m3 ← IO.FS.Handle.mk f6 .readWrite
  m3.putStr "c"
  let rn ← IO.mkRef (#[m1, m2], [m3])
  rn.set (#[], [])
  showF "6 array and list" f6
  IO.FS.removeDirAll d
