/-! Runtime test: native Lean's borrow inference takes every parameter of
an exported declaration (`@[export]`, and `main`) owned (`isExport`, by
name), so a handle's last use inside such a declaration closes (and
flushes) it there. lean2rr ran the inference on its instances
(`helper._l2r_0`), which have other names: their parameters were inferred
borrowed, the caller kept the handle until the call returned, and the
helper read an empty file (hunt3 own, `helper read []`).
- `helper h path`: exported; writes to the handle, then reads the file;
- `wrap h path`: not exported; passes its handle to `helper`'s owned
  parameter, so natively it owns it too (the handle closes inside
  `helper` again);
- `plain h path`: the same body, not exported: the handle is borrowed and
  stays open (nothing read). -/

@[export rt_borrow_export_helper, noinline]
def helper (h : IO.FS.Handle) (path : System.FilePath) : IO String := do
  h.putStr "hello"
  IO.FS.readFile path

@[noinline] def wrap (h : IO.FS.Handle) (path : System.FilePath) : IO String := do
  let s ← helper h path
  return s ++ "."

@[noinline] def plain (h : IO.FS.Handle) (path : System.FilePath) : IO String := do
  h.putStr "hello"
  IO.FS.readFile path

def main : IO Unit := do
  let dir : System.FilePath := "rtborrowexport-tmp"
  IO.FS.createDirAll dir
  let a := dir / "a.txt"
  let h ← IO.FS.Handle.mk a .write
  IO.println s!"helper read [{← helper h a}]"
  let b := dir / "b.txt"
  let hb ← IO.FS.Handle.mk b .write
  IO.println s!"wrap read [{← wrap hb b}]"
  let c := dir / "c.txt"
  let hc ← IO.FS.Handle.mk c .write
  IO.println s!"plain read [{← plain hc c}] after [{← IO.FS.readFile c}]"
  IO.FS.removeDirAll dir
