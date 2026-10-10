/-! Runtime test: optimization `flatten-structs` must not change Lean's
borrow flag of a parameter that holds a resource through a callee that
gets a field of it (found in the review of `ResourceFlow`; a bug of dev
615a9618 too). `report (ctx : Ctx)` writes through `ctx.h`, passes
`ctx.cfg` (two numbers, no resource) to `loopE`, which updates its record
in place (an owned parameter), and then reads the file. Natively Lean's
inference takes `ctx` owned (`loopE`'s parameter is owned, and an owned
field makes its object owned), so `report` releases `ctx`, and the handle
is flushed and closed, at its last use, before the read: `[hello]`. The
pass split `loopE`, whose wrapper only projects its record: Lean's
inference on lean2rr's code took `ctx` borrowed, the caller kept it until
`report` returned, and the read saw `[]`. The pass now leaves alone every
declaration whose flags decide such a flag (`flagSources`): `loopE`, and
for `report2` also `relay`, which passes the field on to `loopE`
(`RtFlattenResOwner.l2r-debug`). For `report3`, `mix` gets the field as
`c` and joins it with its other record `d` in a join point (`if b then c
else d`), and passes `d` to `grow`, which owns it: natively `d` is owned,
so the join point's parameter, so `c`, so `ctx`. The walk from `c` must
follow the edges of the inference both ways (review of the analysis,
finding 3: from `c` to the join point only, `grow` was split). -/

structure Config where
  a : UInt64
  b : UInt64

structure Ctx where
  h : IO.FS.Handle
  cfg : Config

@[noinline] def loopE (c : Config) : Nat → UInt64
  | 0 => c.a + c.b
  | n + 1 => loopE { c with a := c.a + 1, b := c.b * 3 } n

@[noinline] def relay (c : Config) (n : Nat) : UInt64 := loopE c n + 1

@[noinline] def report (ctx : Ctx) (path : System.FilePath) : IO String := do
  ctx.h.putStr "hello"
  let r := loopE ctx.cfg 10
  IO.println s!"r = {r}"
  let s ← IO.FS.readFile path
  return s!"[{s}]"

@[noinline] def grow (c : Config) : Nat → UInt64
  | 0 => c.a + c.b
  | n + 1 => grow { c with a := c.a + 1, b := c.b * 3 } n

@[noinline] def mix (c d : Config) (b : Bool) (k : Nat) : UInt64 :=
  let x := if b then c else d
  let r := grow d 2
  x.a * r + x.b * (r + 1) + (x.a ^ k) + (x.b ^ (k + 1)) + x.a * x.b * r + (x.a + r) * (x.b + r)

@[noinline] def report3 (ctx : Ctx) (path : System.FilePath) (b : Bool) : IO String := do
  ctx.h.putStr "third"
  let r := mix ctx.cfg ⟨5, 6⟩ b 3
  IO.println s!"r = {r}"
  let s ← IO.FS.readFile path
  return s!"[{s}]"

@[noinline] def report2 (ctx : Ctx) (path : System.FilePath) : IO String := do
  ctx.h.putStr "again"
  let r := relay ctx.cfg 5
  IO.println s!"r = {r}"
  let s ← IO.FS.readFile path
  return s!"[{s}]"

def main (args : List String) : IO Unit := do
  let dir : System.FilePath := "rtflattenresowner-tmp"
  IO.FS.createDirAll dir
  let a := dir / "a.txt"
  let h ← IO.FS.Handle.mk a .write
  IO.println (← report ⟨h, ⟨1, 2⟩⟩ a)
  IO.println s!"after {(← IO.FS.readFile a).length}"
  let b := dir / "b.txt"
  let h2 ← IO.FS.Handle.mk b .write
  IO.println (← report2 ⟨h2, ⟨3, 4⟩⟩ b)
  IO.println s!"after {(← IO.FS.readFile b).length}"
  let c := dir / "c.txt"
  let h3 ← IO.FS.Handle.mk c .write
  IO.println (← report3 ⟨h3, ⟨1, 2⟩⟩ c (args.length == 0))
  IO.println s!"after {(← IO.FS.readFile c).length}"
