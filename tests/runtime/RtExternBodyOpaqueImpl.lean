/-!
An `opaque` with a type-unsafe `@[implemented_by]` (the usual form of an
unsafe implementation), and library functions with type-unsafe
implementations (`Array.modifyM`, `Array.mapFinIdxM`, `List.attachWith`),
called from the Lean definition of an `@[extern]` of the program (lean2rr
runs it, translation plan §5.8); natively the C side
(`RtExternBodyOpaqueImpl.ffi.c`) calls `@[export]` copies of the same
bodies, `ext 41`. lean2rr compiles the extern's definition from source
(`Mono.recompilePasses`), whose `implemented_by` replacement kept `h`
(its implementation is type-unsafe), and `h`, recompiled from source, gave
the opaque's default value: `ext 0`; the library functions ran their
reference definitions (new arrays, not in place). A bug hunt of the extern
routing (repro R4).
-/

unsafe def hImpl (n : Nat) : Nat := (unsafeCast n : Nat) * 2 + 1
@[implemented_by hImpl] opaque h (n : Nat) : Nat

@[extern "rt_eboi_h"] def extH (n : Nat) : Nat := h n
@[extern "rt_eboi_lib"] def extLib (a : Array Nat) : List Nat :=
  let b := Id.run (a.modifyM 0 fun x => pure (x + 100))
  let c := Id.run (b.mapFinIdxM fun i x _ => pure (x + i))
  (c.toList.attachWith (fun _ => True) (fun _ _ => trivial)).map (·.val)

@[export rt_eboi_h_ref] def extHRef (n : Nat) : Nat := h n
@[export rt_eboi_lib_ref] def extLibRef (a : Array Nat) : List Nat :=
  let b := Id.run (a.modifyM 0 fun x => pure (x + 100))
  let c := Id.run (b.mapFinIdxM fun i x _ => pure (x + i))
  (c.toList.attachWith (fun _ => True) (fun _ _ => trivial)).map (·.val)

def main : IO Unit := do
  IO.println s!"direct {h 20}"
  IO.println s!"ext {extH 20} {extLib #[1, 2, 3]}"
