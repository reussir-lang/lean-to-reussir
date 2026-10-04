/-! Runtime test: placeholders (`box(0)`, written into an array slot by
`Array.map`/`modify` and into a reference by `IO.Ref.modify`) of types
whose only constructor holds a thunk of the type itself: such a type has
values (built here with unsafe code), and its placeholder holds a thunk
cell that is never forced. Also a structure whose field is an array of the
type itself.
From review round 9, area C (RV9C-01), next to `RtZeroFinite`. -/
structure S where
  h : Nat
  t : Thunk S

-- `S` has no value in the logic (each needs another), only at run time.
axiom S.nonempty : Nonempty S
instance : Nonempty S := S.nonempty

unsafe def mkSU (n : Nat) : S := ⟨n, Thunk.mk fun _ => mkSU (n + 1)⟩
@[implemented_by mkSU] opaque mkS (n : Nat) : S

structure Node where
  v : Nat
  kids : Array Node

def main : IO Unit := do
  let ss := #[mkS 1, mkS 5].map fun s => { s with h := s.h + 10 }
  IO.println s!"thunk {ss.map (·.h)} {ss.map (·.t.get.h)}"
  let ss2 := ss.modify 1 fun s => { s with h := s.h * 3 }
  IO.println s!"modify {ss2.map (·.h)} {ss2.map (·.t.get.h)}"
  let r ← IO.mkRef (mkS 7)
  r.modify fun s => { s with h := s.h + 1 }
  IO.println s!"ref {(← r.get).h}"
  let ns := #[Node.mk 1 #[], Node.mk 2 #[Node.mk 3 #[]]].map fun n => { n with v := n.v + n.kids.size }
  IO.println s!"node {ns.map (·.v)}"
