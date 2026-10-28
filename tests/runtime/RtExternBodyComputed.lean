/-!
A type with a computed field (Lean implements its constructors, `casesOn`
and field through `unsafe` `_override` definitions that cast, and
represents its values by the implementation type `Foo._impl`) built and
read in the Lean definition of an `@[extern]` of the program (lean2rr runs
it, translation plan §5.8); natively the C side
(`RtExternBodyComputed.ffi.c`) calls `@[export]` copies of the same bodies.
lean2rr compiles the extern's definition from source
(`Mono.recompilePasses`), whose `implemented_by` replacement kept
`Foo.a` (its `_override` is type-unsafe), and the program was refused:
`constructor Foo.a not in type T_Foo__impl`. A bug hunt of the extern
routing (repro R2).
-/

inductive Foo where
  | a (n : Nat)
  | b (s : String)
with
  @[computed_field] tag : Foo → Nat
    | .a n => n * 10
    | .b s => s.length + 1000

@[extern "rt_ebc_mk"] def mkFoo (n : Nat) : Foo := .a n
@[extern "rt_ebc_tag"] def tagOf (x : Foo) : Nat := x.tag
@[extern "rt_ebc_name"] def nameOf (x : Foo) : String := match x with
  | .a n => s!"a{n}"
  | .b s => s!"b{s}"

@[export rt_ebc_mk_ref] def mkFooRef (n : Nat) : Foo := .a n
@[export rt_ebc_tag_ref] def tagOfRef (x : Foo) : Nat := x.tag
@[export rt_ebc_name_ref] def nameOfRef (x : Foo) : String := match x with
  | .a n => s!"a{n}"
  | .b s => s!"b{s}"

def main : IO Unit := do
  let x := mkFoo 4
  IO.println s!"{x.tag} {tagOf x} {tagOf (.b "hello")} {(mkFoo 7).tag} {nameOf x} {nameOf (.b "q")}"
  match mkFoo 3 with
  | .a n => IO.println s!"a {n}"
  | .b s => IO.println s!"b {s}"
