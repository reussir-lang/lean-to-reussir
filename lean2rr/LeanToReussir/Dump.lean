import Lean

/-!
# Typed LCNF dumps

Lean's LCNF pretty printer omits binder types. lean2rr's correctness
depends on them, so this printer shows every binder with its type.
-/

namespace LeanToReussir
open Lean Compiler LCNF

def fmtArg : Arg .pure → String
  | .erased => "◾"
  | .fvar id => s!"{id.name}"
  | .type e _ => s!"@({e})"

def fmtArgs (args : Array (Arg .pure)) : String :=
  " ".intercalate (args.toList.map fmtArg)

def fmtLetValue : LetValue .pure → String
  | .lit (.nat n) => toString n
  | .lit (.str s) => s.quote
  | .lit (.uint8 n) | .lit (.uint16 n) => s!"{n}"
  | .lit (.uint32 n) => s!"{n}"
  | .lit (.uint64 n) | .lit (.usize n) => s!"{n}"
  | .erased => "◾"
  | .proj s i x _ => s!"{x.name}.{s}#{i}"
  | .const n _ args _ => s!"{n} {fmtArgs args}"
  | .fvar f args => s!"{f.name} {fmtArgs args}"
  | _ => "<impure>"

def fmtParam (p : Param .pure) : String :=
  s!"({p.binderName}#{p.fvarId.name} : {p.type})"

partial def fmtCode (ind : String) : Code .pure → String
  | .let d k => s!"{ind}let {d.binderName}#{d.fvarId.name} : {d.type} := {fmtLetValue d.value}\n" ++ fmtCode ind k
  | .fun d k _ =>
    s!"{ind}fun {d.binderName}#{d.fvarId.name} {" ".intercalate (d.params.toList.map fmtParam)} : {d.type} :=\n"
      ++ fmtCode (ind ++ "  ") d.value ++ fmtCode ind k
  | .jp d k =>
    s!"{ind}jp {d.binderName}#{d.fvarId.name} {" ".intercalate (d.params.toList.map fmtParam)} :=\n"
      ++ fmtCode (ind ++ "  ") d.value ++ fmtCode ind k
  | .jmp j args => s!"{ind}jmp {j.name} {fmtArgs args}\n"
  | .return x => s!"{ind}return {x.name}\n"
  | .unreach ty => s!"{ind}unreach : {ty}\n"
  | .cases c =>
    s!"{ind}cases {c.discr.name} : {c.typeName} (result {c.resultType})\n" ++
      String.join (c.alts.toList.map fun alt =>
        match alt with
        | .alt ctor ps code _ =>
          s!"{ind}| {ctor} {" ".intercalate (ps.toList.map fmtParam)} =>\n" ++ fmtCode (ind ++ "    ") code
        | .default code => s!"{ind}| _ =>\n" ++ fmtCode (ind ++ "    ") code
        | _ => s!"{ind}| <impure>\n")
  | _ => s!"{ind}<impure>\n"

def fmtDecl (d : Decl .pure) : String :=
  let head := s!"def {d.name} {" ".intercalate (d.params.toList.map fmtParam)} : {d.type}"
  match d.value with
  | .code c => head ++ " :=\n" ++ fmtCode "  " c
  | .extern _ => head ++ " := extern\n"

end LeanToReussir
