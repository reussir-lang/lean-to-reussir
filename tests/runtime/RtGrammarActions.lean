/-! Runtime test: the semantic values of a small grammar (a JSON subset). A
symbol's value type is computed from the symbol (`Sym.sem`) and a right-hand
side's from the list of its symbols (`Syms.sem`, a nested tuple); each
production carries a predicate and an action over those types in a Sigma
table, so the parser handles every value in the uniform representation: list
values built by one action flow into another action's constructor, a leaf goes
to a polymorphic predicate, one dispatcher destructures every right-hand side.
Tuples are also concatenated and reversed along `xs ++ ys` and `xs.reverse`
with `cast`, and a heterogeneous stack of symbol values is shown.
A coverage test from Crane's test corpus (Bloomberg's Rocq-to-C++ extractor,
whose regression tests document shapes that broke a typed, reference-counted
code generator); the code is new, the shapes are those of Crane's
tests/regression/action_container_cast, grammar_action_pairlist_crash,
grammar_pairlist_nil_cons_mismatch, grammar_poly_pairlist_pred,
grammar_record_list_field, sigt_fn_any, sigt_prod_fn_any_lit_pair,
sigt_leaf_forward_dispatcher, obj_nil_erasure_mismatch,
list_cons_erasure_bleed, erased_singleton_unit_tuple, any_cast_nested_pair.
From the round-9 review, area crane (rv9/crane), program CrGram. -/

namespace RtGrammarActions

def Tup : List Type → Type
  | [] => Unit
  | t :: ts => t × Tup ts

inductive J | arr (xs : List J) | num (n : Nat) | str (s : String) | obj (kv : List (String × J))
partial def J.render : J → String
  | .arr xs => "[" ++ ",".intercalate (xs.map J.render) ++ "]"
  | .num n => toString n
  | .str s => "\"" ++ s ++ "\""
  | .obj kv => "{" ++ ",".intercalate (kv.map fun (k, v) => s!"{k}:{v.render}") ++ "}"

inductive Term | lbr | rbr | lbrace | rbrace | comma | colon | num | str
  deriving DecidableEq
inductive NT | value | arr | elems | obj | pairs | pair
  deriving DecidableEq, Repr
inductive Sym | t (a : Term) | n (x : NT)

def Term.sem : Term → Type
  | .num => Nat
  | .str => String
  | _ => Unit
def NT.sem : NT → Type
  | .value => J
  | .arr => List J
  | .elems => List J
  | .obj => List (String × J)
  | .pairs => List (String × J)
  | .pair => String × J
def Sym.sem : Sym → Type
  | .t a => a.sem
  | .n x => x.sem
def Syms.sem (g : List Sym) : Type := Tup (g.map Sym.sem)

structure Prod where
  id : Nat
  lhs : NT
  rhs : List Sym
def Prod.Act (p : Prod) : Type := Syms.sem p.rhs → p.lhs.sem
def Prod.Pred (p : Prod) : Type := Syms.sem p.rhs → Bool
def Entry : Type := (p : Prod) × (p.Pred × p.Act)

def T (a : Term) : Sym := .t a
def N (x : NT) : Sym := .n x

def prods : List Prod :=
  [ ⟨0, .value, [T .num]⟩, ⟨1, .value, [T .str]⟩, ⟨2, .value, [N .arr]⟩, ⟨3, .value, [N .obj]⟩,
    ⟨4, .arr, [T .lbr, T .rbr]⟩, ⟨5, .arr, [T .lbr, N .elems, T .rbr]⟩,
    ⟨6, .elems, [N .value]⟩, ⟨7, .elems, [N .value, T .comma, N .elems]⟩,
    ⟨8, .obj, [T .lbrace, T .rbrace]⟩, ⟨9, .obj, [T .lbrace, N .pairs, T .rbrace]⟩,
    ⟨10, .pairs, [N .pair]⟩, ⟨11, .pairs, [N .pair, T .comma, N .pairs]⟩,
    ⟨12, .pair, [T .str, T .colon, N .value]⟩ ]

-- A polymorphic predicate that receives an erased leaf (grammar_poly_pairlist_pred).
@[noinline] def nodupKeys {β : Type} : List (String × β) → Bool
  | [] => true
  | (k, _) :: r => !(r.any (·.1 == k)) && nodupKeys r

-- One dispatcher with one match over the production (sigt_leaf_forward_dispatcher):
-- each arm destructures the nested tuple of its right-hand side.
@[noinline] def mkAction (p : Prod) : p.Act :=
  match p with
  | ⟨0, .value, [.t .num]⟩ => fun (n, ()) => J.num n
  | ⟨1, .value, [.t .str]⟩ => fun (s, ()) => J.str s
  | ⟨2, .value, [.n .arr]⟩ => fun (l, ()) => J.arr l
  | ⟨3, .value, [.n .obj]⟩ => fun (kv, ()) => J.obj kv
  | ⟨4, .arr, [.t .lbr, .t .rbr]⟩ => fun _ => []
  | ⟨5, .arr, [.t .lbr, .n .elems, .t .rbr]⟩ => fun ((), (es, ((), ()))) => es
  | ⟨6, .elems, [.n .value]⟩ => fun (v, ()) => [v]
  | ⟨7, .elems, [.n .value, .t .comma, .n .elems]⟩ => fun (v, ((), (es, ()))) => v :: es
  | ⟨8, .obj, [.t .lbrace, .t .rbrace]⟩ => fun _ => []
  | ⟨9, .obj, [.t .lbrace, .n .pairs, .t .rbrace]⟩ => fun ((), (kv, ((), ()))) => kv
  | ⟨10, .pairs, [.n .pair]⟩ => fun (p, ()) => [p]
  | ⟨11, .pairs, [.n .pair, .t .comma, .n .pairs]⟩ => fun (p, ((), (kv, ()))) => p :: kv
  | ⟨12, .pair, [.t .str, .t .colon, .n .value]⟩ => fun (k, ((), (v, ()))) => (k, v)
  | p => fun _ => match p with
    | ⟨_, .value, _⟩ => J.num 0 | ⟨_, .arr, _⟩ => [] | ⟨_, .elems, _⟩ => []
    | ⟨_, .obj, _⟩ => [] | ⟨_, .pairs, _⟩ => [] | ⟨_, .pair, _⟩ => ("", J.num 0)

@[noinline] def mkPred (p : Prod) : p.Pred :=
  match p with
  | ⟨9, .obj, [.t .lbrace, .n .pairs, .t .rbrace]⟩ => fun ((), (kv, ((), ()))) => nodupKeys kv
  | ⟨2, .value, [.n .arr]⟩ => fun (l, ()) => l.length < 100
  | _ => fun _ => true

def entries : List Entry := prods.reverse.map fun p => ⟨p, (mkPred p, mkAction p)⟩

inductive Tok | lbr | rbr | lbrace | rbrace | comma | colon | num (n : Nat) | str (s : String)

def Tok.is : Tok → Term → Bool
  | .lbr, .lbr | .rbr, .rbr | .lbrace, .lbrace | .rbrace, .rbrace => true
  | .comma, .comma | .colon, .colon | .num _, .num | .str _, .str => true
  | _, _ => false

partial def lex (cs : List Char) (acc : Array Tok) : Array Tok :=
  match cs with
  | [] => acc
  | '[' :: r => lex r (acc.push .lbr)
  | ']' :: r => lex r (acc.push .rbr)
  | '{' :: r => lex r (acc.push .lbrace)
  | '}' :: r => lex r (acc.push .rbrace)
  | ',' :: r => lex r (acc.push .comma)
  | ':' :: r => lex r (acc.push .colon)
  | '"' :: r =>
    let s := r.takeWhile (· != '"')
    lex (r.drop (s.length + 1)) (acc.push (.str (String.ofList s)))
  | c :: r =>
    if c.isDigit then
      let d := (c :: r).takeWhile Char.isDigit
      lex ((c :: r).drop d.length) (acc.push (.num (String.ofList d).toNat!))
    else lex r acc

-- first-token test for choosing a production (LL(1) on this grammar)
def firstOk : List Sym → List Tok → Bool
  | [], _ => true
  | .t a :: _, t :: _ => t.is a
  | .t _ :: _, [] => false
  | .n x :: rest, ts => match x, ts with
    | .value, t :: _ => t.is .num || t.is .str || t.is .lbr || t.is .lbrace
    | .arr, t :: _ => t.is .lbr
    | .obj, t :: _ => t.is .lbrace
    | .elems, t :: _ => t.is .num || t.is .str || t.is .lbr || t.is .lbrace
    | .pairs, t :: _ => t.is .str
    | .pair, t :: _ => t.is .str
    | _, [] => rest.isEmpty && false

-- how far a production's right-hand side reaches, for the two-way choices
def better (e : Entry) (ts : List Tok) : Bool :=
  match e.1.id, ts with
  | 4, _ :: t :: _ => t.is .rbr
  | 5, _ :: t :: _ => !(t.is .rbr)
  | 8, _ :: t :: _ => t.is .rbrace
  | 9, _ :: t :: _ => !(t.is .rbrace)
  | _, _ => true

mutual
partial def parseSym (s : Sym) (ts : List Tok) : Option (s.sem × List Tok) :=
  match s, ts with
  | .t .num, .num n :: r => some (n, r)
  | .t .str, .str x :: r => some (x, r)
  | .t a, t :: r => if t.is a then (match a with
      | .lbr | .rbr | .lbrace | .rbrace | .comma | .colon => some ((), r)
      | .num | .str => none) else none
  | .t _, [] => none
  | .n x, ts => parseNT x ts (entries.filter fun e => decide (e.1.lhs = x))
partial def parseNT (x : NT) (ts : List Tok) : List Entry → Option (x.sem × List Tok)
  | [] => none
  | e :: es =>
    if h : e.1.lhs = x then
      if firstOk e.1.rhs ts && better e ts then
        match parseSyms e.1.rhs ts with
        | some (vs, r) =>
          if e.2.1 vs then some (h ▸ e.2.2 vs, r) else parseNT x ts es
        | none => parseNT x ts es
      else parseNT x ts es
    else parseNT x ts es
partial def parseSyms (g : List Sym) (ts : List Tok) : Option (Syms.sem g × List Tok) :=
  match g with
  | [] => some ((), ts)
  | s :: rest =>
    match parseSym s ts with
    | some (v, r) =>
      match parseSyms rest r with
      | some (vs, r') => some ((v, vs), r')
      | none => none
    | none => none
end

-- concatenating and reversing tuples along the symbol lists
def concatT : (xs ys : List Sym) → Syms.sem xs → Syms.sem ys → Syms.sem (xs ++ ys)
  | [], _, _, vs' => vs'
  | _ :: xs, ys, (v, vs), vs' => (v, concatT xs ys vs vs')

def revT : (xs : List Sym) → Syms.sem xs → Syms.sem xs.reverse
  | [], () => ()
  | x :: xs, (v, vs) =>
    cast (congrArg Syms.sem List.reverse_cons.symm) (concatT xs.reverse [x] (revT xs vs) (v, ()))

-- a heterogeneous stack of symbol values (sigt_list_heterogeneous_box)
def showSem : (s : Sym) → s.sem → String
  | .t .num, (n : Nat) => s!"#{n}"
  | .t .str, (x : String) => s!"'{x}'"
  | .t _, _ => "."
  | .n .value, v => v.render
  | .n .arr, l => s!"arr{l.length}"
  | .n .elems, l => s!"elems{l.length}"
  | .n .obj, kv => s!"obj{kv.length}"
  | .n .pairs, kv => s!"pairs{kv.length}"
  | .n .pair, p => s!"pair:{p.1}"

def showTup : (g : List Sym) → Syms.sem g → List String
  | [], () => []
  | s :: g, (v, vs) => showSem s v :: showTup g vs

@[noinline] def parse (src : String) : String :=
  match parseSym (.n .value) (lex src.toList #[]).toList with
  | some (v, []) => v.render
  | some (v, r) => s!"{v.render} (+{r.length} tokens)"
  | none => "no parse"

def main (args : List String) : IO Unit := do
  let k := args.length
  let srcs := ["[]", "{}", "[1,2,3]", "{\"a\":1}", "{\"a\":[],\"b\":{}}",
    s!"[[],[{k}],[[{k + 1}]],\{\"x\":[1,\{\"y\":\"z\"}]}]", "{\"a\":1,\"a\":2}", "[1,", "\"s\""]
  for s in srcs do IO.println s!"parse {s} => {parse s}"
  let g1 : List Sym := [T .num, N .elems]
  let g2 : List Sym := [T .str, N .value, T .comma]
  let v1 : Syms.sem g1 := (5 + k, ([J.num 1, J.str "q"], ()))
  let v2 : Syms.sem g2 := ("w", (J.arr [J.num k], ((), ())))
  let c := concatT g1 g2 v1 v2
  IO.println s!"concat {showTup (g1 ++ g2) c}"
  let r := revT (g1 ++ g2) c
  IO.println s!"rev {showTup (g1 ++ g2).reverse r}"
  let stack : List ((s : Sym) × s.sem) := [⟨T .num, (3 + k : Nat)⟩, ⟨N .elems, [J.num 2]⟩, ⟨N .pair, ("k", J.str "v")⟩, ⟨T .comma, ()⟩]
  IO.println s!"stack {stack.map fun e => showSem e.1 e.2}"
  let acts := entries.map fun e => (e.1.id, e.1.rhs.length)
  IO.println s!"entries {acts}"

end RtGrammarActions

def main (args : List String) : IO Unit := RtGrammarActions.main args
