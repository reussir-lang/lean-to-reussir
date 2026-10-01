/-! Runtime test: arrays of enumerations (and of `Unit`), which lean2rr
stores as indices (translation plan §5.1): literals, `push`, `set!`,
`modify`, `map` in place and between representations, folds, `reverse`,
`qsort`, `toList`, `BEq`, nested arrays, an enumeration with more than 256
constructors, arrays in structures and in existential packages, casts
between arrays of enumerations, `UInt8` and `Nat`. -/

inductive Dir | n | e | s | w deriving Repr, BEq, Inhabited, Ord, Hashable

def Dir.turn : Dir → Dir | .n => .e | .e => .s | .s => .w | .w => .n

def Dir.ofNat (i : Nat) : Dir := match i % 4 with | 0 => .n | 1 => .e | 2 => .s | _ => .w

inductive Big where
  | c0 | c1 | c2 | c3 | c4 | c5 | c6 | c7 | c8 | c9 | c10 | c11 | c12 | c13 | c14 | c15
  | c16 | c17 | c18 | c19 | c20 | c21 | c22 | c23 | c24 | c25 | c26 | c27 | c28 | c29 | c30 | c31
  | c32 | c33 | c34 | c35 | c36 | c37 | c38 | c39 | c40 | c41 | c42 | c43 | c44 | c45 | c46 | c47
  | c48 | c49 | c50 | c51 | c52 | c53 | c54 | c55 | c56 | c57 | c58 | c59 | c60 | c61 | c62 | c63
  | c64 | c65 | c66 | c67 | c68 | c69 | c70 | c71 | c72 | c73 | c74 | c75 | c76 | c77 | c78 | c79
  | c80 | c81 | c82 | c83 | c84 | c85 | c86 | c87 | c88 | c89 | c90 | c91 | c92 | c93 | c94 | c95
  | c96 | c97 | c98 | c99 | c100 | c101 | c102 | c103 | c104 | c105 | c106 | c107 | c108 | c109
  | c110 | c111 | c112 | c113 | c114 | c115 | c116 | c117 | c118 | c119 | c120 | c121 | c122 | c123
  | c124 | c125 | c126 | c127 | c128 | c129 | c130 | c131 | c132 | c133 | c134 | c135 | c136 | c137
  | c138 | c139 | c140 | c141 | c142 | c143 | c144 | c145 | c146 | c147 | c148 | c149 | c150 | c151
  | c152 | c153 | c154 | c155 | c156 | c157 | c158 | c159 | c160 | c161 | c162 | c163 | c164 | c165
  | c166 | c167 | c168 | c169 | c170 | c171 | c172 | c173 | c174 | c175 | c176 | c177 | c178 | c179
  | c180 | c181 | c182 | c183 | c184 | c185 | c186 | c187 | c188 | c189 | c190 | c191 | c192 | c193
  | c194 | c195 | c196 | c197 | c198 | c199 | c200 | c201 | c202 | c203 | c204 | c205 | c206 | c207
  | c208 | c209 | c210 | c211 | c212 | c213 | c214 | c215 | c216 | c217 | c218 | c219 | c220 | c221
  | c222 | c223 | c224 | c225 | c226 | c227 | c228 | c229 | c230 | c231 | c232 | c233 | c234 | c235
  | c236 | c237 | c238 | c239 | c240 | c241 | c242 | c243 | c244 | c245 | c246 | c247 | c248 | c249
  | c250 | c251 | c252 | c253 | c254 | c255 | c256 | c257 | c258 | c259 | c260 | c261 | c262 | c263
  deriving Repr, BEq, Inhabited

def Big.ofIdx (i : Nat) : Big := match i % 4 with
  | 0 => .c3 | 1 => .c255 | 2 => .c256 | _ => .c263

structure Grid where
  cells : Array Dir
  name : String
deriving Repr

structure Pkg where
  α : Type
  xs : Array α
  f : α → Nat

@[noinline] def total (p : Pkg) : Nat := p.xs.foldl (fun acc x => acc + p.f x) 0

@[noinline] def generic {α : Type} [BEq α] (xs : Array α) (x : α) : Nat × Bool :=
  (xs.size, xs.contains x)

def main (args : List String) : IO Unit := do
  let n := args.length + 10
  let lit : Array Dir := #[.n, .e, .s, .w, .w]
  IO.println s!"lit {repr lit} {lit.size} {lit == #[.n, .e, .s, .w, .w]} {lit.toList.length}"
  -- push, set!, modify, map (in place), reverse, folds
  let mut a : Array Dir := #[]
  for i in [0:n] do a := a.push (Dir.ofNat i)
  a := a.set! 3 .w
  a := a.modify 0 Dir.turn
  let b := a.map Dir.turn
  IO.println s!"a {repr a} b {repr b} rev {repr a.reverse}"
  IO.println s!"count {a.foldl (fun c d => if d == .w then c + 1 else c) 0} any {a.any (· == .s)} all {a.all (· != .s)} idx {a.findIdx? (· == .w)}"
  -- maps between representations
  let idx := a.map fun | .n => 0 | .e => 1 | .s => 2 | .w => 3
  let back := (Array.range n).map Dir.ofNat
  let flags := a.map (· == .e)
  IO.println s!"idx {idx} back {repr back} flags {flags}"
  -- sorting with a derived Ord
  let srt := (back.push .n).qsort (fun x y => compare x y == .lt)
  IO.println s!"sorted {repr srt}"
  -- nested arrays and arrays in structures
  let grid : Array (Array Dir) := (Array.range 3).map fun i => Array.replicate (i + 1) (Dir.ofNat i)
  let g : Grid := { cells := a.extract 0 4, name := "g" }
  IO.println s!"grid {repr grid} {repr g}"
  -- more than 256 constructors (a two-byte index)
  let mut bigs : Array Big := #[]
  for i in [0:n] do bigs := bigs.push (Big.ofIdx i)
  IO.println s!"bigs {repr (bigs.extract 0 5)} {bigs.size} {bigs.contains .c256} {bigs.contains .c4}"
  -- Unit and Bool arrays
  let units := Array.replicate n ()
  let bools := (Array.range n).map (· % 3 == 0)
  IO.println s!"units {units.size} {units.push () |>.size} {units == Array.replicate n ()} bools {bools}"
  -- existential packages and generic code
  IO.println s!"pkg {total ⟨Dir, a, fun d => if d == .w then 10 else 1⟩} {total ⟨Unit, units, fun _ => 2⟩} generic {generic a .s} {generic bigs .c255}"
  -- casts between arrays of enumerations, UInt8 and Nat (same representation natively)
  let asU8 : Array UInt8 := unsafe unsafeCast a
  let asNat : Array Nat := unsafe unsafeCast a
  let fromU8 : Array Dir := unsafe unsafeCast (#[3, 2, 1, 0] : Array UInt8)
  IO.println s!"casts {asU8} {asNat} {repr fromU8}"
