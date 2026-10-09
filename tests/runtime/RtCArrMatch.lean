/-! Runtime test (compact scalar arrays, hunt HARR2-01): a `match` that takes
an `Array` apart into its list (`match a with | ⟨l⟩ => …`, also
`let ⟨xs⟩ := a`). Lean's `toMono` makes it `let l := Array.toList ◾ a`,
a call by the extern's own name, after lean2rr made the extern instances:
taken at its declared types, the call took `Array lcAny`, so the compact
array was a crossing and its kind went off for the whole program: on dev
0b6ef980 every kind was off here (u8 by `Array Bool` and by an
enumeration, u16, u32 by `Array Char`, u64, f32, f64 by a generic function
at `Float`). Now `l` has the field's type `List α` and
Stage 3 calls the instance of `Array.toList` at `α`
(docs/implementation/representations/compact-arrays.md, "A `match` on an
array takes the array at its own type"): every kind stays on
(RtCArrMatch.l2r-debug). A `match` on a `Thunk` and on a `Task`, which
`toMono` turns into calls by the extern's own name too, stays as Lean made
it. Also element types that are no scalar or that mono changes:
functions, `Unit`, `Fin`, `Option`, `String`, `Int8`, `Float32`, a subtype,
`Vector`, an array of arrays, and a `match` on the result of `extract`. -/
inductive Color where | red | green | blue deriving Repr, BEq, Inhabited

@[noinline] def viaMatchA (a : Array Bool) : Nat := match a with | ⟨l⟩ => l.length + (l.filter id).length
@[noinline] def rebuildA (a : Array UInt16) : Array UInt16 := match a with | ⟨l⟩ => ⟨l.reverse ++ [9]⟩
@[noinline] def colors (a : Array Color) : List Color := match a with | ⟨l⟩ => l.reverse
@[noinline] def chars (a : Array Char) : String := match a with | ⟨l⟩ => String.ofList (l ++ ['!'])
@[noinline] def nested (a : Array (Array UInt8)) : Nat := match a with | ⟨l⟩ => l.foldl (fun s x => s + x.size) 0
@[noinline] def generic {α} (a : Array α) : Nat := match a with | ⟨l⟩ => l.length
@[noinline] def letForm (a : Array UInt64) : UInt64 := let ⟨xs⟩ := a; xs.foldl (· + ·) 0
@[noinline] def thunkGet (t : Thunk Nat) : Nat := match t with | ⟨f⟩ => f () + 1
@[noinline] def taskGet (t : Task Float) : Float := match t with | ⟨v⟩ => v * 2

@[noinline] def fns (a : Array (Nat → Nat)) : Nat := match a with | ⟨l⟩ => l.foldl (fun s f => s + f s) 1
@[noinline] def units (a : Array Unit) : Nat := match a with | ⟨l⟩ => l.length
@[noinline] def fins (a : Array (Fin 5)) : Nat := match a with | ⟨l⟩ => l.foldl (fun s x => s * 5 + x.val) 0
@[noinline] def opts (a : Array (Option UInt8)) : Nat := match a with | ⟨l⟩ => l.foldl (fun s x => s + (x.getD 7).toNat) 0
@[noinline] def strs (a : Array String) : String := match a with | ⟨l⟩ => String.intercalate "," l
@[noinline] def i8s (a : Array Int8) : Int := match a with | ⟨l⟩ => l.foldl (fun s x => s + x.toInt) 0
@[noinline] def f32s (a : Array Float32) : Float32 := match a with | ⟨l⟩ => l.foldl (· + ·) 0
@[noinline] def big (a : Array UInt64) : List UInt64 := match a with | ⟨l⟩ => l
@[noinline] def props (a : Array (Subtype fun (n : Nat) => n < 100)) : Nat := match a with | ⟨l⟩ => l.foldl (fun s x => s + x.val) 0
@[noinline] def vecs (a : Array (Vector UInt8 2)) : Nat := match a with | ⟨l⟩ => l.foldl (fun s v => s + v[0].toNat + v[1].toNat) 0
@[noinline] def sub (a : Array UInt16) : Nat := match a.extract 1 3 with | ⟨l⟩ => l.length

def main (args : List String) : IO Unit := do
  let n := args.length + 6
  let a : Array Bool := (Array.range n).map (· % 3 == 0)
  let u : Array UInt16 := (Array.range n).map (·.toUInt16 * 1000)
  IO.println s!"{viaMatchA a} {(rebuildA u).toList} {u.size}"
  let cs : Array Color := (Array.range n).map fun i => if i % 3 == 0 then .red else if i % 3 == 1 then .green else .blue
  IO.println s!"{repr (colors cs)}"
  IO.println (chars ((Array.range n).map fun i => Char.ofNat (97 + i)))
  let nest : Array (Array UInt8) := (Array.range n).map fun i => (Array.range i).map (·.toUInt8)
  IO.println s!"{nested nest} {generic cs} {generic nest} {generic #[1.5, 2.5]}"
  IO.println s!"{letForm ((Array.range n).map (·.toUInt64 * 0xFFFFFFFFFF))}"
  IO.println s!"{thunkGet (Thunk.mk fun _ => n * 3)} {taskGet (Task.spawn fun _ => n.toFloat)}"
  IO.println s!"{fns #[(· + 1), (· * 2), fun x => x + n]} {units (Array.replicate n ())}"
  IO.println s!"{fins #[1, 2, 3, 4]} {opts #[some 3, none, some 250]} {strs #["a", "bc", toString n]}"
  IO.println s!"{i8s #[-5, 100, -128]} {f32s #[1.5, 2.25]} {big #[0xFFFFFFFFFFFFFFFF, (1 : UInt64) <<< 63, n.toUInt64]}"
  IO.println s!"{props #[⟨3, by decide⟩, ⟨99, by decide⟩]} {vecs #[#v[1, 2], #v[200, 100]]} {sub #[1, 2, 3, 4]}"
