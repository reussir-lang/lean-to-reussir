/-!
Runtime test of the optimization `unread-fields` (off by default; this
test turns it on, `RtUnreadFieldsDataRead.enable-opts`): data fields that
kept code reads stay. Entries registered by `initialize` blocks are read
by projection, by a match, through a nested structure, and by the derived
`BEq`, `Hashable`, `Ord` and `Repr` instances (Lean code that matches
every field); a field read only by a hash or only by an equality test
still counts as read.
-/

structure Pos where
  line : Nat
  col : Nat
deriving BEq, Hashable, Repr, Ord, Inhabited

structure Entry where
  name : String
  pos : Pos
  tags : List String
  weight : UInt32
deriving BEq, Hashable, Repr, Inhabited

structure Tagged where
  label : String
  hidden : Nat
deriving Hashable

structure Keyed where
  key : String
  secret : Nat
deriving BEq

initialize entriesRef : IO.Ref (Array Entry) ← IO.mkRef #[]

def register (e : Entry) : IO Unit := entriesRef.modify (·.push e)

initialize register { name := "a", pos := { line := 3, col := 7 }, tags := ["x", "y"], weight := 15 }
initialize register { name := "b", pos := { line := 3, col := 9 }, tags := [], weight := 25 }

@[noinline] def mkTagged (n : Nat) : Tagged := { label := s!"t{n}", hidden := n * 7 }
@[noinline] def mkKeyed (n : Nat) : Keyed := { key := "k", secret := n + 1 }

def main (args : List String) : IO Unit := do
  let es ← entriesRef.get
  for e in es do
    IO.println s!"{e.name} at {e.pos.line}:{e.pos.col}"
    match e with
    | ⟨n, ⟨l, _⟩, ts, w⟩ => IO.println s!"{n}: line {l}, {ts.length} tags, weight {w}"
  IO.println (repr es[0]!)
  IO.println s!"equal {es[0]! == es[1]!}, hash differs {hash es[0]! != hash es[1]!}"
  IO.println s!"compare {repr (compare es[0]!.pos es[1]!.pos)}"
  -- `hidden` is read only by the derived hash, `secret` only by `==`.
  let n := args.length
  IO.println s!"tagged hashes differ: {hash (mkTagged n) != hash (mkTagged (n + 1))}"
  IO.println s!"keyed equal: {mkKeyed n == mkKeyed (n + 1)}"
