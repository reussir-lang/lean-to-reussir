/-! Runtime test: a random-type fuzzer output (fz/gen2.py, fixed seed): 14
container contexts C[α] whose hole goes uniform (List/Array/Option/Prod/Sum/
Except/Thunk/Task/function types, a generic value structure `W1`, a
field-reordered record `P3`, a binary tree `Tr`, a rose tree with Array
children, mutual inductives, nested 1-3 deep): each value is converted
C[T] → C[Box] structurally, mapped in uniform code (polymorphic recursion),
and converted back; shown directly and after the round trip.
From the round-7 review, area R (rv7/repr), check fz/Gz5. -/

-- Gz5
structure WN where
  n : Nat
structure W1 (α : Type) where
  v : α
structure P3 (α β : Type) where
  x : β
  y : α
  w : β
inductive Tr (α : Type) where
  | leaf
  | node (l : Tr α) (k : α) (r : Tr α)
def Tr.map {α β : Type} (f : α → β) : Tr α → Tr β
  | .leaf => .leaf
  | .node l k r => .node (l.map f) (f k) (r.map f)
def Tr.mirror {α : Type} : Tr α → Tr α
  | .leaf => .leaf
  | .node l k r => .node r.mirror k l.mirror
def Tr.toList {α : Type} : Tr α → List α
  | .leaf => []
  | .node l k r => l.toList ++ [k] ++ r.toList
inductive Ro (α : Type) where
  | node (tag : UInt8) (v : α) (kids : Array (Ro α)) (w : UInt32) (name : String)
def Ro.map {α β : Type} (f : α → β) : Ro α → Ro β
  | .node t v ks w nm => .node t (f v) (ks.map (fun k => Ro.map f k)) w nm
def Ro.flip {α : Type} : Ro α → Ro α
  | .node t v ks w nm => .node (t + 1) v (ks.map (fun k => Ro.flip k)).reverse (w + 1) (nm ++ "'")
def Ro.show {α : Type} (s : α → String) : Ro α → String
  | .node t v ks w nm => s!"({t} {s v} {w} {nm} {ks.map (fun k => Ro.show s k)})"
mutual
  inductive MA (α : Type) where
    | a (x : α) (bs : List (MB α)) (tag : UInt16)
    | stop
  inductive MB (α : Type) where
    | b (y : α) (a1 : MA α) (a2 : MA α)
end
mutual
  def MA.map {α : Type} (f : α → α) : MA α → MA α
    | .a x bs t => .a (f x) (MB.mapL f bs).reverse (t + 1)
    | .stop => .stop
  def MB.mapL {α : Type} (f : α → α) : List (MB α) → List (MB α)
    | [] => []
    | .b y a1 a2 :: rest => .b (f y) (a2.map f) (a1.map f) :: MB.mapL f rest
end
mutual
  def MA.show {α : Type} (s : α → String) : MA α → String
    | .a x bs t => s!"a({s x} {t} {MB.showL s bs})"
    | .stop => "stop"
  def MB.showL {α : Type} (s : α → String) : List (MB α) → String
    | [] => "."
    | .b y a1 a2 :: rest => s!"b({s y} {MA.show s a1} {MA.show s a2}) " ++ MB.showL s rest
end
instance : Inhabited WN := ⟨⟨0⟩⟩
instance {α : Type} [Inhabited α] : Inhabited (W1 α) := ⟨⟨default⟩⟩

def mp1 {α : Type} (f : α → α) : (Thunk α) → (Thunk α) := fun t => Thunk.mk fun _ => (f) t.get
def sh2 {α : Type} (s : α → String) : (Thunk α) → String := fun t => "thunk " ++ (s) t.get
def mp3 {α : Type} (f : α → α) : (List (Thunk α)) → (List (Thunk α)) := fun l => (l.map (mp1 f)).reverse
def sh4 {α : Type} (s : α → String) : (List (Thunk α)) → String := fun l => "[" ++ ", ".intercalate (l.map (sh2 s)) ++ "]"
def mp5 {α : Type} (f : α → α) : (α × α) → (α × α) := fun p => ((f) p.2, p.1)
def sh6 {α : Type} (s : α → String) : (α × α) → String := fun p => "(" ++ (s) p.1 ++ ", " ++ (s) p.2 ++ ")"
def mp7 {α : Type} (f : α → α) : (Sum α UInt64) → (Sum α UInt64) := fun x => match x with | .inl a => .inl ((f) a) | .inr b => .inr ((· + 1) b)
def sh8 {α : Type} (s : α → String) : (Sum α UInt64) → String := fun x => match x with | .inl a => "inl " ++ (s) a | .inr b => "inr " ++ toString b
def mp9 {α : Type} (f : α → α) : (Except String (Sum α UInt64)) → (Except String (Sum α UInt64)) := fun x => x.map (mp7 f)
def sh10 {α : Type} (s : α → String) : (Except String (Sum α UInt64)) → String := fun x => match x with | .ok a => "ok " ++ (sh8 s) a | .error e => "error " ++ e
def mp11 {α : Type} (f : α → α) : (Sum α UInt32) → (Sum α UInt32) := fun x => match x with | .inl a => .inl ((f) a) | .inr b => .inr ((· + 7) b)
def sh12 {α : Type} (s : α → String) : (Sum α UInt32) → String := fun x => match x with | .inl a => "inl " ++ (s) a | .inr b => "inr " ++ toString b
def mp13 {α : Type} (f : α → α) : (Tr α) → (Tr α) := fun t => (t.map (f)).mirror
def sh14 {α : Type} (s : α → String) : (Tr α) → String := fun t => "tr[" ++ ", ".intercalate (t.toList.map (s)) ++ "]"
def mp15 {α : Type} (f : α → α) : (Nat → (Tr α)) → (Nat → (Tr α)) := fun g n => (mp13 f) (g (n + 1))
def sh16 {α : Type} (s : α → String) : (Nat → (Tr α)) → String := fun g => "fn " ++ (sh14 s) (g 0) ++ " " ++ (sh14 s) (g 1)
def mp17 {α : Type} (f : α → α) : (List α) → (List α) := fun l => (l.map (f)).reverse
def sh18 {α : Type} (s : α → String) : (List α) → String := fun l => "[" ++ ", ".intercalate (l.map (s)) ++ "]"
def mp19 {α : Type} (f : α → α) : (P3 (List α) Int8) → (P3 (List α) Int8) := fun p => ⟨p.w, (mp17 f) p.y, (· - 1) p.x⟩
def sh20 {α : Type} (s : α → String) : (P3 (List α) Int8) → String := fun p => "P3(" ++ toString p.x ++ ", " ++ (sh18 s) p.y ++ ", " ++ toString p.w ++ ")"
def mp21 {α : Type} (f : α → α) : (P3 α Char) → (P3 α Char) := fun p => ⟨p.w, (f) p.y, (fun c => Char.ofNat (c.toNat + 1)) p.x⟩
def sh22 {α : Type} (s : α → String) : (P3 α Char) → String := fun p => "P3(" ++ (fun c => toString c.toNat) p.x ++ ", " ++ (s) p.y ++ ", " ++ (fun c => toString c.toNat) p.w ++ ")"
def mp23 {α : Type} (f : α → α) : ((P3 α Char) × UInt8) → ((P3 α Char) × UInt8) := fun p => ((mp21 f) p.1, (· + 1) p.2)
def sh24 {α : Type} (s : α → String) : ((P3 α Char) × UInt8) → String := fun p => "(" ++ (sh22 s) p.1 ++ ", " ++ toString p.2 ++ ")"
def mp25 {α : Type} (f : α → α) : (Tr α) → (Tr α) := fun t => (t.map (f)).mirror
def sh26 {α : Type} (s : α → String) : (Tr α) → String := fun t => "tr[" ++ ", ".intercalate (t.toList.map (s)) ++ "]"
def mp27 {α : Type} (f : α → α) : (Option (Tr α)) → (Option (Tr α)) := fun o => o.map (mp25 f)
def sh28 {α : Type} (s : α → String) : (Option (Tr α)) → String := fun o => match o with | some x => "some " ++ (sh26 s) x | none => "none"
def mp29 {α : Type} (f : α → α) : (Ro α) → (Ro α) := fun t => (t.map (f)).flip
def sh30 {α : Type} (s : α → String) : (Ro α) → String := fun t => Ro.show (s) t
def mp31 {α : Type} (f : α → α) : (P3 (Ro α) Int) → (P3 (Ro α) Int) := fun p => ⟨p.w, (mp29 f) p.y, (· * -2) p.x⟩
def sh32 {α : Type} (s : α → String) : (P3 (Ro α) Int) → String := fun p => "P3(" ++ toString p.x ++ ", " ++ (sh30 s) p.y ++ ", " ++ toString p.w ++ ")"
def mp33 {α : Type} (f : α → α) : (Ordering × α) → (Ordering × α) := fun p => (Ordering.swap p.1, (f) p.2)
def sh34 {α : Type} (s : α → String) : (Ordering × α) → String := fun p => "(" ++ (fun o => toString (repr o)) p.1 ++ ", " ++ (s) p.2 ++ ")"
def mp35 {α : Type} (f : α → α) : (UInt16 × α) → (UInt16 × α) := fun p => ((· * 3) p.1, (f) p.2)
def sh36 {α : Type} (s : α → String) : (UInt16 × α) → String := fun p => "(" ++ toString p.1 ++ ", " ++ (s) p.2 ++ ")"
def mp37 {α : Type} (f : α → α) : (Nat → (UInt16 × α)) → (Nat → (UInt16 × α)) := fun g n => (mp35 f) (g (n + 1))
def sh38 {α : Type} (s : α → String) : (Nat → (UInt16 × α)) → String := fun g => "fn " ++ (sh36 s) (g 0) ++ " " ++ (sh36 s) (g 1)
def mp39 {α : Type} (f : α → α) : (Tr (Nat → (UInt16 × α))) → (Tr (Nat → (UInt16 × α))) := fun t => (t.map (mp37 f)).mirror
def sh40 {α : Type} (s : α → String) : (Tr (Nat → (UInt16 × α))) → String := fun t => "tr[" ++ ", ".intercalate (t.toList.map (sh38 s)) ++ "]"
def mp41 {α : Type} (f : α → α) : (P3 α (Array String)) → (P3 α (Array String)) := fun p => ⟨p.w, (f) p.y, (·.push "x") p.x⟩
def sh42 {α : Type} (s : α → String) : (P3 α (Array String)) → String := fun p => "P3(" ++ toString p.x ++ ", " ++ (s) p.y ++ ", " ++ toString p.w ++ ")"
def mp43 {α : Type} (f : α → α) : (Array (P3 α (Array String))) → (Array (P3 α (Array String))) := fun l => (match l[0]? with | some x => ((l.map (mp41 f)).pop.push x) | none => l.map (mp41 f)).swapIfInBounds 0 2
def sh44 {α : Type} (s : α → String) : (Array (P3 α (Array String))) → String := fun l => "#[" ++ ", ".intercalate (l.toList.map (sh42 s)) ++ "]"
def mp45 {α : Type} (f : α → α) : (P3 α Unit) → (P3 α Unit) := fun p => ⟨p.w, (f) p.y, id p.x⟩
def sh46 {α : Type} (s : α → String) : (P3 α Unit) → String := fun p => "P3(" ++ (fun _ => "()") p.x ++ ", " ++ (s) p.y ++ ", " ++ (fun _ => "()") p.w ++ ")"
def mp47 {α : Type} (f : α → α) : (W1 (P3 α Unit)) → (W1 (P3 α Unit)) := fun w => ⟨(mp45 f) w.v⟩
def sh48 {α : Type} (s : α → String) : (W1 (P3 α Unit)) → String := fun w => "W1 " ++ (sh46 s) w.v
def mp49 {α : Type} (f : α → α) : (Sum α Unit) → (Sum α Unit) := fun x => match x with | .inl a => .inl ((f) a) | .inr b => .inr (id b)
def sh50 {α : Type} (s : α → String) : (Sum α Unit) → String := fun x => match x with | .inl a => "inl " ++ (s) a | .inr b => "inr " ++ (fun _ => "()") b
def go0 {α β : Type} (n : Nat) (x : (List (Thunk α))) (b : β) (f : α → α) (k : (List (Thunk α)) → String) : String :=
  match n with
  | 0 => k (mp3 f x) ++ " / " ++ k x ++ " / " ++ k (mp3 f (mp3 f x))
  | n+1 => go0 n x (b, b) f k
def go1 {α β : Type} (n : Nat) (x : (α × α)) (b : β) (f : α → α) (k : (α × α) → String) : String :=
  match n with
  | 0 => k (mp5 f x) ++ " / " ++ k x ++ " / " ++ k (mp5 f (mp5 f x))
  | n+1 => go1 n x (b, b) f k
def go2 {α β : Type} (n : Nat) (x : (Except String (Sum α UInt64))) (b : β) (f : α → α) (k : (Except String (Sum α UInt64)) → String) : String :=
  match n with
  | 0 => k (mp9 f x) ++ " / " ++ k x ++ " / " ++ k (mp9 f (mp9 f x))
  | n+1 => go2 n x (b, b) f k
def go3 {α β : Type} (n : Nat) (x : (Sum α UInt32)) (b : β) (f : α → α) (k : (Sum α UInt32) → String) : String :=
  match n with
  | 0 => k (mp11 f x) ++ " / " ++ k x ++ " / " ++ k (mp11 f (mp11 f x))
  | n+1 => go3 n x (b, b) f k
def go4 {α β : Type} (n : Nat) (x : (Nat → (Tr α))) (b : β) (f : α → α) (k : (Nat → (Tr α)) → String) : String :=
  match n with
  | 0 => k (mp15 f x) ++ " / " ++ k x ++ " / " ++ k (mp15 f (mp15 f x))
  | n+1 => go4 n x (b, b) f k
def go5 {α β : Type} (n : Nat) (x : (P3 (List α) Int8)) (b : β) (f : α → α) (k : (P3 (List α) Int8) → String) : String :=
  match n with
  | 0 => k (mp19 f x) ++ " / " ++ k x ++ " / " ++ k (mp19 f (mp19 f x))
  | n+1 => go5 n x (b, b) f k
def go6 {α β : Type} (n : Nat) (x : ((P3 α Char) × UInt8)) (b : β) (f : α → α) (k : ((P3 α Char) × UInt8) → String) : String :=
  match n with
  | 0 => k (mp23 f x) ++ " / " ++ k x ++ " / " ++ k (mp23 f (mp23 f x))
  | n+1 => go6 n x (b, b) f k
def go7 {α β : Type} (n : Nat) (x : (Option (Tr α))) (b : β) (f : α → α) (k : (Option (Tr α)) → String) : String :=
  match n with
  | 0 => k (mp27 f x) ++ " / " ++ k x ++ " / " ++ k (mp27 f (mp27 f x))
  | n+1 => go7 n x (b, b) f k
def go8 {α β : Type} (n : Nat) (x : (P3 (Ro α) Int)) (b : β) (f : α → α) (k : (P3 (Ro α) Int) → String) : String :=
  match n with
  | 0 => k (mp31 f x) ++ " / " ++ k x ++ " / " ++ k (mp31 f (mp31 f x))
  | n+1 => go8 n x (b, b) f k
def go9 {α β : Type} (n : Nat) (x : (Ordering × α)) (b : β) (f : α → α) (k : (Ordering × α) → String) : String :=
  match n with
  | 0 => k (mp33 f x) ++ " / " ++ k x ++ " / " ++ k (mp33 f (mp33 f x))
  | n+1 => go9 n x (b, b) f k
def go10 {α β : Type} (n : Nat) (x : (Tr (Nat → (UInt16 × α)))) (b : β) (f : α → α) (k : (Tr (Nat → (UInt16 × α))) → String) : String :=
  match n with
  | 0 => k (mp39 f x) ++ " / " ++ k x ++ " / " ++ k (mp39 f (mp39 f x))
  | n+1 => go10 n x (b, b) f k
def go11 {α β : Type} (n : Nat) (x : (Array (P3 α (Array String)))) (b : β) (f : α → α) (k : (Array (P3 α (Array String))) → String) : String :=
  match n with
  | 0 => k (mp43 f x) ++ " / " ++ k x ++ " / " ++ k (mp43 f (mp43 f x))
  | n+1 => go11 n x (b, b) f k
def go12 {α β : Type} (n : Nat) (x : (W1 (P3 α Unit))) (b : β) (f : α → α) (k : (W1 (P3 α Unit)) → String) : String :=
  match n with
  | 0 => k (mp47 f x) ++ " / " ++ k x ++ " / " ++ k (mp47 f (mp47 f x))
  | n+1 => go12 n x (b, b) f k
def go13 {α β : Type} (n : Nat) (x : (Sum α Unit)) (b : β) (f : α → α) (k : (Sum α Unit) → String) : String :=
  match n with
  | 0 => k (mp49 f x) ++ " / " ++ k x ++ " / " ++ k (mp49 f (mp49 f x))
  | n+1 => go13 n x (b, b) f k
def main (args : List String) : IO Unit := do
  let z := args.length
  -- (List (Thunk String))
  let v0 : (List (Thunk String)) := [(Thunk.mk fun _ => (s!"s{z}" : String)), (Thunk.mk fun _ => (s!"s{z}" : String))]
  IO.println ("0 " ++ go0 2 v0 () ((· ++ "!") : String → String) (sh4 (String.quote : String → String)))
  IO.println ("0d " ++ sh4 (String.quote : String → String) (mp3 ((· ++ "!") : String → String) v0))
  -- (UInt64 × UInt64)
  let v1 : (UInt64 × UInt64) := (((18446744073709551615 : UInt64) - z.toUInt64 : UInt64), ((18446744073709551615 : UInt64) - z.toUInt64 : UInt64))
  IO.println ("1 " ++ go1 2 v1 () ((· + 1) : UInt64 → UInt64) (sh6 (toString : UInt64 → String)))
  IO.println ("1d " ++ sh6 (toString : UInt64 → String) (mp5 ((· + 1) : UInt64 → UInt64) v1))
  -- (Except String (Sum Int8 UInt64))
  let v2 : (Except String (Sum Int8 UInt64)) := (if z == 0 then Except.ok ((Sum.inl (((-128 : Int8) + z.toInt8 : Int8)))) else Except.error "e")
  IO.println ("2 " ++ go2 2 v2 () ((· - 1) : Int8 → Int8) (sh10 (toString : Int8 → String)))
  IO.println ("2d " ++ sh10 (toString : Int8 → String) (mp9 ((· - 1) : Int8 → Int8) v2))
  -- (Sum Bool UInt32)
  let v3 : (Sum Bool UInt32) := (Sum.inl (((z == 0) : Bool)))
  IO.println ("3 " ++ go3 2 v3 () (not : Bool → Bool) (sh12 (toString : Bool → String)))
  IO.println ("3d " ++ sh12 (toString : Bool → String) (mp11 (not : Bool → Bool) v3))
  -- (Nat → (Tr Nat))
  let v4 : (Nat → (Tr Nat)) := (fun (n : Nat) => if n % 2 == 0 then (Tr.node (Tr.node .leaf ((2^63 + z : Nat)) .leaf) ((2^63 + z : Nat)) (Tr.node .leaf ((2^63 + z : Nat)) .leaf)) else (Tr.node (Tr.node .leaf ((2^63 + z : Nat)) .leaf) ((2^63 + z : Nat)) (Tr.node .leaf ((2^63 + z : Nat)) .leaf)))
  IO.println ("4 " ++ go4 2 v4 () ((· + 2^64) : Nat → Nat) (sh16 (toString : Nat → String)))
  IO.println ("4d " ++ sh16 (toString : Nat → String) (mp15 ((· + 2^64) : Nat → Nat) v4))
  -- (P3 (List WN) Int8)
  let v5 : (P3 (List WN) Int8) := (⟨(-128 : Int8) + z.toInt8, [(⟨z⟩ : WN), (⟨z⟩ : WN)], (-128 : Int8) + z.toInt8⟩ : P3 _ _)
  IO.println ("5 " ++ go5 2 v5 () ((fun w => ⟨w.n + 1⟩) : WN → WN) (sh20 ((fun w => s!"WN {w.n}") : WN → String)))
  IO.println ("5d " ++ sh20 ((fun w => s!"WN {w.n}") : WN → String) (mp19 ((fun w => ⟨w.n + 1⟩) : WN → WN) v5))
  -- ((P3 (List Nat) Char) × UInt8)
  let v6 : ((P3 (List Nat) Char) × UInt8) := ((⟨'λ', ([z, 2^64] : (List Nat)), 'λ'⟩ : P3 _ _), (255 : UInt8) + z.toUInt8)
  IO.println ("6 " ++ go6 2 v6 () ((·.map (· + 1)) : (List Nat) → (List Nat)) (sh24 (toString : (List Nat) → String)))
  IO.println ("6d " ++ sh24 (toString : (List Nat) → String) (mp23 ((·.map (· + 1)) : (List Nat) → (List Nat)) v6))
  -- (Option (Tr UInt64))
  let v7 : (Option (Tr UInt64)) := (if z == 0 then some ((Tr.node (Tr.node .leaf (((18446744073709551615 : UInt64) - z.toUInt64 : UInt64)) .leaf) (((18446744073709551615 : UInt64) - z.toUInt64 : UInt64)) (Tr.node .leaf (((18446744073709551615 : UInt64) - z.toUInt64 : UInt64)) .leaf))) else none)
  IO.println ("7 " ++ go7 2 v7 () ((· + 1) : UInt64 → UInt64) (sh28 (toString : UInt64 → String)))
  IO.println ("7d " ++ sh28 (toString : UInt64 → String) (mp27 ((· + 1) : UInt64 → UInt64) v7))
  -- (P3 (Ro Int8) Int)
  let v8 : (P3 (Ro Int8) Int) := (⟨(z : Int) - 5, (Ro.node 3 (((-128 : Int8) + z.toInt8 : Int8)) #[Ro.node 1 (((-128 : Int8) + z.toInt8 : Int8)) #[] 9 "a", Ro.node 2 (((-128 : Int8) + z.toInt8 : Int8)) #[Ro.node 0 (((-128 : Int8) + z.toInt8 : Int8)) #[] 8 ""] 7 "b"] 70000 "r"), (z : Int) - 5⟩ : P3 _ _)
  IO.println ("8 " ++ go8 2 v8 () ((· - 1) : Int8 → Int8) (sh32 (toString : Int8 → String)))
  IO.println ("8d " ++ sh32 (toString : Int8 → String) (mp31 ((· - 1) : Int8 → Int8) v8))
  -- (Ordering × WN)
  let v9 : (Ordering × WN) := (.gt, (⟨2^64 + z⟩ : WN))
  IO.println ("9 " ++ go9 2 v9 () ((fun w => ⟨w.n + 1⟩) : WN → WN) (sh34 ((fun w => s!"WN {w.n}") : WN → String)))
  IO.println ("9d " ++ sh34 ((fun w => s!"WN {w.n}") : WN → String) (mp33 ((fun w => ⟨w.n + 1⟩) : WN → WN) v9))
  -- (Tr (Nat → (UInt16 × (List Nat))))
  let v10 : (Tr (Nat → (UInt16 × (List Nat)))) := (Tr.node (Tr.node .leaf ((fun (n : Nat) => if n % 2 == 0 then ((65535 : UInt16) + z.toUInt16, ([z, 2^64] : (List Nat))) else ((65535 : UInt16) + z.toUInt16, ([z, 2^64] : (List Nat))))) .leaf) ((fun (n : Nat) => if n % 2 == 0 then ((65535 : UInt16) + z.toUInt16, ([z, 2^64] : (List Nat))) else ((65535 : UInt16) + z.toUInt16, ([z, 2^64] : (List Nat))))) (Tr.node .leaf ((fun (n : Nat) => if n % 2 == 0 then ((65535 : UInt16) + z.toUInt16, ([z, 2^64] : (List Nat))) else ((65535 : UInt16) + z.toUInt16, ([z, 2^64] : (List Nat))))) .leaf))
  IO.println ("10 " ++ go10 2 v10 () ((·.map (· + 1)) : (List Nat) → (List Nat)) (sh40 (toString : (List Nat) → String)))
  IO.println ("10d " ++ sh40 (toString : (List Nat) → String) (mp39 ((·.map (· + 1)) : (List Nat) → (List Nat)) v10))
  -- (Array (P3 UInt64 (Array String)))
  let v11 : (Array (P3 UInt64 (Array String))) := #[(⟨#["a", toString z], ((18446744073709551615 : UInt64) - z.toUInt64 : UInt64), #["a", toString z]⟩ : P3 _ _), (⟨#["a", toString z], ((18446744073709551615 : UInt64) - z.toUInt64 : UInt64), #["a", toString z]⟩ : P3 _ _), (⟨#["a", toString z], ((18446744073709551615 : UInt64) - z.toUInt64 : UInt64), #["a", toString z]⟩ : P3 _ _)]
  IO.println ("11 " ++ go11 2 v11 () ((· + 1) : UInt64 → UInt64) (sh44 (toString : UInt64 → String)))
  IO.println ("11d " ++ sh44 (toString : UInt64 → String) (mp43 ((· + 1) : UInt64 → UInt64) v11))
  -- (W1 (P3 WN Unit))
  let v12 : (W1 (P3 WN Unit)) := (⟨(⟨(), (⟨z⟩ : WN), ()⟩ : P3 _ _)⟩ : W1 _)
  IO.println ("12 " ++ go12 2 v12 () ((fun w => ⟨w.n + 1⟩) : WN → WN) (sh48 ((fun w => s!"WN {w.n}") : WN → String)))
  IO.println ("12d " ++ sh48 ((fun w => s!"WN {w.n}") : WN → String) (mp47 ((fun w => ⟨w.n + 1⟩) : WN → WN) v12))
  -- (Sum UInt8 Unit)
  let v13 : (Sum UInt8 Unit) := (Sum.inl (((255 : UInt8) + z.toUInt8 : UInt8)))
  IO.println ("13 " ++ go13 2 v13 () ((· + 1) : UInt8 → UInt8) (sh50 (toString : UInt8 → String)))
  IO.println ("13d " ++ sh50 (toString : UInt8 → String) (mp49 ((· + 1) : UInt8 → UInt8) v13))

