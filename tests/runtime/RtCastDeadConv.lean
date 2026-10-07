/-! Runtime test: casts (`unsafeCast`) between inductives whose conversion
can never return a value (a function field read as a `String`): lean2rr
generates no function for such a conversion (`deadConvs`); a use is
`l2r_unreachable` in line, also inside another conversion that does
return values (`C' → D`'s `wrap` arm, whose field is an `A'`), and a
conversion that one being generated already called is generated with the
panic as its body (`A' → B`, reached again through `C' → D`'s `wrap` arm
while `A' → B` is being generated; `A2 → B2` below). The casts that run
convert constructors without fields; the others are behind a condition
that is false. -/

mutual
inductive C' where
  | leaf
  | wrap (a : A')
inductive A' where
  | mk (c : C') (f : Nat → Nat)
end

mutual
inductive D where
  | leaf
  | wrap (b : B)
inductive B where
  | mk (d : D) (s : String)
end

-- The same shapes, cast only as `A2 → B2`: that conversion is generated
-- first, so `C2 → D2`'s `wrap` arm calls it while it is being generated,
-- and it is generated with the panic as its body.
mutual
inductive C2 where
  | leaf
  | wrap (a : A2)
inductive A2 where
  | mk (c : C2) (f : Nat → Nat)
end

mutual
inductive D2 where
  | leaf
  | wrap (b : B2)
inductive B2 where
  | mk (d : D2) (s : String)
end

@[noinline] unsafe def toB2 (a : A2) : B2 := unsafeCast a

@[noinline] def name2 : B2 → String
  | .mk _ s => s

@[noinline] unsafe def toB (a : A') : B := unsafeCast a
@[noinline] unsafe def toD (c : C') : D := unsafeCast c

@[noinline] def isLeaf : D → Bool
  | .leaf => true
  | .wrap _ => false

@[noinline] def name : B → String
  | .mk _ s => s

unsafe def main (args : List String) : IO Unit := do
  IO.println (isLeaf (toD .leaf))
  if args.length > 5 then
    IO.println (name (toB (.mk .leaf (· + 1))))
    IO.println (isLeaf (toD (.wrap (.mk .leaf id))))
    IO.println (name2 (toB2 (.mk .leaf id)))
  IO.println "done"
