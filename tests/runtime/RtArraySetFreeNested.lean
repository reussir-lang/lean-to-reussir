/-! Runtime test (switch step 11): the order of the observable releases when
an array set, an array pop or a reference set frees the last reference to a
structure whose fields hold other structures that are freed with it (each
handle's text reaches the shared temporary file when it is closed).
Natively the release is `lean_dec`, which frees through the stack of
objects: a freed object's fields are pushed in order and popped last first,
so its last field is freed first, and a freed field's own fields before the
fields that precede it. lean2rr frees the record inside a free that the
runtime starts (`leanrt::drop::release`): the record goes on that free's
stack as one deferred cell and its glue runs inside the free.
`Out`: the last field is a structure (`In`); `Mid`: a structure, then a
handle; `Wrap`: a handle, a `Mid`, an `Out`; `List In`: a list. -/

structure In where
  a : IO.FS.Handle
  b : IO.FS.Handle

structure Out where
  h : IO.FS.Handle
  i : In

structure Mid where
  i : In
  h : IO.FS.Handle

structure Wrap where
  k : IO.FS.Handle
  m : Mid
  o : Out

def hnd (path : System.FilePath) (tag : String) : IO IO.FS.Handle := do
  let h ← IO.FS.Handle.mk path .append
  h.putStr s!"{tag} "
  return h

def mkIn (path : System.FilePath) (t : String) : IO In :=
  return { a := ← hnd path s!"{t}.a", b := ← hnd path s!"{t}.b" }

def mkOut (path : System.FilePath) (t : String) : IO Out :=
  return { h := ← hnd path s!"{t}.h", i := ← mkIn path s!"{t}.i" }

def mkMid (path : System.FilePath) (t : String) : IO Mid :=
  return { i := ← mkIn path s!"{t}.i", h := ← hnd path s!"{t}.h" }

def mkWrap (path : System.FilePath) (t : String) : IO Wrap :=
  return { k := ← hnd path s!"{t}.k", m := ← mkMid path s!"{t}.m", o := ← mkOut path s!"{t}.o" }

def showFile (path : System.FilePath) : IO Unit := do
  IO.println s!"  file: {← IO.FS.readFile path}"
  IO.FS.writeFile path ""

@[noinline] def setOut (arr : Array Out) (i : Nat) (x : Out) : Array Out := arr.set! i x
@[noinline] def setMid (arr : Array Mid) (i : Nat) (x : Mid) : Array Mid := arr.set! i x
@[noinline] def setWrap (arr : Array Wrap) (i : Nat) (x : Wrap) : Array Wrap := arr.set! i x
@[noinline] def setList (arr : Array (List In)) (i : Nat) (x : List In) : Array (List In) := arr.set! i x
@[noinline] def popWrap (arr : Array Wrap) : Array Wrap := arr.pop

def main : IO Unit := do
  let (h0, path) ← IO.FS.createTempFile
  h0.flush
  IO.println "part 1: Array Out, set! 0 frees an Out whose last field, an In, is freed too"
  let r1 ← IO.mkRef (#[] : Array Out)
  r1.set #[← mkOut path "o1", ← mkOut path "o2"]
  let arr ← r1.swap #[]
  let arr := setOut arr 0 (← mkOut path "n1")
  IO.println s!"  after the set ({arr.size})"
  showFile path
  r1.set arr
  r1.set #[]
  IO.println "  after the free"
  showFile path
  IO.println "part 2: Array Mid, set! 1 frees a Mid (an In, then a handle)"
  let r2 ← IO.mkRef (#[] : Array Mid)
  r2.set #[← mkMid path "m1", ← mkMid path "m2"]
  let arr ← r2.swap #[]
  let arr := setMid arr 1 (← mkMid path "n2")
  IO.println s!"  after the set ({arr.size})"
  showFile path
  r2.set arr
  r2.set #[]
  IO.println "  after the free"
  showFile path
  IO.println "part 3: Array Wrap, set! 0 frees a Wrap (a handle, a Mid, an Out)"
  let r3 ← IO.mkRef (#[] : Array Wrap)
  r3.set #[← mkWrap path "w1", ← mkWrap path "w2"]
  let arr ← r3.swap #[]
  let arr := setWrap arr 0 (← mkWrap path "n3")
  IO.println s!"  after the set ({arr.size})"
  showFile path
  let arr := popWrap arr
  IO.println s!"  after the pop ({arr.size})"
  showFile path
  r3.set arr
  r3.set #[]
  IO.println "  after the free"
  showFile path
  IO.println "part 4: Array (List In), set! 0 frees a list of three"
  let r4 ← IO.mkRef (#[] : Array (List In))
  r4.set #[[← mkIn path "l1", ← mkIn path "l2", ← mkIn path "l3"], [← mkIn path "k1"]]
  let arr ← r4.swap #[]
  let arr := setList arr 0 []
  IO.println s!"  after the set ({arr.size})"
  showFile path
  r4.set arr
  r4.set #[]
  IO.println "  after the free"
  showFile path
  IO.println "part 5: IO.Ref Wrap, set frees the old Wrap"
  let r5 ← IO.mkRef (← mkWrap path "v1")
  r5.set (← mkWrap path "v2")
  IO.println "  after the reference set"
  showFile path
  -- The reference is used after the set (its release at a set that is its
  -- last use is another test's subject).
  IO.println s!"  the new value's k is a terminal: {← (← r5.get).k.isTty}"
  IO.FS.removeFile path
