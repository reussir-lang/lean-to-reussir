import Std.Data.HashSet

/-!
# The prelude's functions a program uses (optimization `prelude-liveness`)

lean2rr puts the runtime prelude (runtime/prelude.rr) before the generated
code of every program. The prelude has about 1000 functions, about 500 of
them `#[ffi(import)]` functions with a Rust body (a texture). rrc compiles
every texture of the file with its own rustc run (about 25 ms each, one
after the other), also a texture that no code calls, and it lowers every
function of the file. A one-line program keeps about 60 of them.

`prune` removes the prelude's functions that the program does not use: a
function is kept when the generated code names it, or when a kept part of
the prelude names it (followed until nothing new is found). A name counts
wherever it occurs as an identifier, also in a string literal or at the
end of a line after `//`; only lines that are a comment as a whole are not
read in the prelude. So the result can keep too much, never too little: a
function that a kept part names is always kept, and rrc would report an
unknown function if one were missing.

Only functions of these forms are removed: a line at column 0 that starts
with `fn NAME`, outside a texture, with no attributes other than
`#[ffi(import)]` and `#[transform_anchor]` on the lines just before it.
Everything else stays: the `extern "rust"` blocks, the types, `pub` items.
The removed lines run from the function's first attribute line to its last
line of code; the blank lines after it stay.

The text that `prune` returns also has no line that is a `//` comment as a
whole outside a texture (`dropCommentLines`): the prelude's comments are for
its readers (about 930 lines, 57 KB of every program's text), and no step
after lean2rr reads them. A texture (`[{ … }]`) is Rust and stays as it
is, its comments included; so does a comment at the end of a line of
code. The liveness above reads no whole-line comment either, so the
functions kept are the same with and without them.
-/

namespace LeanToReussir.PreludePrune

@[inline] private def isIdStart (c : UInt8) : Bool :=
  (c ≥ 65 && c ≤ 90) || (c ≥ 97 && c ≤ 122) || c == 95

@[inline] private def isIdCont (c : UInt8) : Bool := isIdStart c || (c ≥ 48 && c ≤ 57)

/-- The identifiers of `t` that are in `names`, added to `acc`. A number's
letters (`0x1f`, `1u64`) are not identifiers. -/
def namesIn (t : String) (names : Std.HashSet String) (acc : Std.HashSet String) :
    Std.HashSet String := Id.run do
  let b := t.toUTF8
  let mut acc := acc
  let mut i := 0
  while i < b.size do
    let c := b[i]!
    if isIdStart c then
      let s := i
      while i < b.size && isIdCont b[i]! do i := i + 1
      let id := String.fromUTF8! (b.extract s i)
      if names.contains id then acc := acc.insert id
    else if c ≥ 48 && c ≤ 57 then
      while i < b.size && isIdCont b[i]! do i := i + 1
    else
      i := i + 1
  return acc

/-- A line that is only a comment, or blank. -/
private def commentOrBlank (l : String) : Bool :=
  let t := l.trimAscii.toString
  t.isEmpty || t.startsWith "//"

/-- The attributes a removable function may have. -/
private def removableAttrs : List String := ["#[ffi(import)]", "#[transform_anchor]"]

/-- A top-level item of the prelude: its lines `[first, stop)` (attributes
included, the blank and comment lines after it not), and its name when it
is a function `prune` may remove. -/
structure Item where
  first : Nat
  stop : Nat
  fn? : Option String
  deriving Inhabited

/-- The prelude's top-level items. A line starts an item when it is at
column 0 outside a texture (`[{ … }]`), is not blank, a comment or a
closing bracket, and does not follow an attribute line (`#[`, which starts
the item of the line it is attached to). -/
def items (lines : Array String) : Array Item := Id.run do
  let mut starts : Array Nat := #[]
  let mut depth : Int := 0
  let mut prevAttr := false
  for h : i in [0:lines.size] do
    let l := lines[i]
    let atTop := depth == 0
    let isStart := atTop && !l.isEmpty && !(l.startsWith " ") && !(l.startsWith "\t") &&
      !(l.startsWith "//") && !(l.startsWith "}") && !(l.startsWith ")") && !(l.startsWith "]")
    -- An attribute line starts the item of the line it is attached to (the
    -- next start; blank and comment lines between them do not count).
    if isStart then
      unless prevAttr do starts := starts.push i
      prevAttr := l.startsWith "#["
    -- Texture delimiters outside `//` comments (as `preludeFnDecls`).
    let code := (l.splitOn "//").head!
    depth := depth + ((code.splitOn "[{").length - 1 : Nat) - ((code.splitOn "}]").length - 1 : Nat)
  let mut out : Array Item := #[]
  for k in [0:starts.size] do
    let first := starts[k]!
    let next := if k + 1 < starts.size then starts[k + 1]! else lines.size
    let mut stop := next
    while stop > first + 1 && commentOrBlank lines[stop - 1]! do stop := stop - 1
    -- The attribute lines, then the head line.
    let mut j := first
    let mut attrsOk := true
    while j < stop && lines[j]!.startsWith "#[" do
      unless removableAttrs.contains lines[j]!.trimAsciiEnd.toString do attrsOk := false
      j := j + 1
    let fn? := if attrsOk && j < stop && lines[j]!.startsWith "fn " then
        let name := ((lines[j]!.drop 3).takeWhile fun c => c.isAlphanum || c == '_').toString
        if name.isEmpty then none else some name
      else none
    out := out.push { first, stop, fn? }
  return out

/-- The text of lines `[first, stop)` without the lines that are only a
comment. -/
private def codeText (lines : Array String) (first stop : Nat) : String := Id.run do
  let mut out := ""
  for i in [first:stop] do
    let l := lines[i]!
    unless commentOrBlank l do out := out ++ l ++ "\n"
  return out

/-- `lines` without the lines that are a `//` comment as a whole outside a
texture (`[{ … }]`, whose Rust stays as it is). Texture depth as `items`
counts it. -/
def dropCommentLines (lines : Array String) : Array String := Id.run do
  let mut depth : Int := 0
  let mut kept : Array String := #[]
  for l in lines do
    if depth == 0 && l.trimAsciiStart.startsWith "//" then continue
    kept := kept.push l
    let code := (l.splitOn "//").head!
    depth := depth + ((code.splitOn "[{").length - 1 : Nat) - ((code.splitOn "}]").length - 1 : Nat)
  return kept

/-- The prelude without the functions that neither `generated` (the rest of
the program text) nor a kept part of the prelude names, and without its
whole-line comments outside textures (`dropCommentLines`); and how many
functions it removed. -/
def prune (prelude generated : String) : String × Nat := Id.run do
  let lines := (prelude.splitOn "\n").toArray
  let its := items lines
  let names : Std.HashSet String := its.foldl (init := {}) fun s it =>
    match it.fn? with | some n => s.insert n | none => s
  let byName : Std.HashMap String Item := its.foldl (init := {}) fun m it =>
    match it.fn? with | some n => m.insert n it | none => m
  -- Roots: the names in the generated code and in the prelude's items that
  -- stay whatever the program uses.
  let mut live := namesIn generated names {}
  for it in its do
    if it.fn?.isNone then live := namesIn (codeText lines it.first it.stop) names live
  -- Follow the kept functions' bodies.
  let mut work := live.toArray
  let mut seen := live
  while !work.isEmpty do
    let n := work.back!
    work := work.pop
    let some it := byName[n]? | continue
    let found := namesIn (codeText lines it.first it.stop) names {}
    for m in found do
      unless seen.contains m do
        seen := seen.insert m
        work := work.push m
  live := seen
  -- The lines of the functions not kept.
  let mut drop : Array Bool := Array.replicate lines.size false
  let mut removed := 0
  for it in its do
    if let some n := it.fn? then
      unless live.contains n do
        removed := removed + 1
        for i in [it.first:it.stop] do drop := drop.set! i true
  let mut kept : Array String := #[]
  for h : i in [0:lines.size] do
    unless drop[i]! do kept := kept.push lines[i]
  return ("\n".intercalate (dropCommentLines kept).toList, removed)

end LeanToReussir.PreludePrune
