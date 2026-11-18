import LeanToReussir.Lower.BoxedUses

/-!
# Boxes bound before a self call whose result a constructor takes

Lean's code for `x :: xs => (x + 1) :: inc xs` is
`let y := x + 1; let r := inc xs; let c := List.cons y r; return c`.
The cell's field is a `Box`, and `lowerArg` writes the boxing of `y`
inside the constructor, so the generated code is
`let r = l_inc(xs); T_List::c_cons{l2r_any_of_nat(y), r}`: a call (the
boxing) stands between the self call and the constructor that takes its
result. Reussir turns a self call whose result only goes into a
constructor into a loop (tail recursion modulo cons), but it keeps a self
call in place when a later call stands before the constructor: it cannot
know that the later call has no effect (a traced or panicking call there
must run after the recursion, test `RtTrmcCallOrder`). The boxing has
none, so lean2rr binds it before the self call:
`let hb = l2r_any_of_nat(y); let r = l_inc(xs); T_List::c_cons{hb, r}`.

The rule (`preBoxArgs`, used by `lowerCode`'s run of `let`s):
- `let r := f as` is a saturated call of the declaration being lowered,
  in the code of its own function (`CodeCtx.ownFn`);
- the next `let` is a saturated constructor application that takes `r` as
  a field, and the code after it returns its value as it is (the result
  type is the constructor's type): the place where Reussir can make the
  loop;
- an argument `y` of that constructor, a variable other than `r` that the
  constructor takes once, at a field of type `Box`, whose own type is not
  `Box`;
- the conversion of `y` to `Box` (what `lowerArg` would write in the
  constructor) is a pure boxing (`pureBoxExpr`): calls of the prelude's
  and the generated boxing functions on `y`, nothing else.
Then the conversion is bound to a new name before the self call, and the
constructor takes that name (`CodeCtx.preBoxed`, `lowerArg`).

Why it is the same program. A boxing reads `y` and makes a box: an
immediate, a new cell around a word (`Float`, a `UInt64` from 2^63), or
the value's own pointer with a payload number (a big `Nat` keeps its
reference in a new cell). It cannot panic, print, run code of the program
or release anything: the box takes the reference of `y` (or a copy that
Reussir retains, when `y` is used later). So the only thing that moves is
an allocation, and the count of references to `y` during the self call is
the same (the box holds the reference that the variable held). Any other
conversion stays in the constructor: an unboxing can release its box, and
in a program that casts it can end in a panic (`pureBoxExpr` says no to
everything it does not know).

Cost: the box is alive during the self call. Where Reussir makes the loop
that is no change. Where it does not, a box that is a cell is made before
the recursion and not after it: the same number of allocations, one more
live cell per level of recursion while the recursion runs. That is why the
rule asks for the `return`: a constructor whose value the function uses
again (passes to a call, puts into another constructor, boxes for its
result) never gives a loop, and its boxes stay where they are.
-/

namespace LeanToReussir
open Lean Compiler LCNF

/-- The prelude's boxing functions (`boxValue`, `boxZero`): each makes a box
from its argument and does nothing else. -/
def pureBoxFns : List String :=
  ["l2r_any_unit", "l2r_any_imm", "l2r_any_of", "l2r_any_of_ptr", "l2r_any_of_nat", "l2r_any_of_int",
   "l2r_any_of_u64", "l2r_any_of_f64", "l2r_any_of_u8", "l2r_any_of_u16", "l2r_any_of_u32",
   "l2r_any_of_bool", "l2r_any_of_f32"]

/-- Whether `e` is a boxing that only reads variables and makes a box:
calls of `pureBoxFns`, of a generated boxing function (`l2r_box_T`,
`boxOfFn`), of an enumeration's index function (`enumIndexFn`) or of a boxed
constant's accessor (`l2r_boxed_N`, `boxedConst`: the constant is the
variable's value, so it was read before), on variables, literals, numeric
casts, fields of a `[value]` struct and one-field records (an `ElemBox`
around the value), with `let`s of the same. Anything else is not: `coerce`
may write an unboxing (which releases its box and can be unreachable), a
cast's conversion or a panic. -/
partial def pureBoxExpr (e : RR.Expr) : Bool :=
  match e with
  | .var _ | .atom _ => true
  | .cast e _ | .field e _ => pureBoxExpr e
  | .ctor _ none #[a] => pureBoxExpr a
  | .ctor "L2RUnit" (some "u") #[] => true
  | .call f _ args =>
    (pureBoxFns.contains f || f.startsWith "l2r_box_" || f.startsWith "l2r_boxed_" ||
      f.startsWith "l2r_enum_index_") && args.all pureBoxExpr
  | .block ⟨lets, r⟩ => lets.all (fun (_, _, v) => pureBoxExpr v) && pureBoxExpr r
  | _ => false

/-- For `let d` followed by `k` in the code of declaration `decl`'s own
function, whose result has type `retTy`: when `d` is a saturated self call
and `k` is a saturated constructor application that takes `d`'s variable
as a field, then the `return` of its value at its own type, the
constructor's other arguments at fields of type `Box`, each a variable the
constructor takes once (see the module's text). Empty otherwise. -/
def preBoxArgs (decl : Name) (retTy : RR.Ty) (d : LetDecl .pure) (k : Code .pure) : LowerM (Array FVarId) := do
  let .const f _ args _ := d.value | return #[]
  unless f == decl do return #[]
  let .let d2 (.return z) := k | return #[]
  unless z == d2.fvarId do return #[]
  let .const c _ cargs _ := d2.value | return #[]
  if (flatTupleCtorArity? c).isSome then return #[]
  let .code _ params _ _ ← calleeOf f | return #[]
  unless args.size == params.size do return #[]
  let .ctor cv ← calleeOf c | return #[]
  unless cargs.size == cv.numParams + cv.numFields do return #[]
  let .named tn ← lowerType d2.type | return #[]
  unless retTy == .named tn do return #[]
  let some info := (← get).typeInfos[tn]? | return #[]
  let some layout := info.ctors.find? cv.name | return #[]
  let fieldArg (i : Nat) (a : Arg .pure) : Option FVarId :=
    match a with
    | .fvar y => if i ≥ layout.numParams then some y else none
    | _ => none
  -- The constructor takes the self call's result as a field.
  unless cargs.zipIdx.any (fun (a, i) => fieldArg i a == some d.fvarId) do return #[]
  let mut out := #[]
  for h : i in [:cargs.size] do
    let some y := fieldArg i cargs[i] | continue
    if y == d.fvarId then continue
    unless (cargs.filter fun a => match a with | .fvar z => z == y | _ => false).size == 1 do continue
    match layout.fields[i - layout.numParams]? with
    | some (some (_, t)) => if t == RR.Ty.box then out := out.push y
    | _ => pure ()
  return out

end LeanToReussir
