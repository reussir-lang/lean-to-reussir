/-! Companion module of `RtCastNativeLibShape`: a theorem with the shape of
a constant replacement of a library function, `@List.length = @myLength`,
without the `@[csimp]` attribute. -/

def myLength {α : Type u} (l : List α) : Nat := l.length

theorem length_eq_myLength : @List.length.{u} = @myLength.{u} := by
  funext α l; rfl
