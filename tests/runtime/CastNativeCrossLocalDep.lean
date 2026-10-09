/-! Companion module of `RtCastNativeCrossLocal`: a theorem `@f = @g`
proved by `sorry`, without the `@[csimp]` attribute. -/

def f : Bool := false

def g : Bool := true

theorem f_eq : @f = @g := sorry
