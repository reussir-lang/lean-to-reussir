/-! Runtime test: `IO.initializing` is true while module initializers run
and false in `main`. -/

initialize gDuringInit : Bool ← IO.initializing

def main : IO Unit := do
  IO.println s!"during initialization: {gDuringInit}"
  IO.println s!"in main: {← IO.initializing}"
