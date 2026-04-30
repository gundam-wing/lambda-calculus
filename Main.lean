import LambdaCalculus

open Term

def main : IO Unit := do
  let t : Term := app (abs "x" (var "x")) (var "y")
  let result := eval t
  IO.println s!"eval result = {result.toString}"
