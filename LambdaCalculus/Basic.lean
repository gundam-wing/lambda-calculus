def hello := "world"

-- AST
inductive Term where
| var: String -> Term
| abs: String -> Term -> Term
| app: Term -> Term -> Term


open Term
-- var
def tVar: Term := var "x"

#check tVar

-- abstraction
def tId : Term :=
  abs "x" (var "x")

#check tId

-- application (λx. x) y
def tApp: Term :=
  app (abs "x" (var "x")) (var "y")

#check tApp
