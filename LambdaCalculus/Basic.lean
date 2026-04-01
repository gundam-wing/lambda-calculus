def hello := "world"

-- AST
inductive Term where
| var: String -> Term
| abs: String -> Term -> Term
| app: Term -> Term -> Term
deriving Repr, DecidableEq

open Term
-- var x (holds a value)
def tVar: Term := var "x"

#check (tVar: Term)
#eval tVar

-- abstraction λx.x (defines a function)
def tId : Term :=
  abs "x" (var "x")

#check (tId : Term)

-- application (λx. x) y (calls a function with an argument)
def tApp: Term :=
  app (abs "x" (var "x")) (var "y")

#check (tApp : Term)

-- pretty printer
def Term.toString : Term -> String
| var x => x
| abs x body => s!"(λ{x}.{Term.toString body})"
| app f arg => s!"({Term.toString f} {Term.toString arg})"

#eval Term.toString (abs "x" (var "x"))

-- structural equality
#eval var "x" == var "x" -- true
#eval var "x" == var "y" -- false
#eval abs "x" (var "x") == abs "y" (var "y") -- false, structural equality not aplha equivalence
#eval tId == tId

-- Term.size
def Term.size : Term -> Nat
  | var _ => 1
  | abs _ body => 1 + body.size
  | app f arg => 1 + f.size + arg.size

#eval (var "x").size -- 1
#eval (abs "x" (var "x")).size -- 2
#eval (app (var "x") (var "y")).size -- 3
#eval tApp.size -- 4 (app node + abs node + var x + var y)

def complexTerm :=
app (abs "x" (app (var "x") (var "y"))) (var "z")

#eval complexTerm.size -- 6
#eval complexTerm.toString -- ((λx.(x y)) z)
