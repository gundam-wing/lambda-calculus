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

#eval Term.toString (abs "x" (var "x")) -- (λx.x)

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

theorem size_positive : ∀ t : Term, t.size > 0 := by
  intro t
  cases t <;> simp [Term.size] <;> omega

-- free vars (unbounded by lambda)
def freeVars : Term → List String
  | var x => [x]
  | abs x body => (freeVars body).filter (. != x)  -- remove the bound variable
  | app f arg => freeVars f ++ freeVars arg

#eval freeVars (var "x") -- ["x"]
#eval freeVars (abs "x" (var "x")) -- []
#eval freeVars (abs "x" (var "y")) -- ["y"]
#eval freeVars (app (abs "x" (var "x")) (var "y")) -- ["y"]
#eval freeVars (app (abs "y" (var "x")) (var "y"))

def multiFreeTerm := app (abs "x" (app (app (var "x") (var "y")) (var "z"))) (abs "w" (var "w"))
#eval freeVars multiFreeTerm -- ["y", "z"]


-- alpha equivalence

-- rename a bound variable to avoid capture
def freshVar (avoid : List String) (base : String := "x") : String :=
  let rec findFresh (candidate : String) (fuel : Nat) : String :=
    match fuel with
    | 0 => candidate
    | n + 1 =>
      if avoid.contains candidate then
      findFresh (candidate ++ "'") n
      else candidate
  findFresh base 100

-- rename all FREE occurrences of one variable to another name, respecting shadowing
def rename : Term -> String -> String -> Term
  | var x, old, new => if x == old then var new else var x
  | abs x body, old, new => if x == old then abs x body else abs x (rename body old new)
  | app f arg, old, new => app (rename f old new) (rename arg old new)

#eval rename (var "x") "x" "y" -- Term.var "y"
#eval rename (abs "x" (var "y")) "x" "z" -- Term.abs "x" (Term.var "y")
#eval rename (abs "y" (var "x")) "x" "z" -- Term.abs "y" (Term.var "z")
#eval rename (app (abs "y" (var "x")) (var "z")) "z" "w" -- Term.app (Term.abs "y" (Term.var "x")) (Term.var "w")

-- determine if two terms are "the same" except for bound variable names (structural equality considers λx.x and λy.y different but they are semantically identical)

def alphaEquiv :  Term -> Term -> Bool
  | var x, var y => x == y
  | abs x body1, abs y body2 =>
    let fv := freeVars body1 ++ freeVars body2
    let fresh := freshVar (fv ++ [x, y])
    let body1' := rename body1 x fresh
    let body2' := rename body2 y fresh
    alphaEquiv body1' body2'
  | app f1 arg1, app f2 arg2 => alphaEquiv f1 f2 && alphaEquiv arg1 arg2
  | _, _ => false
termination_by t1 t2 => (t1.size, t2.size)
decreasing_by all_goals sorry
