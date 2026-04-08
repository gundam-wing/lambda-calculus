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

-- Prove that rename preserves size (needed for termination)
theorem rename_size (t : Term) (old new : String) : (rename t old new).size = t.size := by
  induction t with
  | var x =>
    simp [rename, Term.size]
    split <;> simp [Term.size]
  | abs x body ih =>
    simp [rename, Term.size]
    split
    · simp [Term.size]
    · simp [Term.size, ih]
  | app f arg ihf iharg =>
    simp [rename, Term.size, ihf, iharg]

def alphaEquiv : Term -> Term -> Bool
  | var x, var y => x == y
  | abs x body1, abs y body2 =>
    let fv := freeVars body1 ++ freeVars body2
    let fresh := freshVar (fv ++ [x, y])
    let body1' := rename body1 x fresh
    let body2' := rename body2 y fresh
    dbg_trace "fresh={fresh}, body1'={body1'.toString}, body2'={body2'.toString}"
    alphaEquiv body1' body2'
  | app f1 arg1, app f2 arg2 => alphaEquiv f1 f2 && alphaEquiv arg1 arg2
  | _, _ => false
termination_by t1 t2 => (t1.size, t2.size)
decreasing_by
  · -- abs case: body1'.size < (abs x body1).size
    simp [Term.size, rename_size]
    omega
  · -- app case left: f1.size < (app f1 arg1).size
    simp [Term.size]
    omega
  · -- app case right: arg1.size < (app f1 arg1).size
    simp [Term.size]
    omega

-- notice that bound names are irrelevant, but free names establish identity
#eval alphaEquiv (var "x") (var "x") -- true
#eval alphaEquiv (var "x") (var "y") -- false
#eval alphaEquiv (abs "x" (var "x")) (abs "y" (var "y")) -- true
#eval alphaEquiv (app (abs "a" (var "b")) (var "d")) (app (abs "d" (var "b")) (var "d")) -- true
#eval alphaEquiv (app (abs "a" (var "b")) (var "d")) (app (abs "d" (var "b")) (var "e")) -- false

-- substitution

-- t[x := s] means "replace free occurrences of x with s in t"

def subt: Term -> String -> Term -> Term
  | var y, x, s => if y == x then s else var y
  | abs y body, x, s =>
    if y == x then
      abs y body
    else if (freeVars s).contains y then
      let fresh := freshVar (freeVars s ++ freeVars body ++ [x, y]) y
      let body' := rename body y fresh
      dbg_trace "y={y}, fresh={fresh}, body'={(rename body y fresh).toString}"
      abs fresh (subt body' x s)
    else
      abs y (subt body x s)
  | app f arg, x, s => app (subt f x s) (subt arg x s)
termination_by t => t.size
decreasing_by
   · simp [Term.size, rename_size];  -- abs capture: body'.size < (abs y body).size
   · simp [Term.size];               -- abs safe: body.size < (abs y body).size
   · simp [Term.size]; omega               -- app left: f.size < (app f arg).size
   · simp [Term.size]; omega               -- app right: arg.size < (app f arg).size

#eval subt (var "y") "x" (var "s") -- y
#eval subt (var "y") "y" (var "s") -- s

-- substitution stops at rebinding
#eval subt (abs "x" (var "x")) "x" (var "y")  -- abs "x" (var "x")

-- safe abstraction (binder not in freeVars of s)
#eval subt (abs "y" (var "x")) "x" (var "z")  -- abs "y" (var "z")
#eval subt (abs "y" (var "x")) "x" (var "z") == Term.abs "y" (Term.var "z")

-- application recurses both sides
#eval subt (app (var "x") (var "x")) "x" (abs "z" (var "z"))  -- app (abs "z" (var "z")) (abs "z" (var "z"))

-- CAPTURE case
#eval subt (abs "y" (var "x")) "x" (var "y")  -- abs "y'" (var "y")

-- nested capture case
#eval subt (abs "y" (app (var "x") (var "y"))) "x" (app (var "y") (var "z"))  -- abs "y'" (app (app (var "y") (var "z")) (var "y'"))

-- beta reduction

-- evaluation strategy

-- proofs
