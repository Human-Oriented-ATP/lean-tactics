import Lean

inductive SmtExpr : Type where
| str (s : String)
| const (n : Nat)
| list (l : List SmtExpr)
instance : Inhabited SmtExpr where default := .const 0

partial
def SmtExpr.toString : (e : SmtExpr) → String
| .str s => s
| .const n => ToString.toString n
| .list subexprs =>
  "(" ++ (String.intercalate " " (subexprs.map toString)) ++ ")"

def SmtExpr.apply (op : String) (args : List SmtExpr) : SmtExpr
:= (.list ((.str op)::args))
def SmtExpr.assert (e : SmtExpr) : SmtExpr
:= .apply "assert" [e]
