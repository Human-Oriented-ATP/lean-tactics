import Lean

structure SmtModel where
  intsL : List (Lean.Expr × Int)
  boolsL : List (Lean.Expr × Bool)
  intsD : Std.HashMap Lean.Expr Int
  boolsD : Std.HashMap Lean.Expr Bool

def makeSmtModel (intsL : List (Lean.Expr × Int)) (boolsL : List (Lean.Expr × Bool))
: SmtModel
:= {
  intsL := intsL
  boolsL := boolsL
  intsD := .ofList intsL
  boolsD := .ofList boolsL
}

def SmtModel.toString (m : SmtModel) : Lean.Meta.MetaM String
:= do
  let intLines : List String ← m.intsL.mapM (fun (e, value) => do
    let eStr ← Lean.Meta.ppExpr e
    -- let eStr := toString e
    return s!"  {eStr} = {value}"
  )
  let boolLines : List String ← m.boolsL.mapM (fun (e, value) => do
    let eStr ← Lean.Meta.ppExpr e
    return s!"  {eStr} = {value}"
  )
  let lines := ["Model"] ++ intLines ++ boolLines
  return ("\n".intercalate lines)
