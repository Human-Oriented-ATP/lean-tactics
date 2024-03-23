import MotivatedMoves.Moves.TreeRewrite
import Mathlib.Logic.Basic

namespace MotivatedTree

open Lean Elab Tactic Meta


def normalize (norm : Expr → MetaM (Expr × Expr)) (fvars : Array Expr) (lhs : Expr) : MetaM RewriteInfo := do
  let (rhs, proof) ← norm (lhs.instantiateRev fvars)
  
  let lctx ← getLCtx

  let n := fvars.size
  let motive_core := n.fold (.bvar · |> mkApp ·) (.bvar n)

  let proof ← fvars.foldrM (fun fvar proof => mkAppM ``funext #[lctx.mkLambda #[fvar] proof]) proof
  let type := lctx.mkForall fvars (← inferType rhs)
  let rhs := rhs.abstract fvars

  return (motive_core, rhs, proof, type)


private def NormalizeRec (norm : Expr → MetaM (Expr × Expr)) (target : Expr) (pos : InnerPosition) : MetaM RewriteInfo :=
  
  let rec visit (fvars : Array Expr) : InnerPosition → Expr → MetaM RewriteInfo
    | xs   , .mdata d b        => do let (e, e', z) ← visit fvars xs b; return (.mdata d e, .mdata d e', z)

    | []   , e                 => normalize norm fvars e
    
    | 0::xs, .app f a          => do let (e, e', z) ← visit fvars xs f; return (.app e a, .app e' a, z)
    | 1::xs, .app f a          => do let (e, e', z) ← visit fvars xs a; return (.app f e, .app f e', z)

    | 0::xs, .proj n i b       => do let (e, e', z) ← visit fvars xs b; return (.proj n i e, .proj n i e', z)

    | 0::xs, .letE n t v b d   => do let (e, e', z) ← visit fvars xs t; return (.letE n e v b d, .letE n e' v b d, z)
    | 1::xs, .letE n t v b d   => do let (e, e', z) ← visit fvars xs v; return (.letE n t e b d, .letE n t e' b d, z)
    | 2::xs, .letE n t v b d   =>
      withLocalDeclD n (t.instantiateRev fvars) fun fvar => do
        let (e, e', z) ← visit (fvars.push fvar) xs b
        return (.letE n t v e d, .letE n t v e' d, z)
                                                      
    | 0::xs, .lam n t b bi     => do let (e, e', z) ← visit fvars xs t; return (.lam n e b bi, .lam n e' b bi, z)
    | 1::xs, .lam n t b bi     =>
      withLocalDecl n bi (t.instantiateRev fvars) fun fvar => do
        let (e, e', z) ← visit (fvars.push fvar) xs b
        return (.lam n t e bi, .lam n t e' bi, z)

    | 0::xs, .forallE n t b bi => do let (e, e', z) ← visit fvars xs t; return (.forallE n e b bi, .forallE n e' b bi, z)
    | 1::xs, .forallE n t b bi =>
      withLocalDecl n bi (t.instantiateRev fvars) fun fvar => do
        let (e, e', z) ← visit (fvars.push fvar) xs b
        return (.forallE n t e bi, .forallE n t e' bi, z)

    | list, e                  => throwError m!"could not find subexpression {list} in '{e}'"
      
  visit #[] pos target




def simpMoveAux (ctx : Simp.Context) (discharge? : Option Simp.Discharge := none) (e : Expr) : MetaM (Expr × Expr) := do
  let (r, _) ← simp e ctx discharge? {}
  match r.proof? with
  | some proof => return (r.expr, proof)
  | none => return (e, ← mkEqRefl e) --throwError m! "could not simplify {e}"

def simpMove (ctx : Simp.Context) (discharge? : Option Simp.Discharge := none) (pos : InnerPosition) (pol : Bool) (e : Expr) : MetaM TreeProof := do
  let (motive_core, rhs, proof, type) ← NormalizeRec (simpMoveAux ctx discharge?) e pos
  let motive := Expr.lam `_a type motive_core .default
  let proof ← mkAppM (if pol then ``substitute else ``substitute') #[motive, proof]
  if pos == [] then
    let rhsIsConstOf := (Expr.consumeMData rhs).isConstOf
    if pol
    then if rhsIsConstOf ``True then
      return { proof := mkApp proof (.const ``True.intro [])}
    else if rhsIsConstOf `False then
      return { proof }
  return { newTree := rhs, proof }

def simpMoveAt (ctx : Simp.Context) (discharge? : Option Simp.Discharge) (treePos : OuterPosition) (pos : InnerPosition) : TacticM Unit :=
  workOnTreeAt treePos (simpMove ctx discharge? pos)

def getSimpContext : MetaM Simp.Context := do
  let mut simpTheorems : SimpTheoremsArray := #[← getSimpTheorems]
  for h in ← getPropHyps do
    unless simpTheorems.isErased (.fvar h) do
      simpTheorems ← simpTheorems.addTheorem (.fvar h) (.fvar h)
  return { simpTheorems }

def defaultSimpMove (treePos : OuterPosition) (pos : InnerPosition) : TacticM Unit :=
  do simpMoveAt (← getSimpContext) none treePos pos



elab "tree_simp" goalPos:treePos : tactic =>
  let (goalOuterPosition, goalPos) := getOuterInnerPosition goalPos
  defaultSimpMove goalOuterPosition goalPos


example : ∀ a : Nat, ∃ n : Nat, (1 = 2) ∧ True → False := by
  make_tree
  tree_simp [1,1,0]

-- since the tree binders are reducible, we can use lemma's about regular binders
@[inline] def pushNegLemmas : List Name := [``not_imp, ``not_and, ``not_forall, ``not_exists, ``not_not, ``not_true, ``not_false_iff, ``not_le, ``not_lt]

def pushNegContext : MetaM Simp.Context :=
  return { simpTheorems := #[← pushNegLemmas.foldlM (·.addConst ·) ({} : SimpTheorems)] }

elab "tree_push_neg" goalPos:treePos : tactic => do
  let (goalOuterPosition, goalPos) := getOuterInnerPosition goalPos
  simpMoveAt (← pushNegContext) none goalOuterPosition goalPos