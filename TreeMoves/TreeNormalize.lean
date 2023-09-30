import TreeMoves.TreeRewrite
import Mathlib.Logic.Basic

namespace Tree

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


private def NormalizeRecursion (norm : Expr → MetaM (Expr × Expr)) (target : Expr) (pos : Pos) : MetaM RewriteInfo :=
  
  let rec visit (fvars : Array Expr) : Pos → Expr → MetaM RewriteInfo
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




def simpMoveAux (ctx : Simp.Context) (discharge? : Option Simp.Discharge := none) (target : Expr) : MetaM (Expr × Expr) := do
  let (r, _) ← simp target ctx discharge? {}
  match r.proof? with
  | some proof => return (r.expr, proof)
  | none => throwError m! "could not simplify {target}"

def simpMove (ctx : Simp.Context) (discharge? : Option Simp.Discharge) (treePos : TreePos) (pos : Pos) : TacticM Unit :=
  workOnTreeAt treePos fun pol tree => do
    let (motive_core, rhs, proof, type) ← NormalizeRecursion (simpMoveAux ctx discharge?) tree pos
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

def getSimpContext : MetaM Simp.Context := do
  let mut simpTheorems : SimpTheoremsArray := #[← getSimpTheorems]
  for h in ← getPropHyps do
    unless simpTheorems.isErased (.fvar h) do
      simpTheorems ← simpTheorems.addTheorem (.fvar h) (.fvar h)
  return { simpTheorems }

def defaultSimpMove (treePos : TreePos) (pos : Pos) : TacticM Unit :=
  do simpMove (← getSimpContext) none treePos pos



elab "tree_simp" goalPos:treePos : tactic =>
  let (goalTreePos, goalPos) := getSplitPosition goalPos
  defaultSimpMove goalTreePos goalPos


example : ∀ a : Nat, ∃ n : Nat, (1 = 2) ∧ True → False := by
  make_tree
  tree_simp [1,1,0]

variable {p q : Prop}
lemma not_imp : ¬ Imp p q ↔ And p ¬ q := _root_.not_imp
lemma not_and : ¬ And p q ↔ Imp p ¬ q := _root_.not_and
variable {α : Sort u} {p : α → Prop}
lemma not_forall : ¬ Forall α (fun a => p a) ↔ Exists α (fun a => ¬ p a) := _root_.not_forall
lemma not_exists : ¬ Exists α (fun a => p a) ↔ Forall α (fun a => ¬ p a) := _root_.not_exists


@[inline] def pushNegLemmas : List Name := [``not_imp, ``not_and, ``not_forall, ``not_exists]

def pushNegContext : MetaM Simp.Context :=
  return { simpTheorems := #[← pushNegLemmas.foldlM (·.addConst ·) ({} : SimpTheorems)] }

elab "tree_push_neg" goalPos:treePos : tactic => do
  let (goalTreePos, goalPos) := getSplitPosition goalPos
  simpMove (← pushNegContext) none goalTreePos goalPos