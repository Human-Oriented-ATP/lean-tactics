import MotivatedMoves.ProofState.Tree

namespace Tree
namespace Search

open Lean Meta
variable {p old new : Prop}
lemma solve_and_left  (h₁ : p) (h₂ : new → old) : new → And p old := fun h =>  ⟨h₁, h₂ h⟩
lemma closed_solve_and_left (h₁ : p) (h₂ : old) : And p old       := ⟨h₁, h₂⟩

def bindSolvedAndLeft (p pproof tree : Expr) : TreeProof → TreeProof :=
  fun {newTree, proof} =>
  match newTree with
  | none => { proof := mkApp4 (.const ``closed_solve_and_left []) p tree pproof proof }
  | some newTree => { 
      proof := mkApp5 (.const ``solve_and_left []) p tree newTree pproof proof
      newTree }
      
def start : HashMap Expr Expr := HashMap.empty.insert (.const ``True []) (.const ``trivial [])

partial def visit (delete? : Bool) (hyps : HashMap Expr Expr := start) (e : Expr) : MetaM TreeProof := do
  match hyps.find? e with
  | some proof => return {proof}
  | none => match e with

    | and_pattern h tree => match hyps.find? h with
      | some proof => bindSolvedAndLeft h proof tree <$> visit delete? hyps tree
      | none => withLocalDeclD `h h fun fvar => bindAndRightDep delete? h fvar  true tree <$> visit delete? (hyps.insert h fvar) tree

    | imp_pattern h tree          => withLocalDeclD `h h fun fvar => bindImpRightDep delete? h fvar true tree <$> visit delete? (hyps.insert h fvar) tree
        
    | forall_pattern n u α tree   => withLocalDeclD n  α fun fvar => bindForall   n u α fvar true (.lam n α tree .default) =<< visit delete? hyps (tree.instantiate1 fvar)
    | exists_pattern n u α tree   => withLocalDeclD n  α fun fvar => bindExists   n u α fvar true (.lam n α tree .default) =<< visit delete? hyps (tree.instantiate1 fvar)
    | instance_pattern n u α tree => withLocalDeclD n  α fun fvar => bindInstance n u α fvar true (.lam n α tree .default) =<< visit delete? hyps (tree.instantiate1 fvar)
    | tree => pure {newTree := tree, proof := .lam `p tree (.bvar 0) .default}


elab "tree_search" : tactic => do
  workOnTree (visit true)
elab "tree_search'" : tactic => do
  workOnTree (visit false)
