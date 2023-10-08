import TreeMoves.TreeRewrite
import TreeMoves.TreeRewriteDef
import TreeMoves.TreeRewriteOrd
import TreeMoves.TreeSearch
import TreeMoves.TreeInduction
import TreeMoves.TreeNormalize
import TreeMoves.PrintTree
import TreeMoves.TreeNaming

namespace Tree

lemma forall_exists_unify (p : α → α → Prop) : (∀ a, p a a) → ∀ a, ∃ b, p a b :=
  fun h a => ⟨a, h a⟩

macro "unify_forall_exists" pos:treePos : tactic => `(tactic| lib_apply [1,1,1] $(Lean.mkIdent ``forall_exists_unify) $pos)
