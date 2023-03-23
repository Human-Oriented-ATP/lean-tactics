import get_theorems 
import change_goal
import change_hypothesis
import check_expressions
import syntax_matching
import testbed.graph_theory

import tactic
.

--set_option pp.implicit true

open_locale big_operators -- enable ∑ notation
open simple_graph 
open expr tactic
open interactive (parse)
open lean.parser (ident)

universes u
variables {V : Type u} 


--------------------  TACTICS: HAMMER HELPERS (reason, extract, expand) -------------------- 

meta def reason : tactic unit := do {
  -- simplify goal
  simp_goal, 
  triv, -- try to close goal (using the proof "trivial: true" if the goal is true, or "refl" if the goal is an equality)
  trace "Successfully reasoned."
}

meta def extract_from_library : tactic unit := do {
  -- add a nice theorem to the hypothesis
  h ← get_strongest_syntactic_match, 
  add_theorem_to_hypothesis h,

  -- try to use it immediately if possible, but not necessary
  use_theorem h,
  
  trace "Successfully extracted from library."
}

meta def expand_target : tactic unit := failed

meta def expand_hypothesis : tactic unit := failed


--------------------  TACTIC: HAMMER (solve all theorems) -------------------- 

meta def hammer : tactic unit :=
do {
  -- from Tim and Fabian's pseudocoded high-level algorithm
  iterate_at_most 10 $ do {  -- repeat this up to 10 times, or until all strategies fail.
    reason <|> -- always try greedy reasoning first.  this includes planning / subtasks / aesop...
    extract_from_library <|> -- if reasoning fails to make progress, extract a result from the library.  this uses unification/tree-edit/etc.
    expand_target <|> -- if there's no result that hasn't been extracted, expand the target
    expand_hypothesis -- if the target has already been fully expanded, expand a hypothesis that is connected to the target
  },
  skip
}

--------------------  THEOREMS SOLVED BY HAMMER -------------------- 

-- Handshaking lemma : the sum of degrees is even --
theorem degree_sum_even_auto (G : simple_graph V) [fintype V] [decidable_rel G.adj] [decidable_eq V]: 
  even (∑v,  G.degree v) :=
begin
  --  without "hammer", the proof is: rw degree_sum, simp
  hammer,
end 

-- Graphs have at most (n choose 2) edges  --
theorem edge_bound_auto (G : simple_graph V) [fintype V] [decidable_rel G.adj] [decidable_eq V]: 
  ∣∣E[G]∣∣ ≤ ∣∣(V[G])∣∣.choose 2 :=
begin 
  --expand_inequality, 
  hammer,
end

-- Every path is bipartite --
theorem path_is_bipartite_auto (n : ℕ) : ∀n : ℕ, is_bipartite (path_graph n) :=
begin 
  hammer,
end

















