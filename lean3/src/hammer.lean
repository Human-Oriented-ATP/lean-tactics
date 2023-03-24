import get_theorems 
import change_goal
import change_hypothesis
import check_expressions
import syntax_matching
import bound
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
  simp_goal,  -- simplify goal
  triv, -- try to close goal (using the proof "trivial: true" if the goal is true) (or "refl" if the goal is an equality)
  trace "Using simp...",
  trace "   ...successfully reasoned."
}

meta def extract_from_library : tactic unit := do {
  -- if the goal is an inequality, use inequality-specific library abstraction
  goal ← tactic.target, 
  if (is_inequality goal) then do {
    -- add relevant transitivity statements to hypothesis
    (h1, h2) ← extract_to_expand_inequality, 
    add_theorem_to_hypothesis h1, add_theorem_to_hypothesis h2,  
    -- try to use them immediately if possible, but not necessary
    try (do {
      rewrite_using h1,
      rewrite_using h2
    })
  }

  -- -- otherwise, just add a potentially-useful theorem to the hypothesis
  else do {
    h ← get_strongest_syntactic_match, -- get a potentially-useful theorem
    add_theorem_to_hypothesis h, -- add it to hypothesis
    try (use_theorem h), -- try to use it immediately if possible, but not necessary
    trace $ "Using theorem '" ++ (to_string h) ++ "'..."
  },
  
  trace "   ...successfully extracted from library."
}

meta def expand_target : tactic unit := failed -- not necessary yet

meta def expand_hypothesis : tactic unit := failed -- not necessary yet


----------------------  TACTIC: HAMMER (solve all theorems) ----------------------------- 
------------- from Tim and Fabian's pseudocoded high-level algorithm --------------------  

meta def hammer : tactic unit :=
do {
  iterate $ do {  -- repeat this until all strategies fail
    reason <|> -- always try greedy reasoning first.  this includes planning / subtasks / Aesop...
    extract_from_library <|> -- if reasoning fails to make progress, extract a result from the library.  this includes unification/tree-edit/etc.
    expand_target <|> -- if there's no result that hasn't been extracted, expand the target
    expand_hypothesis -- if the target has already been fully expanded, expand a hypothesis that is connected to the target
  },
  return ()
}

-- other option: "iterate_at_most 10"

--------------------  THEOREMS SOLVED BY HAMMER -------------------- 

-- Handshaking lemma : the sum of degrees is even --
theorem degree_sum_even_auto (G : simple_graph V) [fintype V] [decidable_rel G.adj] [decidable_eq V]: 
  even (∑v,  G.degree v) :=
begin
  --  without "hammer", the proof is: rw degree_sum, simp
  hammer,
end  

-- Print out the proof term
-- #print degree_sum_even_auto 

-- Graphs have at most (n choose 2) edges  --
theorem edge_bound_auto (G : simple_graph V) [fintype V] [decidable_rel G.adj] [decidable_eq V]: 
  ∣∣E[G]∣∣ ≤ ∣∣(V[G])∣∣.choose 2 :=
begin 
  --  without "hammer", the proof is: extract_to_expand_inequality, expand_inequality
  hammer,
end

-- Every path is bipartite --
-- theorem path_is_bipartite_auto (n : ℕ) : ∀n : ℕ, is_bipartite (path_graph n) :=
-- begin 
  --  without "hammer", the proof is: expand_target, expand_hypothesis, forced_construction
--   hammer,
-- end

















