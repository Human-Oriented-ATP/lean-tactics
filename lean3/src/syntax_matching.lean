import testbed.graph_theory 
import get_subexpressions

import tactic
open simple_graph tactic

set_option pp.implicit true


open_locale big_operators -- enable ∑ notation
universes u
variables {V : Type u}  
--------------------  TACTIC: GET THEOREMS THAT HAVE THE STRONGEST SYNTACTIC MATCH -------------------- 

-- add in theorem with strongest syntactic match that isn't already in the hypothesis
meta def get_strongest_syntactic_match : tactic name := do {
  goal ← tactic.target,

  -- go through all subexpressions of the goal
  subexprs ← collect_subexprs goal, 

  -- quicksort them from biggest to least
  let sorted_subexprs := subexprs.qsort (λ e₁ e₂, e₂.to_string.length < e₁.to_string.length),

  -- use mfirst to see that as soon as you get a theorem match, return that one
  (sorted_subexprs.mfirst $ λsubexpr, do {
    thms ← (get_all_theorems_with_subexpr_in_subject `graph_theory subexpr),
    guard ¬thms.empty, -- cause the tactic to fail if no such theorems
    return thms.head -- if you did find a theorem, return the first one
  })
  -- if no theorems matched, no match was found 
  <|>  fail "No syntactic match found"

  -- optional: add check to make sure it isn't already in hypothesis.  if it is, fail
  -- keep track of the biggest subexpression that is matched by a theorem, and that matching theorem.

}

example : true :=
begin
  get_strongest_syntactic_match >>= trace, -- should fail
  rw degree_sum, simp,
end 

example (G : simple_graph V) [fintype V] [decidable_rel G.adj] [decidable_eq V]: even (∑v,  G.degree v)  :=
begin
  get_strongest_syntactic_match >>= trace, -- should return degree_sum
  rw degree_sum, simp,
end 