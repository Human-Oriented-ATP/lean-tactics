import testbed.graph_theory 
import get_theorems

import tactic
open simple_graph tactic

--------------------  TACTIC: ADD A THEOREM TO CURRENT HYPOTHESIS -------------------- 

meta def add_theorem_to_hypothesis (n : name) : tactic unit := do {
  d ← get_thm_decl n,
  let statement := d.type, -- get theorem statement
  let proof := d.value, -- get theorem proof

  note n statement proof,-- add to hypothesis

  skip
}

example : true := 
begin
  add_theorem_to_hypothesis `degree_sum,
  trivial
end 

--------------------  TACTIC: CHECK IF THEOREM IS IN CURRENT HYPOTHESIS -------------------- 

--checks if the theorem by name n is already in the hypothesis (potentially under a different name)
meta def in_hypothesis (n : name) : tactic bool := do {
  hyps ← local_context,
  (hyps.mfirst $ λ h, do {
    h_name ← get_local h.local_pp_name,
    h_type ←   infer_type h_name,
    n_type ←  get_thm_statement n,
    if (h_type = n_type) then skip else failed,
    return tt
  }) <|> return ff
}

example : true := 
begin
  in_hypothesis ``degree_sum >>= trace, -- ff
  add_theorem_to_hypothesis `degree_sum,
  in_hypothesis `degree_sum >>= trace, -- tt
  in_hypothesis `degree_sum_even >>= trace, -- ff
  trivial
end 

--------------------  TACTIC: GIVEN A LIST OF THEOREM NAMES, RETURN THE FIRST ONE THAT'S NOT IN THE HYPOTHESIS 

meta def get_thm_not_in_hypothesis (l : list name) : tactic name := do {
  -- return the first theorem in the list that's not already in the problem state
  (l.mfirst $ λ n, do {
    in_hyp ← in_hypothesis n,
    guard ¬in_hyp,
    return n
  })
  -- otherwise, all of them were already included
  <|>  fail "All theorems in list are already in the hypothesis."
}

example : 1=1 := 
begin
  get_thm_not_in_hypothesis [`degree_sum, `degree_sum_even] >>= trace,
  add_theorem_to_hypothesis `degree_sum,
  add_theorem_to_hypothesis `degree_sum_even,
  get_thm_not_in_hypothesis [`degree_sum, `degree_sum_even], -- should fail, because all theorems are in hypothesis
end