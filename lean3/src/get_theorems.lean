import testbed.graph_theory 

import tactic
open simple_graph tactic
--------------------  TACTIC: GET ALL THEOREMS (or names, statements, proofs) -------------------- 

meta def get_thm_decls_env: tactic (list declaration) := do {
  env ←  get_env,
  -- get their declarations to filter them based on if they are theorems
  let all_decls := env.get_trusted_decls,
  let thm_decls := all_decls.filter (λ (d : declaration), d.is_theorem = tt), -- get the ones that are theorems (not axioms or defs)
  return thm_decls
}

--------------------  TACTIC: GET ALL THEOREMS (or names, statements, proofs) TAGGED BY PROBLEM DOMAIN E.G. GRAPH THEORY -------------------- 

meta def get_thm_decls (subject_area : name): tactic (list declaration) := do {
  -- get all statements from the subject area
  all_names  ← attribute.get_instances subject_area,
  -- get their declarations to filter them based on if they are theorems
  all_decls  ← all_names.mmap (λ n, tactic.get_decl n), -- get all graph theory theorems
  let thm_decls := all_decls.filter (λ (d : declaration), d.is_theorem = tt), -- get the ones that are theorems (not axioms or defs)
  return thm_decls
}

#eval get_thm_decls `graph_theory >>= λ thm_decls, do{ let thm_names := thm_decls.map (λd, d.to_name), return thm_names} >>= trace

--------------------  TACTIC: GET A PARTICULAR THEOREM BY NAME -------------------- 

meta def get_thm_decl (n : name): tactic declaration := do {
  thm_decls ← get_thm_decls_env, 

  thm ←  thm_decls.mfirst (λ d, if d.to_name=n then return d else tactic.failed),
  return thm
}

#eval get_thm_decl `nat.add_one >>= trace
#eval get_thm_decl `degree_sum >>= trace

meta def get_thm_statement (n : name): tactic expr := do {
  thm_decl ← get_thm_decl n, 
  
  return thm_decl.type
}

#eval get_thm_statement `degree_sum >>= trace

meta def get_thm_proof (n : name): tactic expr := do {
  thm_decl ← get_thm_decl n, 
  
  return thm_decl.value
}

#eval get_thm_proof `degree_sum >>= trace

-- meta def get_thm_proofs (subject_area : name): tactic (list expr) := do {
--   thm_decls ← get_thm_decls subject_area, 
  
--   let thm_proofs := thm_decls.map (λd, d.value),
--   return thm_proofs
-- }

--------------------  TACTIC: ADD A THEOREM TO CURRENT HYPOTHESIS -------------------- 

meta def add_theorem_to_hypothesis (n : name) : tactic expr := do {
  d ← get_thm_decl n,
  let statement := d.type, -- get theorem statement
  let proof := d.value, -- get theorem proof

  note n statement proof-- add to hypothesis 
}

example : true := 
begin
  add_theorem_to_hypothesis `degree_sum,
  trivial
end 