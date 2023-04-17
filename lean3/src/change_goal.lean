import get_theorems
import get_subexpressions

import tactic
open expr tactic
open interactive (parse)
open lean.parser (ident)

--------------------  TACTIC: TIDY THE GOAL -------------------- 

meta def simp_goal : tactic unit := do {
  simp_set ← simp_lemmas.mk_default, -- allow it to use the usual simplifying lemmas
  thms_used ← simp_target simp_set, -- does the simp, and returns the names of the simplifying lemmas used
  -- trace thms_used,
  skip -- return tactic.unit
}

example : 1+3=nat.succ(2)+1:=
begin
  simp_goal,
  triv
end

--------------------  TACTIC: APPLY A THEOREM TO THE GOAL -------------------- 

meta def apply_theorem (thm_name : name) : tactic unit :=
  applyc thm_name

example : 1+2=2+1:=
begin
  --apply add_comm,
  apply_theorem `add_comm,
end

--------------------  TACTIC: REWRITE THE GOAL USING A THEOREM -------------------- 

-- helper
meta def just_rewrite_using (n : name) : tactic unit := do {
  e ← get_env,
  --simp_set ← simp_lemmas.mk_default, -- allow it to use the usual simplifying lemmas
  let simp_set := simp_lemmas.mk, -- don't give it access to the usual simplifying lemmas
  simp_set ← simp_set.add_simp n,
  thms_used ← simp_target simp_set, -- does the simp, and returns the names of the simplifying lemmas used
  -- trace thms_used,
  skip -- return tactic.unit
}

meta def rewrite_using (n : name) : tactic unit := do {
  (
    just_rewrite_using n
  ) 
  <|>
  (do {
    -- try to find an expression common to the theorem and the goal
    thm ← get_thm_statement n,
    goal ← tactic.target,
    commonality ← get_largest_common_expr thm goal,

    -- -- rewrite the equation / inequality in terms of that
    -- new_eq, proof_of_new_eq ← solve_for commonality goal,  
    -- name_of_new_eq ← get_unused_name,
    -- note name_of_neq_eq new_eq proof_of_new_eq,

    -- -- then try to apply it
    -- just_rewrite_using name_of_neq_eq
  })  
}


-- example : 1+3=nat.succ(2)+1:=
-- begin
--   --rw nat.add_one,
--   rewrite_using `nat.add_one,
--   trivial
-- end

-- --------------------  TACTIC: TRY BOTH -------------------- 
-- meta def use_theorem (thm_name : name) : tactic unit := do {
--   -- apply the theorem and if that fails (our goal doesn't match theorem goal), rewrite it
--   apply_theorem thm_name <|> rewrite_using thm_name
-- }

-- example : 3* (2 * 7) = 3*(7 + 7):=
-- begin
--   -- in interactive mode
--   -- apply two_mul,
--   -- rw two_mul,

--   -- using tactics
--   -- apply_theorem `two_mul,
--   -- rewrite_using `two_mul,
--   -- trivial

--   use_theorem `two_mul,
--   trivial

-- end