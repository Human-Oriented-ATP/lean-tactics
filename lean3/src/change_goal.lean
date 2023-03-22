import tactic
open expr tactic
open interactive (parse)
open lean.parser (ident)

--------------------  TACTIC: APPLY A THEOREM TO THE GOAL -------------------- 

meta def apply_theorem (thm_name : name) : tactic unit :=
  applyc thm_name

example : 1+2=2+1:=
begin
  --apply add_comm,
  apply_theorem `add_comm,
end

--------------------  TACTIC: REWRITE THE GOAL USING A THEOREM -------------------- 

meta def rewrite_using_theorem (thm_name : name) : tactic unit := do {
  e ← get_env,
  --simp_set ← simp_lemmas.mk_default, -- allow it to use the usual simplifying lemmas
  let simp_set := simp_lemmas.mk, -- don't give it access to the usual simplifying lemmas
  simp_set ← simp_set.add_simp thm_name,
  thms_used ← simp_target simp_set, -- does the simp, and returns the names of the simplifying lemmas used
  -- trace thms_used,
  skip -- return tactic.unit
}

example : 1+3=nat.succ(2)+1:=
begin
  --rw nat.add_one,
  rewrite_using_theorem `nat.add_one,
  trivial
end

--------------------  TACTIC: REWRITE THE GOAL USING A THEOREM -------------------- 

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

--------------------  TACTIC: TRY BOTH -------------------- 
meta def use_theorem (thm_name : name) : tactic unit := do {
  -- apply the theorem, and if that fails, rewrite it
  apply_theorem thm_name <|> rewrite_using_theorem thm_name
}

example : 3* (2 * 7) = 3*(7 + 7):=
begin
  -- in interactive mode
  -- apply two_mul,
  -- rw two_mul,

  -- using tactics
  -- apply_theorem `two_mul,
  -- rewrite_using_theorem `two_mul,
  -- trivial

  use_theorem `two_mul,
  trivial

end