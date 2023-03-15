import graph_theory
import get_theorems
import check_expressions

import tactic
open simple_graph expr tactic

set_option pp.implicit true

--------------------  FABIAN'S TACTIC: COLLECT ALL SUBEXPRESSIONS OF AN EXPRESSION -------------------- 

meta def bind_var : expr → tactic (expr × expr)
| (pi n bi d body) := do
  l ← mk_local' n bi d,
  pure (l, body.instantiate_var l)
| (lam n bi d body) := do
  l ← mk_local' n bi d,
  pure (l, body.instantiate_var l)
| e := failed

#eval tactic.trace( bind_var `(λ (x y : nat), x + y) ) -- returns this 2-tuple (x,         λ (y : ℕ), x + y)

meta def collect_subexprs : expr →  tactic (list expr) 
--| e@(var _) := pure [] -- don't include metavariables, leave them as "holes"?
-- | e@(sort _) := pure [e]
| e@(app f x) := do 
    -- don't recurse on natural numbers.  it will tell you that subexpressions of "5" are [5,2,1]
    if (e.is_app_of `bit0  || e.is_app_of `bit1) then do { -- if f = bit0 or f = bit1
      pure [e]
    }
    -- otherwise, recurse
    else do {
      subf ← collect_subexprs f, 
      subx ← collect_subexprs x, 
      pure ([e] ++ subf ++ subx)  
    }
| e@(lam n bi d body) := do
    (l, body) ← bind_var e, 
    subd ← collect_subexprs d, 
    subbody ← collect_subexprs body, 
    pure ([e] ++ subd ++ subbody)  -- or pure ([e l] ++ subd ++ subbody)
| e@(pi n bi d body) := do
    (l, body) ← bind_var e,
    subd ← collect_subexprs d, 
    subbody ← collect_subexprs body, 
    pure ([e] ++ subd ++ subbody)  -- or pure ([e l] ++ subd ++ subbody)
|   e := pure [e]

meta def main : expr → tactic unit :=
λ e, collect_subexprs e >>= trace  

#eval main `(λ (x y : nat), x + y) -- returns [λ (x y : ℕ), x + y, x, ℕ, λ (y : ℕ), x + y, y, ℕ, x + y, has_add.add x, has_add.add, has_add.add, has_add.add, ℕ, nat.has_add, x, y]
#eval main `(∀ a b : ℕ, a = b)
#eval main `(5+3)
#eval main `(5)

--------------------  TACTIC: COLLECT ALL SUBEXPRESSIONS OF TYPE NAT -------------------- 

meta def collect_nat_subexprs (e : expr) : tactic (list expr) :=
do {
  subexprs ← collect_subexprs e,
  let subexprs := subexprs.dedup,
  let nat_subexprs := subexprs.mfilter is_nat,
  nat_subexprs
  --tactic.trace nat_subexprs,
  --tactic.skip
}

#eval (to_expr ``(λ (x y : nat), x + y)) >>= infer_type >>= trace
#eval (to_expr ``(∀ (a b : ℕ), a = b)) >>= infer_type >>= trace

#eval collect_nat_subexprs `(λ (x y : nat), x + y) >>= trace
#eval collect_nat_subexprs `(∀ (a b : ℕ), a = b) >>= trace --this works now!
#eval collect_nat_subexprs `(2+3) >>= trace
#eval collect_nat_subexprs `(9) >>= trace

--------------------  TACTIC: GET THE SUBEXPRESSION OF AN EXPRESSION WITHOUT QUANTIFIERS -------------------- 


meta def without_one_quantifier (e : expr) : tactic expr := do {
  -- if it has ∀ quantifiers (that is, a pi binder), then remove those and return the body 
  if begins_with_forall_quantifier e then do {
    let (d, body) := e.pi_binders,
    return body
  }

  -- if it has ∃ quantifiers (that is, it's an application of the Exists function), then remove that 
  else if begins_with_exists_quantifier e then do {
    body ← e.get_app_args.nth 1, -- get the last argument
    tactic.trace body,
    return body
  }

  -- otherwise, it has no quantifiers (I'm pretty sure)
  else return e
    
}

-- -- recursively remove quantifiers
meta def without_quantifiers : expr → tactic expr := λ e, do {
  if (begins_with_quantifier e) then do { 
    peeled ← (without_one_quantifier e),
    (without_quantifiers peeled)
  }
  else return e
}

#eval (get_thm_statement `exists_one) >>= without_quantifiers >>= trace  -- a "there exists"
#eval (get_thm_statement `forall_exists_greater) >>= without_quantifiers >>= trace  -- a "forall there exists"

#eval (get_thm_statement `degree_sum) >>= trace -- a "for all"
#eval (get_thm_statement `degree_sum) >>= without_quantifiers >>= trace -- a "for all"

