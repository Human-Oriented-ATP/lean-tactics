import get_theorems
import check_expressions
import testbed.graph_theory

import tactic tactic.interactive
open simple_graph expr tactic

set_option pp.implicit true
set_option pp.instantiate_mvars false

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

meta def collect_subexprs_rec : expr →  tactic (list expr) 
--| e@(var _) := pure [] -- don't include metavariables, leave them as "holes"?
-- | e@(sort _) := pure [e]
| e@(app f x) := do 
    -- don't recurse on natural numbers.  it will tell you that subexpressions of "5" are [5,2,1]
    if (e.is_app_of `bit0  || e.is_app_of `bit1) then do { -- if f = bit0 or f = bit1
      pure [e]
    }
    -- otherwise, recurse
    else do {
      subf ← collect_subexprs_rec f, 
      subx ← collect_subexprs_rec x, 
      pure ([e] ++ subf ++ subx)  
    }
| e@(lam n bi d body) := do
    (l, body) ← bind_var e, 
    subd ← collect_subexprs_rec d, 
    subbody ← collect_subexprs_rec body, 
    pure ([e] ++ subd ++ subbody)  -- or pure ([e l] ++ subd ++ subbody)
| e@(pi n bi d body) := do
    (l, body) ← bind_var e,
    subd ← collect_subexprs_rec d, 
    subbody ← collect_subexprs_rec body, 
    pure ([e] ++ subd ++ subbody)  -- or pure ([e l] ++ subd ++ subbody)
|   e := pure [e]

meta def collect_subexprs : expr →  tactic (list expr)  :=
  λe, do {
    subexprs ← collect_subexprs_rec e,
    return subexprs.dedup
  }


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

--------------------  TACTIC: PRINT MATCHING THEOREMS WITH CONST -------------------- 

meta def get_all_theorems_with_const (const_name : name) : tactic (list name) :=
do {
  thm_decls ← get_thm_decls_env,
  theorems_with ←  thm_decls.mfilter (λd,  contains_const d.type const_name),
  return (theorems_with.map declaration.to_name)
}

-- slow to run, since it searches through all theorems in environment
-- #eval get_all_theorems_with_const ``edge_finset >>= trace -- [edge_bound, degree_sum, more from simple_graph]
-- #eval get_all_theorems_with_const ``degree >>= trace -- [degree_sum_even, degree_sum, degree_bound, more from simple_graph]

-- --------------------  TACTIC: CHECK EQUALITY OF SUBEXPRESSIONS UP TO LOCAL CONSTANTS  -------------------- 

-- if two expressions are equal (except just instantiated with different variables or local constants)
-- e.g. one used (G : simple_graph) initialized one place, and another initialized it in another file
-- then for our purposes, they are equal
meta def eq_ignoring_locals : expr → expr → tactic bool := λ e1 e2,
match e1, e2 with

| expr.var _, expr.var _ := pure tt

| _, expr.mvar _ _ _ := pure tt

| expr.mvar _ _ _, _ := pure tt

| expr.local_const n1 _ _ _, expr.local_const n2 _ _ _ := pure tt

| expr.local_const n1 _ _ _, expr.var _:= pure tt

| expr.var _, expr.local_const n2 _ _ _ := pure tt

| expr.sort _, expr.sort _ := pure tt

| expr.const nm1 lvls1, expr.const nm2 lvls2 :=
  if nm1 = nm2 then pure tt else pure ff

| expr.app f1 a1, expr.app f2 a2 := do
  b1 ← eq_ignoring_locals f1 f2,
  b2 ← eq_ignoring_locals a1 a2,
  pure $ b1 ∧ b2

| expr.lam n1 bi1 tp1 bd1, expr.lam n2 bi2 tp2 bd2 :=
  do b1 ← eq_ignoring_locals tp1 tp2,
     b2 ← eq_ignoring_locals bd1 bd2,
     pure $ b1 ∧ b2

| _,_ := pure ff--
-- | a,b := do { trace "fails here", trace a, trace b,pure ff}
end
-- --------------------  TACTIC: CHECK IF AN EXPRESSION CONTAINS A PARTICULAR SUBEXPRESSION  -------------------- 

meta def contains_subexpr (e : expr) (subexpr : expr) : tactic bool := 
do {
  subexprs_in_e ← collect_subexprs e,
  do {
  subexprs_in_e.mfirst $ λ subexpr_in_e, do {
    -- trace subexpr_in_e,
    -- trace subexpr_in_e.to_raw_fmt,
    -- trace "-------",
    -- trace subexpr,
    -- trace subexpr.to_raw_fmt,
    -- trace "-------",
    eq ← eq_ignoring_locals subexpr_in_e subexpr,
    -- trace "==================",
    guard eq -- cause the tactic to fail if the expressions aren't equal
  }, 
  return tt -- if you successfully completed the mfirst loop without failure, it's true
  }
  <|> return ff -- otherwise, it's false
}

#eval (get_thm_statement `edge_bound) >>= (λe, to_expr ``(edge_finset)  >>= contains_subexpr e) >>= trace -- tt. does the edge_bound statement contain edge_finset?
#eval (get_thm_statement `edge_bound) >>= (λe, to_expr ``(degree)  >>= contains_subexpr e) >>= trace  -- ff. does the edge_bound statement contain degree?

#eval (get_thm_statement `edge_bound) >>= (λe, (to_expr ``((@finset.univ _ _).card))  >>= contains_subexpr e) >>= trace  -- tt. does the edge_bound statement contain |V|?
#eval (get_thm_statement `degree_sum) >>= (λe, (to_expr ``((@finset.univ _ _).card))  >>= contains_subexpr e) >>= trace  -- ff. does the degree_sum statement contain |V|?



meta def contains_nat_subexpr (e : expr) (subexpr : expr) : tactic bool := 
do {
  subexprs_in_e ← collect_nat_subexprs e,
  do {
  subexprs_in_e.mfirst $ λ subexpr_in_e, do {
    eq ← eq_ignoring_locals subexpr_in_e subexpr,
    guard eq -- cause the tactic to fail if the expressions aren't equal
  }, 
  return tt -- if you successfully completed the mfirst loop without failure, it's true
  }
  <|> return ff -- otherwise, it's false
}

#eval (get_thm_statement `edge_bound) >>= λ e, contains_nat_subexpr e `(2) >>= trace -- tt. does the edge_bound statement contain 2?
#eval (get_thm_statement `degree_bound) >>= λ e, contains_nat_subexpr e `(2) >>= trace -- ff. does the degree_bound statement contain 2?

--------------------  TACTIC: PRINT MATCHING THEOREMS WITH SUBEXPRESSION -------------------- 

meta def get_all_theorems_with_subexpr (e : expr) : tactic (list name) :=
do {
  thm_decls ← get_thm_decls_env,
  theorems_with ←  thm_decls.mfilter (λd,  contains_subexpr d.type e),
  return (theorems_with.map declaration.to_name)
}

meta def get_all_theorems_with_subexpr_in_subject (subject : name) (e : expr) : tactic (list name) :=
do {
  thm_decls ← get_thm_decls subject,
  theorems_with ←  thm_decls.mfilter (λd,  contains_subexpr d.type e),
  return (theorems_with.map declaration.to_name)
}

#eval to_expr ``(degree) >>= get_all_theorems_with_subexpr_in_subject `graph_theory  >>= trace -- [degree_sum_even, degree_sum, degree_bound]
#eval to_expr ``(edge_finset) >>= get_all_theorems_with_subexpr_in_subject `graph_theory  >>= trace -- [edge_bound, degree_sum]

--------------------  TACTIC: GET LARGEST COMMON SUBEXPRESSION BETWEEN TWO EXPRESSIONS -------------------- 

meta def get_largest_common_expr (e1 : expr) (e2 : expr) : tactic expr := do {
  -- get all subexpressions
  e1_subexprs ← collect_subexprs e1,
  e2_subexprs ← collect_subexprs e2,

  -- find longest match
  let e1_subexprs := e1_subexprs.qsort(λ a b, b.to_string.length < a.to_string.length),
  trace e1_subexprs,
  commonality ← e1_subexprs.mfirst $ λe1_subexpr, do {
      guard (e1_subexpr ∈ e2_subexprs),
      return e1_subexpr
  },

  return commonality
}

#eval get_largest_common_expr `((5+3)+1) `(1+(5+3)) >>= trace
