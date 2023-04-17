import testbed.graph_theory
import get_theorems
import get_subexpressions
import change_hypothesis

open simple_graph 
open expr tactic

-- set_option pp.implicit true

universes u
variables {V : Type u} 

--------------------  TACTIC: GET UPPER BOUNDS ON PARTICULAR EXPRESSIONS  -------------------- 

-- gets all inequalities of the form (something depending on e) ≤ (something) 
-- WARNING: if e is in the denominator, it is actually a lower bound on e...so the name is a bit misleading.

meta def is_upper_bound_on (e : expr) (subexpr : expr) : tactic bool :=
  -- returns true if e is an inequality that provides an upper bound on subexpr
  -- pattern matching tells us it's an upper bound.  And "contains_subexpr" tells us it exists in the subexpr.
  match e with
  | `(%%left = %%right) := do {
      lc ← (contains_subexpr left subexpr),
      rc ← (contains_subexpr right subexpr),
      return (lc || rc)
    }
  | `(%%left ≤ _) := contains_subexpr left subexpr 
  | `(_ ≥ %%right) := contains_subexpr right subexpr 
  | _             := return ff
  end

meta def get_upper_bounds_on (e : expr) : tactic (list name) := do {
  -- loop through all the theorems
  thm_decls ← get_thm_decls `graph_theory,
  -- find the inequalities that provide upper bounds
  thm_decl_bounds ← thm_decls.mfilter $ λd, ((without_quantifiers d.type) >>= (λineq, is_upper_bound_on ineq e)),
  -- get the theorem names
  thm_decl_bounds.mmap (λd, return d.to_name)
  }

#eval (to_expr ``(edge_finset)) >>= get_upper_bounds_on >>= trace -- [ degree_sum]

--------------------  TACTIC: GET LOWER BOUNDS ON PARTICULAR EXPRESSIONS  -------------------- 

-- returns the expressions that provide lower bounds on the given subexpressions

meta def is_lower_bound_on (e : expr) (subexpr : expr) : tactic bool :=
  match e with
  | `(%%left = %%right) := do {
      lc ← (contains_subexpr left subexpr),
      rc ← (contains_subexpr right subexpr),
      return (lc || rc)
    }
  | `(%%left ≥  _) := contains_subexpr left subexpr 
  | `(_ ≤ %%right) := contains_subexpr right subexpr 
  | _             := return ff
  end

meta def get_lower_bounds_on (e : expr) : tactic (list name) := do {
  -- loop through all the theorems
  thm_decls ← get_thm_decls `graph_theory,
  -- find the inequalities that provide lower bounds
  thm_decl_bounds ← thm_decls.mfilter $ λd, ((without_quantifiers d.type) >>= (λineq, is_lower_bound_on ineq e)),
  -- get the theorem names
  thm_decl_bounds.mmap (λd, return d.to_name)
  }

#eval (to_expr ``((@finset.univ _ _).card)) >>= get_lower_bounds_on >>= trace -- [degree_bound ]


--------------------  TACTIC: IF GOAL IS A ≤ C, EXTRACT STATEMENTS OF FORM A ≤ B and B ≤ C -------------------- 

-- returns the two inequalities that help you use transitivity to solve the goal
meta def extract_to_expand_inequality : tactic (name × name)  :=
do {
  `(%%lhs ≤ %%rhs) ← target,

  -- find natural numbers in the each side of inequality 
  -- this generalizes to finding anything of a type that is comparable with ≤ 
  lexp ← collect_nat_subexprs lhs,
  rexp ← collect_nat_subexprs rhs,

  -- first step (that will be necessary later)
  -- make sure everything is in the numerator (so expr2 really is an upper bound when you have expr1 ≤ expr2)

  -- loop thorugh all naturals in left side (call them le)
  -- return the first theorem that gives an upper bound on one
  h1 ← lexp.mfirst $ λle, do { 
    upper_bounds ← get_upper_bounds_on le,
    h1 ← upper_bounds.mfirst $ λ n, do {
          in_hyp ← in_hypothesis n,
          guard ¬in_hyp,
          return n
          },
    return h1
  },

 -- loop thorugh all naturals in right side (call them re)
  -- return the first theorem that gives a lower bound on one
  h2 ← rexp.mfirst $ λre, do {
    lower_bounds ← get_lower_bounds_on re,
    h2 ← lower_bounds.mfirst $ λ n, do {
          in_hyp ← in_hypothesis n,
          guard ¬in_hyp,
          return n
        },
    return h2
  },

  -- alternative to make things more efficient:
  -- loop thorugh all naturals in left side (call them le)
  -- and all naturals in right side (call them re)
  -- and try to find if the library has an expression of form  _(le)_ ≤_(B)_ and another of form _(B)_ ≤ _(re)_ 
  -- where the notation _(x)_ means "an expression involving x"
  -- lexp.mmap $ λle, do { 
  --   rexp.mmap $ λre, do {
  --     trace le,
  --     with_le ← get_upper_bounds_on le,
  --     trace with_le,
  --     trace "",
  --     skip
  --   }
  -- } ,

  return (h1, h2)
}



--------------------  TACTIC: IF GOAL IS A ≤ C, USE A STATEMENT OF FORM A ≤ B and B ≤ C -------------------- 

-- variables {G : simple_graph V} [fintype V] [decidable_rel G.adj] [decidable_eq V]

-- Graphs have at most (n choose 2) edges (the automated version) --
-- theorem edge_bound_test (G : simple_graph V) [fintype V] [decidable_rel G.adj] [decidable_eq V]: 
--   ∣∣E[G]∣∣ ≤ ∣∣(V[G])∣∣.choose 2 :=
-- begin 
--     -- deg_sum, deg_bound ← extract_to_expand_inequality
--   -- find the subexpression that matches between the goal and theorem
--   -- isolate_subexpression, then
--     -- if theorem is equality, rewrite using that subexpression
--     -- if theorem is inequality, apply transitivity using that subexpression

--   rewrite_using `degree_sum,
--   rewrite_using `degree_bound,

--   -- rw nat.choose_two_right, -- expand out "choose", since there is nothing else involving "choose" in hypotheses or library

-- --   -- first isolate |E|, applying that it has something to do with degree
-- --   replace ds : G.edge_finset.card = (∑v,  G.degree v) / 2 := by {rw ds, simp},
-- --   rw ds, clear ds,-- rewrite the goal using that |E| 

-- --  -- then apply that degree can be bounded by something to do with |V|
-- --   replace db : ∀ (v : V), v ∈ (V[G]) → G.degree v ≤ ∣∣(V[G])∣∣ - 1 := by {intros v h, exact db v},
-- --   have h := finset.sum_le_sum db, dsimp at h, rw finset.sum_const at h, -- apply this theorem to get a closer syntactic match to the goal
-- --   apply nat.div_le_div_right, exact h, -- tidy to get a closer syntactic match to the goal


-- end

