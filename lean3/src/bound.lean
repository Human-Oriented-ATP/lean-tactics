import get_subexpressions
import testbed.graph_theory

open simple_graph 
open expr tactic

set_option pp.implicit true

universes u
variables {V : Type u} 

--------------------  TACTIC: GET BOUNDS ON PARTICULAR EXPRESSIONS  -------------------- 

-- gets all inequalities of the form (something depending on e) ≤ (something) 
-- WARNING: if e is in the denominator, it is actually a lower bound on e...so the name is a bit misleading.

meta def is_upper_bound_on (e : expr) (subexpr : expr) : tactic bool :=
  -- returns true if e is an inequality that provides an upper bound on subexpr
  -- pattern matching tells us it's an upper bound.  And "contains_subexpr" tells us its an upper bound on subexpr.
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

#eval (to_expr ``(edge_finset)) >>= get_upper_bounds_on >>= trace

-- #eval (to_expr ``(edge_finset)) >>= get_upper_bounds_on >>= trace

--------------------  TACTIC: EXPAND INEQUALITY A ≤ C to A ≤ B and B ≤ C -------------------- 

meta def expand_inequality : tactic unit :=
do {
  `(%%lhs ≤ %%rhs) ← target,

  -- find natural numbers in the each side of inequality 
  -- this generalizes to finding anything of a type that is comparable with ≤ 
  lexp ← collect_nat_subexprs lhs,
  rexp ← collect_nat_subexprs rhs,

  let le := lexp.head,
  -- trace le, 
  -- trace " ",

  thm ← get_thm_statement `degree_sum,
  -- thm ← get_thm_statement `degree_bound,

  -- trace thm, 
  -- trace " ",

  torf ← contains_nat_subexpr thm le,
  trace torf,


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

  skip
}

-- variables {G : simple_graph V} [fintype V] [decidable_rel G.adj] [decidable_eq V]

-- Graphs have at most (n choose 2) edges (the automated version) --
theorem edge_bound_auto (G : simple_graph V) [fintype V] [decidable_rel G.adj] [decidable_eq V]: 
  ∣∣E[G]∣∣ ≤ ∣∣(V[G])∣∣.choose 2 :=
begin 
  expand_inequality,
end