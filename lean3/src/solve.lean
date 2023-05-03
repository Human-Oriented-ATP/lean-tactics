import get_subexpressions
import testbed.graph_theory

import tactic tactic.interactive
open simple_graph expr tactic

set_option pp.implicit true
set_option pp.instantiate_mvars false

universes u
variables {V : Type u}  
--------------------  TACTIC: PUT A PARTICULAR SUBEXPRESSION ON ONE SIDE (SOLVE FOR IT) -------------------- 

-- -- solve for "x" in the expression "e"
-- -- returns the expression "x=..." as well as the proof of it
-- meta def solve_for (x : expr) (e : expr) : tactic (expr × expr)  :=
-- do {

--   -- assumes the variable is only on one side of the equation/inequality
--   -- if not, have to add a first step moving everything to one side
--   var_side   ← get_side_of_expr_with    x e,
--   other_side ← get_side_of_expr_without x e,

--   (var_side_x,var_side_const) ← is_addition var_side, 
--   -- the equation initially looked like var_side_x + var_side_const = other_side
--   -- now you want it to be var_side_x  = other_side - var_side_const
--   let new_expr := `(var_side_x = other_side - var_side_const),
--   trace new_expr,

--   -- add it to hypothesis
--   -- note new_expr proof_of_new_expr

--   return (var_side,other_side)



-- }

-- meta def mini_hammer : tactic unit :=
-- do {
--   trace "mini hammer"
-- }

-- example (G : simple_graph V) [fintype V] [decidable_rel G.adj] [decidable_eq V]: 
-- ∣∣E[G]∣∣ ≤ ∣∣(V[G])∣∣.choose 2 :=
-- begin
--   mini_hammer,
-- end 

-- #eval (solve_for `(7) `(7+3 = 10) ) >>= trace -- return 7