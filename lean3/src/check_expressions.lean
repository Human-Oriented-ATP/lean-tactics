import get_theorems
import testbed.graph_theory
import testbed.dummy

import tactic data.real.basic
open simple_graph expr tactic

--------------------  TACTIC: CHECK WHAT TYPE OF EXPRESSION SOMETHING IS -------------------- 
meta def print_expr_type : expr →  tactic unit 
| e@(var dbi) := tactic.trace "It's a var." -- dbi is the de-Bruijn index of the variable e.g. #0
| e@(sort lev) := tactic.trace "It's a sort." -- used for types
| e@(const nm lev) := tactic.trace "It's a const." -- e.g. simple_graph.degree
| e@(mvar uniq_nm pretty_nm v) := tactic.trace "It's an mvar."
| e@(local_const uniq_nm pretty_nm bi v) := tactic.trace "It's a local const."
| e@(app f x) := do tactic.trace ("It's an app." ++ "\n \t f:"++ to_string f ++ "\n \t x:"++ to_string x)
| e@(lam nm bi d body) := tactic.trace ("It's a lam." 
                                        ++ "\n \t d:"++ to_string d 
                                        ++ "\n \t body:" ++ to_string body)
| e@(pi nm bi d body) := tactic.trace ("It's a pi." 
                                        ++ "\n \t d:"++ to_string d 
                                        ++ "\n \t body:" ++ to_string body)
| e@(elet nm v t body) := tactic.trace "It's a elet."
| e@(macro d l) := tactic.trace "It's a macro."

-- example with APP
#eval print_expr_type `(5) --in binary: 1 0 1
#eval bit1 (bit0 1)        -- the natural number 5, as stored in lean
#eval print_expr_type `(5+3) 

-- example with LAMBDA
#eval print_expr_type `(λ (n : ℕ),  nat.succ n)  

--------------------  TACTIC: CHECK IF AN EXPRESSION IS A NAT  -------------------- 
meta def is_nat (e : expr) : tactic bool := 
do {
   t ← infer_type e,
   if t = `(ℕ) then return tt else return ff
}

#eval trace (is_nat `(5)) -- tt for true
#eval trace (is_nat `(5.3 : ℝ)) -- ff for false
#eval trace (is_nat `(tt)) -- ff for false


--------------------  TACTIC: CHECK IF AN EXPRESSION CAN BE COMPARED WITH ≤ e.g. ℕ or ℝ  -------------------- 
-- for all terms, find their types (e.g. ℕ)
-- for all those types (e.g. ℕ), see if t.has_le (e.g. ℕ.has_le)
-- todo

--------------------  TACTIC: CHECK IF AN EXPRESSION BEGINS WITH A QUANTIFIER  -------------------- 

meta def begins_with_forall_quantifier (e : expr) : bool :=
  if (e.is_pi) then tt else ff

meta def begins_with_exists_quantifier (e : expr) : bool :=
  if (e.is_app_of `Exists) then tt else ff


meta def begins_with_quantifier (e : expr) : bool :=
  if begins_with_forall_quantifier e || begins_with_exists_quantifier e then tt else ff


#eval (get_thm_statement `forall_exists_greater) >>= λ e, return (begins_with_forall_quantifier e) >>= trace --tt
#eval (get_thm_statement `exists_one) >>= λ e, return (begins_with_forall_quantifier e) >>= trace -- ff

#eval (get_thm_statement `forall_exists_greater) >>= λ e, return (begins_with_exists_quantifier e) >>= trace --ff
#eval (get_thm_statement `exists_one) >>= λ e, return (begins_with_exists_quantifier e) >>= trace --tt

--------------------  TACTIC: CHECK IF AN EXPRESSION CONTAINS A PARTICULAR CONSTANT  -------------------- 

meta def contains_const (e : expr) (const_name : name) : tactic bool := 
do {
  let constants_in_e := e.list_constant,
  return (constants_in_e.contains const_name)
}

#eval (get_thm_statement `degree_sum) >>= (λ e, contains_const e ``degree) >>= trace -- tt
#eval (get_thm_statement `edge_bound) >>= (λ e, contains_const e ``degree) >>= trace -- ff

--------------------  TACTIC: CHECK IF AN EXPRESSION IS AN INEQUALITY  -------------------- 
meta def is_inequality (e : expr) :  bool := 
match e with
  | `(_ ≤  _) := tt
  | `(_ ≥ _) := tt
  | `(_ < _) := tt
  | `(_ > _) := tt
  | _        := ff
end

#eval is_inequality `(5+3)
#eval is_inequality `(3≤5)

--------------------  TACTIC: CHECK IF AN EXPRESSION IS AN INSTANCE OF ADDITION  -------------------- 
-- meta def is_addition (e : expr) : tactic bool := do {
--   match e with
--   | e@(app (app f x) y):= do {
--       let consts := f.list_constant.to_list,
--       let add := `has_add.add,
--       if (add ∈ consts) then return tt else return ff
--   }
--   | _ := return ff
--   end
-- }

-- #eval is_addition `(3+5) >>= trace -- should be tt
-- #eval is_addition `(35)  >>= trace -- should be ff
-- #eval is_addition `(3-5) >>= trace -- should be ff
-- #eval print_expr_type `(3+5)

-- if it is, return the two summands
-- if not, the tactic fails
meta def is_addition (e : expr) : tactic (expr × expr)  := do {
  match e with
  | e@(app (app f x) y):= do {
      let consts := f.list_constant.to_list,
      let add := `has_add.add,
      if (add ∈ consts) then return (x,y) else failed
  }
  | _ := failed
  end
}


#eval is_addition `(3+5) >>= trace -- should return (3,5)
#eval is_addition `(3+(5+7)) >>= trace -- should return (3,5+7)
#eval is_addition `(35)  >>= trace -- should fail
#eval is_addition `(3-5) >>= trace -- should fail
#eval print_expr_type `(3+5)

