import tactic
import init.meta.expr
import init.meta.lean.parser

open tactic expr

-- Like expr.get_pis, but uses mvars instead of local variables.
meta def get_pi_mvars : expr → tactic (list expr × expr)
| (pi n bi d b)  :=
do mv ← mk_meta_var d,
   (mvs, b) ← get_pi_mvars (b.instantiate_var mv),
   pure (mv::mvs, b)
| e              := pure ([], e)

-- returns expr and its local variables
meta def mk_mvar_app_aux : expr → list expr → list expr → tactic (expr × list expr)
| g (m::ms) local_vars := do
  g ← instantiate_mvars g,
  (loc::locs, _) ← infer_type g >>= mk_local_pis,
  assigned ← is_assigned m,
  match assigned with
  | tt := mk_mvar_app_aux (app g m) ms local_vars
  | ff := do
    tm ← infer_type m,
    tm ← instantiate_mvars tm,
    tloc ← infer_type loc,
    unify tm tloc,
    unify m loc,
    mk_mvar_app_aux (app g loc) ms (loc::local_vars)
  end
| g [] local_vars := pure (g, list.reverse local_vars)

-- Given a function-type expression `f`, and a list of mvars `ms`, construct the application of `f` to `ms`
-- where assigned mvars are replaced by their instantiations and unassigned mvars are turned into local variables.
meta def mk_mvar_app : expr → list expr → tactic (expr × list expr) :=
λ e ms, mk_mvar_app_aux e ms []

-- Modus ponens in the `n`th argument of `f` usinf `g`.
meta def mp_nth_arg (f g : expr) (n : ℕ) : tactic expr :=
do tf ← infer_type f,
  tg ← infer_type g,
  (gmvs, gconc) ← get_pi_mvars tg,
  gtys ← mmap infer_type gmvs,
  let replace : list bool := list.map (= n) $ list.range (list.length gtys),
  match list.nth gtys n with
  | some t := do
    (fmvs, fconc) ← get_pi_mvars tf,
    unify fconc t,
    gmvs ← mmap (λ a, match a with
    | (m, tt) := do (app_of_list f <$> (mmap instantiate_mvars fmvs)) >>= unify m, pure m
    | (m, ff) := pure m    
    end
    ) (list.zip gmvs replace),
    (res, locs) ← mk_mvar_app g gmvs,
    res ← instantiate_mvars res,  
    pure $ expr.lambdas locs res 
   | none := failed
   end

/- Apply modus ponens once in each argument in which it is possible, returning a list consisting of the results
   if possible and none otherwise. -/
meta def mp_core (f g : expr) : tactic (list (option expr)) :=
do tg ← infer_type g,
  let n := pi_arity tg,
  mmap (λ k, try_core $ mp_nth_arg f g k) (list.range n)

def option_list_to_list {α : Type*} (l : list (option α)) : list α :=
list.foldl list.append [] (list.map option.to_list l)

/- Apply modus ponens once in each argument in which it is possible, returning the list of results. -/
meta def mp_core' (f g : expr) : tactic (list expr) :=
option_list_to_list <$> mp_core f g


/- Define the interactive `mp` tactic-/

open interactive
open lean.parser (ident tk)

/- Turn numbers in strings to lowercase indices. -/ 
meta def to_lower_digits (s : string) : string :=
list.foldl (++) "" $
(list.map $ (λ (c : char), match to_string c with
| "0" := "₀"
| "1" := "₁"
| "2" := "₂"
| "3" := "₃"
| "4" := "₄"
| "5" := "₅"
| "6" := "₆"
| "7" := "₇"
| "8" := "₈"
| "9" := "₉"
| x := x
end
)) s.to_list

/- Apply the local hyposthesis `f` to an argument (assumption) of `g`, and add the resulting statements to the 
   context, optionally using the name `nm` for the new hypotheses. If there are several possibilities, do it
   for each possibility once and add subscripts to the new hypothesis names. -/
meta def tactic.interactive.mp (f g : parse ident) 
(nm : parse (optional (tk "with" *> ident))) 
: tactic unit :=
-- Note: switched order w.r.t. to `mp_core`
let nm := nm.get_or_else `this in
do f ← get_local f,
  g ← get_local g,
  hs ← mp_core' g f,
  let num_new_hyps := list.length hs,
  let inds := list.range num_new_hyps,

  mmap ( λ (hi : expr × nat) , 
    match hi with
    | (h, i) := do
      let nm_i :=  mk_simple_name $ (name.to_string nm) ++ (to_lower_digits $ to_string i),
      let nm' := if num_new_hyps = 1 then nm else nm_i,
      interactive.have nm' none ``(%%h)
    end
  ) (list.zip hs inds),
  pure ()



/-- EXAMPLE -/

def P : ℕ → ℕ → Prop := sorry
def Q : ℕ → ℕ → ℕ → Prop := sorry


example (f : ∀ a, P a a) (g : ∀ a b c, P a b → P b c → Q a b c) (g' : ∀ a b, P a b → Q a a b): true :=
begin
  mp g f with H,        -- give the new hypotheses names starting with `H`
  mp g f,               -- use `this` instead
  mp g' f,              -- no indices if there is only one possibility
  mp H₀ f with HH₀,     -- can be applied multiple times
  mp H₁ f with HH₁,
  trivial
end

def PP : Prop := sorry
def QQ : Prop := sorry


/- The argument order was chosen such that `mp g f` is like `g(f)` or `g ∘ f` (but that can be changed). -/ 
example (f : PP) (g : PP → QQ) : QQ := by mp g f; assumption

