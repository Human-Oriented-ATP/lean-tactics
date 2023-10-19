import BFS.Move 

set_option trace.aesop true

open Lean Elab Tactic Move 

def IdentityMove : Move Unit where
  name := "Identity"
  tactic := fun _ () => pure ()
  validArguments? _ := none

def UnsoundMove : Move Unit where 
  name := "Unsound" 
  tactic := fun _ () => withMainContext do
    admitGoal (← getMainGoal) 
  validArguments? _ := some #[(#[], ())]

def SimpMove : Move Unit where 
  name := "Simp" 
  tactic := fun _ () => do 
    evalTactic (← `(tactic| simp))
  validArguments? _ := some #[(#[], ())]

@[aesop unsafe tactic (rule_sets [Move.BFS])]
def IdentityMoveBFS := IdentityMove.toBFSCapableTactic

#aesop_rules

example : True := by 
  aesop? (rule_sets [Move.BFS, -default, -builtin])
        (simp_options := {enabled := false})
  sorry -- nice! 

@[aesop unsafe tactic (rule_sets [Move.BFS])]
def UnsoundMoveBFS := UnsoundMove.toBFSCapableTactic

elab "unsoundMove" : tactic => do 
  UnsoundMoveBFS

example : False := by 
  unsoundMove

example : False := by
  aesop (rule_sets [Move.BFS, -default, -builtin])
        (options := {strategy := .breadthFirst})
        (simp_options := {enabled := false})

@[aesop unsafe tactic (rule_sets [Move.BFS])]
def SimpMoveBFS := SimpMove.toBFSCapableTactic

example : True := by 
  aesop (rule_sets [-default, -builtin])
        (options := {strategy := .breadthFirst})
        (simp_options := {enabled := false})
  sorry

example : True := by 
  aesop (rule_sets [Move.BFS, -default, -builtin])
        (options := {strategy := .breadthFirst})
        (simp_options := {enabled := false})


-- TODOs: 
-- * Make the process of adding a move nicer
-- * Make generation of tactic scripts possible
-- * Figure out how to add normalization tactics
--   without having to activate the default ones
-- => perhaps as unsafe rules? What happens to the unsafeness etc. concepts 
-- when using the BFS option? 

-- Tactics like library_search should - instead of returning multiple subgoals s1 s2 - 
-- just return s1 ∨ s2 if that's what you need to prove next. This should be immediately
-- unfolded by aesop (i.e. we would use builtin to do some elementary logic)

-- Alternative: Every move that wants to do n different thing needs to supply n tactics
-- for doing them. Might be the nicer solution 