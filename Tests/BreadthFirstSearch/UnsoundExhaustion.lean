import MotivatedMoves.BreadthFirstSearch.UnsoundExhaustion

open Lean Elab Tactic 

def myTactic (n : Nat) : TacticM Unit := do 
  match n with 
  | 0 => dbg_trace "Case 0: Error" 
         throwError "Ouch!"
  | 1 => dbg_trace "Case 1: Nothing"
         pure ()
  | 2 => dbg_trace "Case 2: Simp"
         evalTactic (← `(tactic|simp))
  | _ => dbg_trace "Case >=3: Nothing"
         pure ()

elab "testExhaust" : tactic => do 
  exhaustParametricTacticUnsound myTactic #[0, 1]

example : 1+1 = 2 := by 
  testExhaust
