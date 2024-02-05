import MotivatedMoves.Mirek.ProofMode

theorem T : ∃ x, x < x + 1 := by
  constructor
  start_proof -- this pushes the current proof state (note, it doesn't work in `example`)

## -- cursor here to see proof state
## refine Nat.lt_succ_self ?_ -- you can write a tactic or tactic block here
## exact 1 -- when the goal is finished, it pops the proof state and reports "Goals accomplished 🎉"

#print T
