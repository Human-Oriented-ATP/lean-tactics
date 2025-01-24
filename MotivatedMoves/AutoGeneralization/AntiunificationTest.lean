import MotivatedMoves.AutoGeneralization.Antiunification

open Lean Elab Meta Command Term AntiUnify

elab "#antiunify" e:term "&" e':term : command => runTermElabM fun _ ↦ do
  let e ← Term.elabTerm e none
  let e' ← Term.elabTerm e' none
  logInfo m!"{e}, {e'}"
  let (result, mismatches) ← antiUnify e e' |>.run []
  logInfo m!"Result: {result}"
  logInfo "---\nMismatches:\n---"
  for mismatch in mismatches do
    logInfo m!"Left: {mismatch.left}\nRight: {mismatch.right}"

#antiunify (((1 + 2) + 3) : Nat) & (((3 + 2) + 4) : Nat)

#antiunify ∃ n : Nat, 1 + n = 2 & ∃ n : Nat, 2 + n = 2

#antiunify λ x : Nat => x + 5 & λ x : Nat => 2

#antiunify (let n : Nat := 1 + 2; n + 5) & (let n : Nat := 1 + 3; n + 7)

#antiunify ((1 + 2) + _ : Nat) & ((_ + 2) + 3 : Nat)

#antiunify (decide (?n ≠ 2) = true) & (true = true)

#antiunify (?n + ?n : Nat) & (?n + ?m : Nat)

#antiunify (((?n : Nat) - 1) = ((?n : Nat) - 1)) & (((?n : Nat) - 1) = 3)
