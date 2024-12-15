import MotivatedMoves.AutoGeneralization.Antiunification

open Lean Elab Meta Command Term AntiUnify

elab "#antiunify" e:term "&" e':term : command => runTermElabM fun _ ↦ do
  let e ← Term.elabTerm e none
  let e' ← Term.elabTerm e' none
  let result ← leastCommonGeneralizer e e'
  logInfo m!"{e}, {e'}\nResult: {result}"

#antiunify (((1 + 2) + 3) : Nat) & (((3 + 2) + 4) : Nat)
