import Lean

open Lean Elab Parser Tactic

syntax "get" : tactic
syntax "set " num : tactic

#check evalTacticSeq

elab "enriched_proof" seq:tacticSeq : tactic => do
  match seq with
    | `(tacticSeq| $[$tacs]*)
    | `(tacticSeq| { $[$tacs]* }) => do
      let mut n := 0
      for tac in tacs do
        logInfo tac
        match tac with
          | `(tactic| get) =>
            logInfoAt tac m!"The current state is {n}."
          | `(tactic| set $i) =>
            n := i.getNat
          | `(tactic| $tac) => evalTactic tac
    | _ => throwUnsupportedSyntax

example : True ∧ True := by
  constructor
  · sleep 1000
    sleep 1000
    sleep 1000
    sleep 1000
    sleep 1000
    sleep 1000
    sleep 1000
    sleep 1000
    sleep 1000; save
    sleep 1000; save
    simp
  · simp


example : True := by
  enriched_proof
    let x := 5
    set 5
    have : 1 = 1 := rfl
    get
    sleep 1000
    save
    set 10
    apply False.elim
    get
    sorry
