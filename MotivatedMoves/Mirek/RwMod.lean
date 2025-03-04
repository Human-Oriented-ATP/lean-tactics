import Mathlib

example (a b : ℕ) : a+b = b+a := by exact Nat.add_comm a b

open Lean Meta Elab Tactic Qq

namespace ModRw

def Rewriter (n e : Q(ℤ)): Type :=
  MetaM (Option (Σ re : Q(ℤ), Q($e ≡ $re [ZMOD $n])))

partial
def rwInt
    (n : Q(ℤ))
    (rwRoot : ∀ e, Rewriter n e)
    (e : Q(ℤ))
    : Rewriter n e := do
  match ← rwRoot e with
  | some x => return x
  | none =>
    match e with
    | ~q($a + $b) =>
      match (← rwInt n rwRoot a, ← rwInt n rwRoot b) with
      | (some ⟨ar, apf⟩, some ⟨br, bpf⟩) =>
        return some ⟨q($ar + $br), q(Int.ModEq.add $apf $bpf)⟩
      | (some ⟨ar, apf⟩, none) =>
        return some ⟨q($ar + $b), q(Int.ModEq.add_right $b $apf)⟩
      | (none, some ⟨br, bpf⟩) =>
        return some ⟨q($a + $br), q(Int.ModEq.add_left $a $bpf)⟩
      | (none, none) => return none
    | ~q($a - $b) =>
      match (← rwInt n rwRoot a, ← rwInt n rwRoot b) with
      | (some ⟨ar, apf⟩, some ⟨br, bpf⟩) =>
        return some ⟨q($ar - $br), q(Int.ModEq.sub $apf $bpf)⟩
      | (some ⟨ar, apf⟩, none) =>
        return some ⟨q($ar - $b), q(Int.ModEq.sub_right $b $apf)⟩
      | (none, some ⟨br, bpf⟩) =>
        return some ⟨q($a - $br), q(Int.ModEq.sub_left $a $bpf)⟩
      | (none, none) => return none
    | ~q($a * $b) =>
      match (← rwInt n rwRoot a, ← rwInt n rwRoot b) with
      | (some ⟨ar, apf⟩, some ⟨br, bpf⟩) =>
        return some ⟨q($ar * $br), q(Int.ModEq.mul $apf $bpf)⟩
      | (some ⟨ar, apf⟩, none) =>
        return some ⟨q($ar * $b), q(Int.ModEq.mul_right $b $apf)⟩
      | (none, some ⟨br, bpf⟩) =>
        return some ⟨q($a * $br), q(Int.ModEq.mul_left $a $bpf)⟩
      | (none, none) => return none
    | ~q($a ^ $b) =>
      match ← rwInt n rwRoot a with
      | (some ⟨ar, apf⟩) =>
        return some ⟨q($ar ^ $b), q(Int.ModEq.pow $b $apf)⟩
      | none =>
        return none
    | _ => return none

def rwZModEq (n a b : Q(ℤ))
    (rwRoot : ∀ e, Rewriter n e) :
    MetaM (Option (Σ eq2 : Q(Prop), Q(($a ≡ $b [ZMOD $n]) = $eq2))) := do
  match (← rwInt n rwRoot a, ← rwInt n rwRoot b) with
  | (some ⟨ar, apf⟩, some ⟨br, bpf⟩) =>
    return some ⟨q($ar ≡ $br [ZMOD $n]), q(propext <| Eq.congr $apf $bpf)⟩
  | (some ⟨ar, apf⟩, none) =>
    return some ⟨q($ar ≡ $b [ZMOD $n]), q(propext <| Eq.congr_left $apf)⟩
  | (none, some ⟨br, bpf⟩) =>
    return some ⟨q($a ≡ $br [ZMOD $n]), q(propext <| Eq.congr_right $bpf)⟩
  | (none, none) =>
    return none

def rwRootBasic (n₀ a₀ b₀ : Q(ℤ)) (pf : Q($a₀ ≡ $b₀ [ZMOD $n₀]))
    (n a : Q(ℤ)) : MetaM <| Option  <| Σ b : Q(ℤ), Q($a ≡ $b [ZMOD $n₀])
    := do
    if n == n₀ ∧ a == a₀ then
      return some ⟨b₀, pf⟩
    else
      return none

def rwRootAdvanced (n e : Q(ℤ)) (eqn : Expr) : Rewriter n e := do
  let thm ← inferType eqn -- the statement that `eqn` proves
  let (mvars, _, body) ← forallMetaTelescope thm -- the body of the statement
  let ⟨1, ~q(Prop), ~q($lhs ≡ $rhs [ZMOD $n])⟩ ← inferTypeQ body | throwError "Expected the equation to be of the form lhs ≡ rhs [ZMOD $mod]"
  match ← isDefEqQ (u := 1) lhs n with
  | .defEq _ =>
    let mvars ← mvars.mapM instantiateMVars
    -- the universally quantified variables that remain uninstantiated by unification
    let sideGoals ← mvars.filterMapM fun mvar => do
      if let .mvar mvarId := mvar then
        pure <| some mvarId
      else
        pure none
    -- this needs `TacticM` to work
    -- appendGoals sideGoals.toList
    return some ⟨rhs, mkAppN eqn mvars⟩
  | .notDefEq => return none

def rwTopStep
  (rw_root : ∀ n e : Q(ℤ), MetaM (Option (Σ re : Q(ℤ), Q($e ≡ $re [ZMOD $n]))))
  : Simp.Simproc := fun e => do
  let e_whnf ← whnfR e
  if let some (n,a,b) := e_whnf.app3? `Int.ModEq then
    match ← rwZModEq n a b (rw_root n) with
    | some ⟨eq2, pf⟩ => return Simp.Step.done { expr := eq2, proof? := pf }
    | none => return Simp.Step.done { expr := e, proof? := none }
  else
    return Simp.Step.continue

def SimpConfig : Simp.Config where
  zeta := false
  proj := false

#print Simp.Simproc

def rwTop
  (rwRoot : ∀ n e : Q(ℤ), MetaM (Option (Σ re : Q(ℤ), Q($e ≡ $re [ZMOD $n]))))
  (tgt : Expr)
  : MetaM Simp.Result := do
  let ctx : Simp.Context ← Simp.mkContext SimpConfig
      (simpTheorems := #[])
      (congrTheorems := ← getSimpCongrTheorems)
  let methods := { pre := rwTopStep rwRoot }
  (·.1) <$> Simp.main tgt ctx (methods := methods)

def rwModTarget (rwRoot : ∀ n e, Rewriter n e) :
    TacticM Unit := do
  let mvarId ← getMainGoal
  let tgt ← instantiateMVars (← mvarId.getType)
  let mvarIdNew ← applySimpResultToTarget mvarId tgt (← rwTop rwRoot tgt)
  if mvarIdNew == mvarId then throwError "push made no progress"
  replaceMainGoal [mvarIdNew]

def rwModLocalDecl (rwRoot : ∀ n e, Rewriter n e) (fvarId : FVarId) :
    TacticM Unit := do
  let ldecl ← fvarId.getDecl
  if ldecl.isAuxDecl then return
  let tgt ← instantiateMVars ldecl.type
  let mvarId ← getMainGoal
  let result ← rwTop rwRoot tgt
  let some (_, mvarIdNew) ← applySimpResultToLocalDecl mvarId fvarId result False | failure
  if mvarIdNew == mvarId then throwError "push made no progress"
  replaceMainGoal [mvarIdNew]

elab "rw_mod " t:term : tactic =>
  withMainContext do
    let pf ← elabTerm t none
    let t ← inferType pf
    match t.app3? `Int.ModEq with
    | some (n,a,b) =>
      let rwRoot := rwRootBasic n a b pf
      rwModTarget rwRoot
    | none => throwError "mod_rw must be provided with a proof of a statement of the form a ≡ b [ZMOD n]"

elab "rw_mod " t:term " at " i:ident : tactic =>
  withMainContext do
    let pf ← elabTerm t none
    let t ← inferType pf
    match t.app3? `Int.ModEq with
    | some (n,a,b) =>
      let rwRoot := rwRootBasic n a b pf
      let fvarId ← getFVarId i
      rwModLocalDecl rwRoot fvarId
    | none => throwError "mod_rw must be provided with a proof of a statement of the form a ≡ b [ZMOD n]"

example (a b c d n : ℤ) (h : b + c * d ≡ d + b * b [ZMOD n])
(eq : a ≡ b [ZMOD n])
: a + c * d ≡ d + a * a [ZMOD n]
:= by
  rw_mod eq
  rw_mod h
  rfl

example (a b c d n : ℤ) (h : b + c * d ≡ d + b * b [ZMOD n])
(eq : a ≡ b [ZMOD n])
: a + c * d ≡ d + a * a [ZMOD n]
:= by
  rw_mod eq.symm at h
  exact h

end ModRw
