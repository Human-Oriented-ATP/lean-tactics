prelude
import Init.Prelude
import Lean
import Init.Coe
import Init.Data.List.BasicAux
import Lean.Elab.Tactic
import Lean.Elab.Tactic.Basic
import Std
import Lean.Syntax

-- set_option pp.all true


open Lean Lean.Meta Lean.Expr Lean.Elab.Tactic

-- Not needed because of forallMetaTelescope
-- Like expr.get_pis, but uses mvars instead of local variables.
partial def getPiMvars : Expr → MetaM (List Expr × Expr)
| forallE _ d b _ => 
do let mv ← mkFreshExprMVar d
   let (mvs, b) ← getPiMvars (b.instantiate1 mv)
   pure (mv::mvs, b)
| e            => pure ([], e)


def print_assignments (mvs : List Expr) : MetaM Unit := do
let assigns ← List.mapM Lean.getExprMVarAssignment? (List.map mvarId! mvs)
Lean.logInfo "assignments:"
for m in mvs, val in assigns do
  let ty ← inferType m
  Lean.logInfo m!"{m} : {ty} := {val}"

-- -- returns expr and its local variables
def mkMvarAppAux (g : Expr) (ms : List Expr) (fvars : List Expr) : MetaM (Expr × List Expr) :=
match ms with
| (m::ms) => do
  let mvarid := mvarId! m
  let g ← instantiateMVars g
  forallTelescope (← inferType g) $ fun (locs : Array Expr) _ => do
  let loc := locs[0]!
  match (← mvarid.isAssigned) with
  | true => mkMvarAppAux (app g m) ms fvars
  | false => do
    let tm ← inferType m
    let tm ← instantiateMVars tm
    let tloc ← inferType loc
    _ ← isDefEq tm tloc
    m.mvarId!.assign loc
    -- let succ ← isDefEq m loc
    -- Lean.logInfo m!"{succ}"
    -- Lean.logInfo m!"m: {m} : {tm}"
    -- Lean.logInfo m!"loc: {loc} : {tloc}"
    -- print_assignments [m]
    mkMvarAppAux (app g loc) ms (loc::fvars)
| _ => do 
  let res ← instantiateMVars g
  let res ← mkLambdaFVars (List.toArray $ List.reverse fvars) res
  pure (res, [])

-- -- Given a function-type expression `f`, and a list of mvars `ms`, construct the application of `f` to `ms`
-- -- where assigned mvars are replaced by their instantiations and unassigned mvars are turned into local variables.
def mkMvarApp : Expr → List Expr → MetaM Expr :=
λ e ms => Prod.fst <$> mkMvarAppAux e ms []

-- Modus ponens in the `n`th argument of `g` using `f`.
def MpNthArg (f g : Expr) (n : Nat) : MetaM Expr := do
let tf ← inferType f
let tg ← inferType g
let (gmvs, _) ← getPiMvars tg
let (fmvs, fconc) ← getPiMvars tf
_ ← isDefEq fconc (← inferType gmvs[n]!)
let gmvs ← List.mapM (λ pair => match pair with 
| (m, i) => 
if i = n then
  do _ ← isDefEq m (mkAppN f (List.toArray (← (List.mapM instantiateMVars fmvs)))); pure m
else
  pure m 
) (List.zip gmvs (List.range $ List.length gmvs))
mkMvarApp g gmvs

/- Turn numbers in strings to lowercase indices. -/ 
def toLowerDigits (s : String) : String :=
List.foldl String.append "" $
(List.map $ (λ (c : Char) => match toString c with
| "0" => "₀"
| "1" => "₁"
| "2" => "₂"
| "3" => "₃"
| "4" => "₄"
| "5" => "₅"
| "6" => "₆"
| "7" => "₇"
| "8" => "₈"
| "9" => "₉"
| x => x
)) s.toList

/- Turn numbers in strings to lowercase indices. -/ 
def toUpperDigits (s : String) : String :=
List.foldl String.append "" $
(List.map $ (λ (c : Char) => match toString c with
| "₀" => "0"
| "₁" => "1"
| "₂" => "2"
| "₃" => "3"
| "₄" => "4"
| "₅" => "5"
| "₆" => "6"
| "₇" => "7"
| "₈" => "8"
| "₉" => "9"
| x => x
)) s.toList

def MpNthArg' (f g : Expr) (n : Nat) (index : Nat) (name : Name) (goal : MVarId) : MetaM (Nat × List MVarId) := do
goal.checkNotAssigned `MpNthArg'
goal.withContext do
  let h ← MpNthArg f g n
  -- let h ← instantiateMVars h
  if ← isDefEq (← inferType h) (← inferType g) then
    pure (index, [goal])
  else
    let (_, goal) ← goal.assertHypotheses #[⟨.str .anonymous $ name.toString ++ (toLowerDigits (toString index)), ← inferType h, h⟩]
    pure (index + 1, [goal])

def Mp (f g : Expr) (h : Option (TSyntax `ident)) : TacticM Unit := do
let mut idx := 0
for i in [: Lean.Expr.forallArity (← inferType g)] do
  let h := Option.getD (Lean.Syntax.getId <$> h) `this
  idx ← Elab.Tactic.liftMetaTacticAux (λ goal => MpNthArg' f g i idx h goal)

syntax (name := mp) &"mp" term " in " term (" with " ident)? : tactic

@[tactic mp]
def evalMp : Tactic
  | `(tactic| mp $f:term in $g:term $[ with $h:ident]?) => withMainContext do
      let f ← Elab.Term.elabTerm f none
      let g ← Elab.Term.elabTerm g none
      Mp f g h
  | _ => unreachable!

def Forward1 : TacticM Unit :=
withMainContext do
  let ctx ← getLCtx
  for f in ctx.getFVars do
    let tf ← inferType f
    if ← isProp tf then do
      for g in ctx.getFVars do
        let tg ← inferType g
        if ← isProp tg then do
          Mp f g none

elab "forward1" : tactic => Forward1

syntax (name := forward) "forward " (" depth " num)? : tactic

def Forward (n : Option (TSyntax `num)) : TacticM Unit :=
withMainContext do
  let n := Option.getD (n.map (·.getNat)) 1
  for _ in [:n] do
    Forward1

@[tactic forward]
def evalForward : Tactic
  | `(tactic| forward $[ depth $n:num]?) => Forward n
  | _ => unreachable!


def P : Nat → Nat → Prop := sorry
def Q : Nat → Nat → Nat → Prop := sorry

example (f : ∀ a, P a a) (g : ∀ a b c, P a b → P b c → Q a b c) : True := by
  -- mp h1 in h2
  -- mp f in g with h
  -- mp f in h₀ with H 
  -- forward1
  -- forward1
  forward depth 2
  trivial




