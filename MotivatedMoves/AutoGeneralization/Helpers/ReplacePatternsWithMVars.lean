import Lean
import MotivatedMoves.AutoGeneralization.Helpers.Antiunification
import MotivatedMoves.AutoGeneralization.Helpers.Metavariables
import MotivatedMoves.AutoGeneralization.Helpers.Naming
import MotivatedMoves.AutoGeneralization.Helpers.FunctionApplications

open Lean Elab Tactic Meta Term Command AntiUnify

initialize
  registerTraceClass `TypecheckingErrors

/- Replaces all instances of `p` in `e` with a metavariable.
Roughly implemented like kabstract, with the following differences:
  kabstract replaces "p" with a bvar, while this replaces "p" with an mvar
  kabstract replaces "p" with the same bvar, while this replaces each instance with a different mvar
  kabstract doesn't look for instances of "p" in the types of constants, this does
  kabstract doesn't look under loose bvars, but this creates LocalDecls so we can still look under bvars
-/

-- NOTE (future TODO): this code can now be rewritten without `withLocalDecl` or `mkFreshExprMVarAt`
partial def replacePatternsWithMVars (e : Expr) (lctx : LocalContext) (linsts : LocalInstances) : StateT (List Expr) MetaM Expr := do
  logInfo m!"We are replacing the patterns {← get} with mvars."
  -- abstracting `p` so that it can be transported to other meta-variable contexts
  -- let pAbs ← abstractMVars p (levels := false) -- the `(levels := false)` prevents bizarre instantiations across universe levels

  -- the "depth" here is not depth of expression, but how many constants / theorems / inference rules we have unfolded
  let rec visit (e : Expr) (depth : Nat := 0): StateT (List Expr) MetaM Expr := do

    let visitChildren : Unit →  StateT (List Expr) MetaM Expr := fun _ => do
      if e.hasLooseBVars then
        logInfo m!"Loose BVars detected on expression {e}"
      match e with
      -- unify types of metavariables as soon as we get a chance in .app
      -- that is, ensure that fAbs and aAbs are in sync about their metavariables
      | .app f a         => --logInfo m!"recursing under function {f} of type {← inferType f}"
                          let fAbs ← visit f depth -- the type
                          let aAbs ← visit a depth
                          let expectedA ← extractArgType fAbs
                          let inferredA ← inferType aAbs
                          try
                            -- guard <| ← liftM <| isDefEq expectedA inferredA
                            check <| .app fAbs aAbs
                            return e.updateApp! fAbs aAbs
                          catch err =>  -- as an argument to fabs, feed in an mvar with the type it is expected to have.
                            -- trace[TypecheckingErrors] m!"Error in typechecking: {err.toMessageData}"
                            trace[TypecheckingErrors] m!"Error in typechecking: aAbs was expected to have type \n\t{← instantiateMVars expectedA} \nbut has type \n\t{← instantiateMVars =<< inferType aAbs}"

                            -- the mismatch is probably caused because something else needs to be generalized
                            let (_, conflicts) ← getTermsToGeneralize expectedA inferredA
                            let (_, problemTerms) := conflicts.unzip
                            trace[TypecheckingErrors] m!"The mismatch can probably be fixed by generalizing the terms {problemTerms}"
                            modify (fun terms ↦ (problemTerms ++ terms).eraseDups)

                            let fAbs ← visit fAbs depth
                            let aAbs ← visit aAbs depth
                            let expectedA ← extractArgType fAbs
                            let inferredA ← inferType aAbs

                            -- if this doesn't typecheck, that means probably that term has been generalized,
                            -- but type still has the pattern (or a comp rule was used).
                            -- so to fix it, we should discard the proof entirely (by making it a mvar
                            try
                              -- guard <| ← liftM <| isDefEq expectedA inferredA
                              check <| .app fAbs aAbs
                              return e.updateApp! fAbs aAbs
                            catch err =>  -- as an argument to fabs, feed in an mvar with the type it is expected to have.
                              throwError "Type-checking error after abstracting problematic terms: {err.toMessageData}"
                              -- let (result, conflicts) ← getTermsToGeneralize expectedA (← inferType aAbs)
                              -- let (positions, problemTerms) := conflicts.unzip
                              -- -- get rid of the side with the problematic term
                              -- let fAbs ← if positions.contains false then -- if the function has a problematic term
                              --   trace[TypecheckingErrors] m!"Function {fAbs} has a problematic term"
                              --   mkFreshExprMVar none (kind := .synthetic) -- TODO: Make the type of the meta-variable another meta-variable
                              -- else
                              --   pure fAbs
                              -- let aAbs ← if positions.contains true then -- if the argument has a problematic term
                              --   trace[TypecheckingErrors] m!"Argument {aAbs} has a problematic term; probl"
                              --   mkFreshExprMVar result (kind := .synthetic) -- TODO: Make the type of the meta-variable another meta-variable
                              -- else
                              --   pure aAbs
                              -- return e.updateApp! fAbs aAbs
      | .mdata _ b       => return e.updateMData! (← visit b depth)
      | .proj _ _ b      => return e.updateProj! (← visit b depth)
      | .letE n t v b _ =>  let tAbs ← visit t depth
                            let vAbs ← visit v depth
                            let updatedLet ← withLetDecl n tAbs vAbs (fun placeholder => do
                              let b := b.instantiate1 placeholder
                              let bAbs ← if (←  liftM <| withoutModifyingState (isDefEq tAbs t)) then
                                    visit b depth -- now it's safe to recurse on b (no loose bvars)
                                  else
                                    logInfo m!"tAbs {tAbs} and t {t} are not defeq"
                                    return b
                              return ← mkLetFVars #[placeholder] bAbs-- put the "n:tAbs" back in the expression itself instead of in an external fvar
                            )
                            return updatedLet
      | .lam n d b bi     =>
                              let dAbs ← visit d depth
                              --"withLocalDecl" temporarily adds "n : dAbs" to context, storing the fvar in placeholder
                              let updatedLambda ← withLocalDecl n bi dAbs (fun placeholder => do
                                let b := b.instantiate1 placeholder
                                -- logInfo m!"lamda body: {b}"
                                let bAbs ←
                                  if (←  liftM <| withoutModifyingState (isDefEq dAbs d)) then
                                    visit b depth-- now it's safe to recurse on b (no loose bvars)
                                  else
                                    logInfo m!"dAbs {dAbs} and d {d} are not defeq"
                                    return b
                                return ← mkLambdaFVars #[placeholder] bAbs (binderInfoForMVars := bi) -- put the "n:dAbs" back in the expression itself instead of in an external fvar
                              )
                              if updatedLambda.hasLooseBVars then
                                logInfo m!"Loose BVars detected on expression {e}"
                              return updatedLambda
      | .forallE n d b bi => --logInfo m!"Recursing under forall {d}"
                              let dAbs ← visit d depth
                              --"withLocalDecl" temporarily adds "n : dAbs" to context, storing the fvar in placeholder
                              let updatedForAll ← withLocalDecl n bi dAbs (fun placeholder => do
                                let b := b.instantiate1 placeholder
                                let bAbs ← visit b depth  -- now it's safe to recurse on b (no loose bvars)
                                return ← mkForallFVars #[placeholder] bAbs (binderInfoForMVars := bi) -- put the "n:dAbs" back in the expression itself instead of in an external fvar
                              )
                              return updatedForAll
      -- when we encounter a theorem used in the proof
      -- check whether that theorem has the variable we're trying to generalize
      -- if it does, generalize the theorem accordingly, and make its proof an mvar.
      | .const n us      => let constType ← inferType (.const n us) -- this ensures that univverse levels are instantiated correctly
                            -- logInfo m!"name {n}"
                            -- if marked as a theorem not to explore, do not recurse
                            -- if n.toString.endsWith "_opaque" then
                              -- logInfo m!"!!!HERE IS THE MATCH!! WILL NOT RECURSE"
                              -- return e

                            if depth ≥ 2 then return e

                            else
                                -- if (← containsExpr p constType) then
                                let genConstType ← visit constType (depth+1)  -- expr for generalized proof statment
                                -- if the const does have the pattern in its definition, it is a property we should generalize
                                -- it may be safer to just check whether the generalized type has any meta-variables at all,
                                -- rather than looking for ones of a specific type, since there's a chance of false negatives with the latter
                                if genConstType.hasExprMVar then
                                  let m ← mkFreshExprMVarAt lctx linsts genConstType (kind := .synthetic) (userName := mkAbstractedName n)-- mvar for generalized proof
                                  -- logInfo m!"made mvar {m} of type {genConstType}"
                                  return m

                                -- otherwise, we don't need to expand the definition of the const
                                else return e
      | e                => --logInfo m!"Can't recurse under this expression \n {e}"
                            return e

    if e.hasLooseBVars then
      logInfo "Loose BVars detected, so we visit children."
      visitChildren ()
    else if e.isMVar then
      return e -- handling this case separately to avoid unnecessary unification in the next case
    else
      -- if the expression "e" is the pattern you want to replace...
      let mctx ← getMCtx
      -- let (_, _, p) ← openAbstractMVarsResult pAbs
      if let .some p ← (← get).findM? (liftM <| withoutModifyingState <| isDefEq e ·) then
          -- since the type of `p` may be slightly different each time depending on the context it's in, we infer its type each time
          let m ← mkFreshExprMVarAt lctx linsts (← inferType p) (userName := placeholderName) --(kind := .syntheticOpaque) -- replace every occurrence of pattern with mvar
          -- let m ← mkFreshExprMVar (← inferType p) (userName := `n) -- replace every occurrence of pattern with mvar
          -- let m ← mkFreshExprMVar pType -- replace every occurrence of pattern with mvar
          -- logInfo m!"made mvar {m} of type {pType}"
          return m
        -- otherwise, "e" might contain the pattern...
      else
        setMCtx mctx
        -- so that other matches are still possible.
        visitChildren ()
  visit e

/- Just like kabstract, except abstracts to mvars instead of bvars
  We use this to abstract the theorem TYPE...so we can re-specialize non-abstracted occurrences in the proof.
  -/
def abstractToOneMVar (thmType : Expr) (pattern : Expr) (occs : Occurrences) : MetaM Expr := do
  let userThmType ← kabstract thmType pattern (occs)

  let userMVar ←  mkFreshExprMVar (← inferType pattern)
  let annotatedMVar := Expr.mdata {entries := [(`userSelected,.ofBool true)]} $ userMVar
  let userThmType := userThmType.instantiate1 annotatedMVar

  return userThmType

/-
  Just like kabstract, except abstracts to different variables instead of the same one
  We use this to abstract the theorem TYPE...so we can re-specialize non-abstracted occurrences in the proof.
-/
def abstractToDiffMVars (e : Expr) (p : Expr) (occs : Occurrences) : MetaM Expr := do
  let pType ← inferType p
  let pHeadIdx := p.toHeadIndex
  let pNumArgs := p.headNumArgs
  let rec visit (e : Expr) : StateRefT Nat MetaM Expr := do
    let visitChildren : Unit → StateRefT Nat MetaM Expr := fun _ => do
      match e with
      | .app f a         => return e.updateApp! (← visit f ) (← visit a )
      | .mdata _ b       => return e.updateMData! (← visit b )
      | .proj _ _ b      => return e.updateProj! (← visit b )
      | .letE _ t v b _  => return e.updateLet! (← visit t ) (← visit v ) (← visit b )
      | .lam _ d b _     => return e.updateLambdaE! (← visit d ) (← visit b )
      | .forallE _ d b _ => return e.updateForallE! (← visit d ) (← visit b )
      | e                => return e
    if e.hasLooseBVars then
      visitChildren ()
    else if e.toHeadIndex != pHeadIdx || e.headNumArgs != pNumArgs then
      visitChildren ()
    else
      -- We save the metavariable context here,
      -- so that it can be rolled back unless `occs.contains i`.
      let mctx ← getMCtx
      if (← isDefEq e p) then
        let i ← get
        set (i+1)
        if occs.contains i then
          let userMVar ← mkFreshExprMVar pType
          let annotatedMVar := Expr.mdata {entries := [(`userSelected,.ofBool true)]} $ userMVar
          return annotatedMVar
        else
          -- Revert the metavariable context,
          -- so that other matches are still possible.
          setMCtx mctx
          visitChildren ()
      else
        visitChildren ()
  visit e |>.run' 1
