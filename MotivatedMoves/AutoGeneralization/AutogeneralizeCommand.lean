import Lean
import MotivatedMoves.AutoGeneralization.Helpers.Antiunification

open Lean Elab Meta

partial def autoGeneralizeCore (term : Expr) (lctx : LocalContext) (linsts : LocalInstances) : StateT (List Expr) MetaM Expr := do
  transform term (skipConstInApp := true) pre post
where
  pre e := do
    if let .some pattern ← (← get).findM? (liftM <| withoutModifyingState <| isDefEq e ·) then
      let m ← mkFreshExprMVarAt lctx linsts (← inferType pattern)
      return .continue m
    else
      -- altering the binder types in a way that they can be modified during the traversal of the body
      match e with
      | .forallE n d b bi => do
        let m ← mkFreshExprMVar (← inferType d) (kind := .syntheticOpaque)
        m.mvarId!.assign d
        return .continue <| Expr.forallE n m b bi
      | .lam n d b bi => do
        let m ← mkFreshExprMVar (← inferType d) (kind := .syntheticOpaque)
        m.mvarId!.assign d
        return .continue <| Expr.lam n m b bi
      | .letE n t v b _ => do
        let m ← mkFreshExprMVar (← inferType t) (kind := .syntheticOpaque)
        m.mvarId!.assign t
        return .continue <| Expr.letE n m v b false
      | _ => return .continue
  post
  | e@(.fvar fvarId) => do
    let type@(.mvar mvarId) ← inferType e | throwError m!"Expected type of free variable {fvarId.name} : {← inferType e} to be a metavariable."
    let type ← instantiateMVars type
    let genType ← autoGeneralizeCore type lctx linsts
    mvarId.assign genType
    return .continue
  | e@(.app f a) => do
    let .forallE _ fDomain _ bInfo ← (whnf <| ← inferType f) | throwError m!"Expected the type of {f}, {← inferType f}, to be a function type."
    if !bInfo.isExplicit && a.hasExprMVar then do -- replacing implicit and typeclass arguments with meta-variables to be synthesized later
      let m ← mkFreshExprMVarAt lctx linsts fDomain (kind := .synthetic)
      return ← continueWithGeneralization <| Expr.app f m
    try
      liftM <| check e
      return ← continueWithGeneralization e
    catch _error =>
      let aType ← inferType a
      let (_, conflicts) ← AntiUnify.getTermsToGeneralize fDomain aType
      let (_, problemTerms) := conflicts.unzip
      trace[AntiUnify] m!"The mismatch between {fDomain} and {aType} can probably be fixed by generalizing the terms {problemTerms}"
      modify (problemTerms ++ ·)
      return .visit e
  | e => continueWithGeneralization e
  continueWithGeneralization (e : Expr) := do
    let type ← inferType e
    let genType ← autoGeneralizeCore type lctx linsts
    if (← getMVars type).size < (← getMVars genType).size then -- generalization had a non-trivial effect on the term
      let m ← mkFreshExprMVarAt lctx linsts genType
      return .continue m
    else
      return .continue e

elab "#autogeneralize" patterns:term,* "in" stmt:ident : command => Command.runTermElabM fun _ ↦ do
  let patterns ← Array.toList <$> patterns.getElems.mapM (Term.elabTerm · none)
  let some result := (← getEnv).find? stmt.getId | throwError "No theorem of name {stmt} was found."
  let proof := result.value!
  let genProof ← autoGeneralizeCore proof (← getLCtx) (← getLocalInstances) |>.run' patterns
  check genProof
  let genThmStmt ← inferType genProof
  let genThmName :=  stmt.getId ++ `Gen
  addAndCompile <| .thmDecl {
    name := genThmName
    levelParams := result.levelParams
    type := genThmStmt
    value := genProof
  }
  logInfo m!"Generalized theorem {genThmName} : {genThmStmt}"
