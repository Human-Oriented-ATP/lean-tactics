import Lean
import MotivatedMoves.AutoGeneralization.Helpers.Antiunification

open Lean Elab Meta

initialize
  registerTraceClass `AutoGeneralization

partial def autoGeneralizeCore (term : Expr) (lctx : LocalContext) (linsts : LocalInstances)
    (depth : Nat := 0) (threshold : Nat := 2) : StateT (List Expr) MetaM Expr := do
  if depth ≥ threshold then
    trace[AutoGeneralization] m!"Threshold reached, not generalizing term of type {← inferType term}"
    return term
  else
    transform term (skipConstInApp := true) pre post
where
  pre e := do
    trace[AutoGeneralization] m!"Visiting {e}"
    if let .some pattern ← (← get).findM? (liftM <| withoutModifyingState <| isDefEq e ·) then
      trace[AutoGeneralization] m!"Found instance of pattern {pattern}"
      let m ← mkFreshExprMVarAt lctx linsts (← inferType pattern)
      return .done m
    else
      -- altering the binder types in a way that they can be modified during the traversal of the body
      match e with
      | .forallE n d b bi => do
        if !d.isMVar then do
          trace[AutoGeneralization] m!"Generalizing `.forallE` variable {n} : {d}"
          let m ← mkFreshExprMVar (← inferType d) (kind := .syntheticOpaque)
          m.mvarId!.assign (← autoGeneralizeCore d lctx linsts (depth + 1) threshold)
          withNewMCtxDepth <| return .visit <| Expr.forallE n m b bi
        else
          return .continue
      | .lam n d b bi => do
        if !d.isMVar then do
          trace[AutoGeneralization] m!"Generalizing `.lam` variable {n} : {d}"
          let m ← mkFreshExprMVar (← inferType d) (kind := .syntheticOpaque)
          m.mvarId!.assign (← autoGeneralizeCore d lctx linsts (depth + 1) threshold)
          withNewMCtxDepth <| return .visit <| Expr.lam n m b bi
        else
          return .continue
      | .letE n t v b _ => do
        if !t.isMVar then do
          trace[AutoGeneralization] m!"Generalizing `.letE` variable {n} : {t}"
          let m ← mkFreshExprMVar (← inferType t) (kind := .syntheticOpaque)
          m.mvarId!.assign (← autoGeneralizeCore t lctx linsts (depth + 1) threshold)
          withNewMCtxDepth <| return .visit <| Expr.letE n m v b false
        else
          return .continue
      | _ => return .continue
  post
  | e@(.fvar fvarId) => do
    trace[AutoGeneralization] m!"Generalizing type of free variable {← fvarId.getUserName}"
    let .mvar mvarId ← fvarId.getType | throwError m!"Expected type of free variable {← fvarId.getUserName} : {← inferType e} to be a metavariable."
    let .some type ← getExprMVarAssignment? mvarId | throwError "Expected type of free variable {← fvarId.getUserName} to be assigned."
    let genType ← autoGeneralizeCore type lctx linsts (depth + 1) threshold
    mvarId.assign genType
    return .done e
  | e@(.app f a) => do
    let .forallE _ fDomain _ bInfo ← (whnf <| ← inferType f) | throwError m!"Expected the type of {f}, {← inferType f}, to be a function type."
    if !bInfo.isExplicit && a.hasExprMVar then do -- replacing implicit and typeclass arguments with meta-variables to be synthesized later
      trace[AutoGeneralization] m!"Replacing implicit/typeclass argument of {f} with meta-variable"
      let m ← mkFreshExprMVarAt lctx linsts fDomain (kind := .synthetic)
      return ← continueWithGeneralization <| Expr.app f m
    try
      liftM <| check e
      trace[AutoGeneralization] m!"Typecheck of application succeeded"
      return ← continueWithGeneralization e
    catch _error =>
      let aType ← inferType a
      trace[AutoGeneralization] m!"Type mismatch in application: {fDomain} ≠ {aType}"
      let (_, conflicts) ← AntiUnify.getTermsToGeneralize fDomain aType
      let (_, problemTerms) := conflicts.unzip
      trace[AutoGeneralization] m!"The mismatch between {fDomain} and {aType} can probably be fixed by generalizing the terms {problemTerms}"
      modify (problemTerms ++ ·)
      return .visit e
  | e => continueWithGeneralization e
  continueWithGeneralization (e : Expr) := do
    let type ← inferType e
    let genType ← autoGeneralizeCore type lctx linsts (depth + 1) threshold
    if (← getMVars type).size < (← getMVars genType).size then -- generalization had a non-trivial effect on the term
      trace[AutoGeneralization] m!"Generalizing term of {type} to metavariable of type {genType}"
      let m ← mkFreshExprMVarAt lctx linsts genType
      return .done m
    else
      return .continue e

elab "#autogeneralize" patterns:term,* "in" stmt:ident : command => Command.runTermElabM fun _ ↦ do
  let patterns ← Array.toList <$> patterns.getElems.mapM (Term.elabTerm · none)
  let some result := (← getEnv).find? stmt.getId | throwError "No theorem of name {stmt} was found."
  let proof := result.value!
  let genProof ← autoGeneralizeCore proof (← getLCtx) (← getLocalInstances) (depth := 0) |>.run' patterns
  check genProof
  Term.synthesizeSyntheticMVarsNoPostponing
  let genThmStmt ← inferType genProof
  let genThmName :=  stmt.getId ++ `Gen
  addAndCompile <| .thmDecl {
    name := genThmName
    levelParams := result.levelParams
    type := genThmStmt
    value := genProof
  }
  logInfo m!"Generalized theorem {genThmName} : {genThmStmt}"
