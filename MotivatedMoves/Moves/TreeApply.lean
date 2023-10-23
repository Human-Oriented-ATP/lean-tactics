import MotivatedMoves.LibrarySearch.LibrarySearch

namespace Tree

open Lean Meta


/-

In this file, we define the infrastructure for using one subexpression to work on another subexpression. This is used for applying and rewriting.
We can also use a general (library) result to work in a subexpression.

The main definitions are
· unfoldHypothesis, which is a recursive function that runs an inner MetaM' monad, and it 
-/
inductive HypBinder where
| meta (mvarId : MVarId) (type : Expr) : HypBinder
| free (fvarId : FVarId) (name : Name) (u : Level) (type definition : Expr) : HypBinder
| unknown (fvar : FVarId) (type : Expr) : HypBinder
| known (definition : Expr) (type : Expr) : HypBinder

instance : ToString HypBinder where
  toString := fun
    | .meta ⟨id⟩ .. => ".meta " ++ toString id
    | .free ⟨id⟩ .. => ".free " ++ toString id
    | .unknown ⟨id⟩ .. => ".unknown " ++ toString id
    | .known .. => ".known "

def mkMetaHypBinder (mvarId : MVarId) : MetaM HypBinder := do
  return .meta mvarId (← instantiateMVars (← mvarId.getType))

structure MvarInfo where
  name : Name
  u : Level

structure HypBinderState where
  binders : Array HypBinder := #[]
  boundMVars : HashSet MVarId := {}
  mvarInfos : HashMap MVarId MvarInfo := {}

abbrev MetaM' := StateRefT HypBinderState MetaM

def bindMeta (mvarId : MVarId) (type : Expr) (pol : Bool) (tree : Expr) (treeProof : TreeProof) : MetaM' TreeProof := do
  match (← get).mvarInfos.find? mvarId with
  | some {name, u} => bindMVar mvarId type name u pol tree treeProof
  | none =>
    let name ← mkFreshUserName `m -- in the future make a more sophisticated name generator
    let u ← getLevel type
    bindMVar mvarId type name u pol tree treeProof


def revertHypBinder (pol : Bool) (tree : Expr) : HypBinder →  TreeProof → MetaM' TreeProof
| .meta mvar type => bindMeta mvar type pol tree
| .free fvar name u type definition => (bindFVar fvar name u type definition pol tree ·)
| .unknown fvar type     => (return bindUnknown type (.fvar fvar) pol tree ·)
| .known definition type => (return bindKnown type definition pol tree ·)

namespace CollectMFVars

structure State where
  visitedExpr  : ExprSet      := {}
  MVarIds       : Array MVarId := {}
  FVarIds       : Array FVarId := {}

def State.toCollectMVarsState : State → CollectMVars.State := fun {visitedExpr, MVarIds ..} => {visitedExpr, result := MVarIds}

instance : Inhabited State := ⟨{}⟩

abbrev Visitor := State → State

mutual
  partial def visit (e : Expr) : Visitor := fun s =>
    if !(e.hasMVar || e.hasFVar) || s.visitedExpr.contains e then s
    else main e { s with visitedExpr := s.visitedExpr.insert e }

  partial def main : Expr → Visitor
    | Expr.proj _ _ e      => visit e
    | Expr.forallE _ d b _ => visit b ∘ visit d
    | Expr.lam _ d b _     => visit b ∘ visit d
    | Expr.letE _ t v b _  => visit b ∘ visit v ∘ visit t
    | Expr.app f a         => visit a ∘ visit f
    | Expr.mdata _ b       => visit b
    | Expr.mvar mvarId     => fun s => { s with MVarIds := s.MVarIds.push mvarId }
    | Expr.fvar fvarId     => fun s => { s with FVarIds := s.FVarIds.push fvarId }
    | _                    => id
end

end CollectMFVars

/-- collect the metavariables and free variables in an expression, given a previous CollectMFVars.State. -/
def _root_.Lean.Expr.collectMFVars (s : CollectMFVars.State) (e : Expr) : CollectMFVars.State :=
  CollectMFVars.visit e s


private inductive TakeHypBinderState where
| none
| only_mvar
| fvar_or_known

def takeMVarHypBinders (startState : CollectMVars.State) (binders : Array HypBinder) (pol : Bool) (tree : Expr) : (TreeProof → MetaM' TreeProof) × Array HypBinder :=
  (binders.foldl (init := fun _ => (pure, #[])) fun f binder s =>
    match binder with
    | .meta mvar (type := type) .. =>
      let isUsed := s.result.contains mvar
      let s := if isUsed then type.collectMVars s else s
      push binder isUsed (f s)

    | .free ..
    | .unknown ..
    | .known .. => push binder false (f s)
    ) startState
where
  push (binder : HypBinder) (isUsed : Bool) : ((TreeProof → MetaM' TreeProof) × Array HypBinder) → ((TreeProof → MetaM' TreeProof) × Array HypBinder)
    := fun (kleisli, binders) => if isUsed then (kleisli <=< revertHypBinder pol tree binder, binders) else (kleisli, binders.push binder)



/-
This funtion is not perfect and should be improved to improve the safety of the algorithm.

When we bind a metavariable in front of a target, we want to bind all free variables and knowns from the hypothesis binders in front of that.
When one such binder is bound, all binders before it must also be bound.
In addition, we must bind all metavariables from the hypothesis that we have a dependency on. This we keep track of with a HashSet MVarId

However, if the hypothesis is not in scope, we are not allowed to use free or known binders, so we only take the required meta binders.
-/

def takeHypBinders (nonHypMVar? : Bool) (startState : CollectMFVars.State) (binders : Array HypBinder) (pol : Bool) (tree : Expr) : (TreeProof → MetaM' TreeProof) × Array HypBinder :=
  (binders.foldl (init := fun _ (_ : TakeHypBinderState) => (pure, #[])) fun f binder s takeHypBinderState =>
    match binder, takeHypBinderState with
    | .unknown .., .fvar_or_known
    | .meta    .., .fvar_or_known => bind binder (f s takeHypBinderState)

    | .meta mvar (type := type), _ =>
      if s.MVarIds.contains mvar then
        let s := type.collectMFVars s
        bind binder (f s .only_mvar)
      else
        push binder (f s takeHypBinderState)

    | .free fvar .., .none =>
      if s.FVarIds.contains fvar then
        bind binder (f s .fvar_or_known)
      else
        push binder (f s takeHypBinderState)
    | .unknown .., _
    | .known   .., .none => push binder (f s takeHypBinderState)

    | .free    .., _
    | .known   .., _ => bind binder (f s .fvar_or_known)
    ) startState (if nonHypMVar? then .only_mvar else .none)
where
  push (binder : HypBinder): ((TreeProof → MetaM' TreeProof) × Array HypBinder) → ((TreeProof → MetaM' TreeProof) × Array HypBinder)
    := Bifunctor.snd (·.push binder)
  bind (binder : HypBinder): ((TreeProof → MetaM' TreeProof) × Array HypBinder) → ((TreeProof → MetaM' TreeProof) × Array HypBinder)
    := Bifunctor.fst (· <=< revertHypBinder pol tree binder)





structure HypothesisContext where
  hypProofM : MetaM' (Expr × Expr)
  metaIntro : MetaM (Array Expr) := pure #[]
  instMetaIntro : MetaM (Array Expr) := pure #[]


def HypothesisRec [Monad m] [MonadControlT MetaM m] [MonadNameGenerator m] : TreeRecursor (ReaderT HypothesisContext m) α where
  inst _n _u cls _pol _tree k := do
    let mvarId ← mkFreshMVarId
    let mvar := .mvar mvarId
    withReader (fun c => { c with
      instMetaIntro := return (← c.instMetaIntro).push (← mkFreshExprMVarWithId mvarId cls (kind := .synthetic))
      hypProofM := do
        let (instance_pattern _n _u _domain tree, hypProof) ← c.hypProofM | panic! ""
        -- sometimes the metavariable assignment is not eta-reduced, but it should be.
        let assignment := Expr.eta (← instantiateMVars mvar)
        
        let newMVars := ((assignment.collectMVars {}).result).filter (!(← get).boundMVars.contains ·)
        let newBinders ← liftMetaM <| newMVars.mapM mkMetaHypBinder
        modify fun s => { s with
          boundMVars := s.boundMVars.insertMany newMVars
          binders := s.binders ++ newBinders
          }

        return ((tree.instantiate1 mvar).replace1Beta mvar assignment, .app hypProof assignment)
    }) do
    k mvar
  all name _u domain _pol _tree k := do
    let mvarId ← mkFreshMVarId
    let mvar := .mvar mvarId
    withReader (fun c => { c with
      metaIntro := return (← c.metaIntro).push (← mkFreshExprMVarWithId mvarId domain (kind := .natural) (userName := name))
      hypProofM := do
        let (forall_pattern name u _domain tree, hypProof) ← c.hypProofM | panic! ""
        let assignment := Expr.eta (← instantiateMVars mvar)

        if let .mvar mvarId' := assignment then
          modify fun s => let (mvarInfos, duplicate) := s.mvarInfos.insert' mvarId' {name, u}; if duplicate then s else { s with mvarInfos }

        let newMVars := ((assignment.collectMVars {}).result).filter (!(← get).boundMVars.contains ·)
        let newBinders ← liftMetaM <| newMVars.mapM mkMetaHypBinder
        modify fun s => { s with
          boundMVars := s.boundMVars.insertMany newMVars
          binders := s.binders ++ newBinders
          }
        return ((tree.instantiate1 mvar).replace1Beta mvar assignment, .app hypProof assignment)
      }) do
    k mvar
    

  ex name _u domain _pol _tree k := do
    withLocalDeclD name domain fun fvar => do
    let fvarId := fvar.fvarId!
    withReader (fun c => { c with
      hypProofM := do
        let (exists_pattern name u domain tree, hypProof) ← c.hypProofM | panic! ""
        let lamTree := .lam name domain tree .default
        addBinder (.free fvarId name u domain (mkApp3 (.const ``Classical.choose [u]) domain lamTree hypProof))
        return (tree.instantiate1 fvar, mkApp3 (.const ``Classical.choose_spec [u]) domain lamTree hypProof)
    }) do
    k fvar
    

  imp_right p _pol _tree k := do
    withLocalDeclD `unknown p fun fvar => do
    let fvarId := fvar.fvarId!
    withReader (fun c => { c with
      hypProofM := do
        let (imp_pattern p tree, hypProof) ← c.hypProofM | panic! ""
        addBinder (.unknown fvarId p)
        return (tree, .app hypProof fvar)
    }) do
    k

  and_right _p _pol _tree k := do
    withReader (fun c => { c with
      hypProofM := do
        let (and_pattern p tree, hypProof) ← c.hypProofM | panic! ""
        addBinder (.known (.proj `And 0 hypProof) p)
        return (tree, .proj `And 1 hypProof)
    }) do
    k
    
  and_left _p _pol _tree k := do
    withReader (fun c => { c with
      hypProofM := do
        let (and_pattern tree p, hypProof) ← c.hypProofM | panic! ""
        addBinder (.known (.proj `And 1 hypProof) p)
        return (tree, .proj `And 0 hypProof)
    }) do
    k
    
  imp_left _ _ _ _ := failure
  not _ _ _ := failure

where
  addBinder (hypBinder : HypBinder) : MetaM' Unit := do
    modify fun s => { s with binders := s.binders.push hypBinder }

/- 
Run the inner MetaM' monad on the inner hypothesis-tree, and the remaining tree position, and the HypothesisContext.
unfoldHypothesis adds free variables into the context for the Exists and Imp binders in the hypothesis-tree,
and the metavariables for Forall and Instance binders are stored in the HypothesisContext. They will be added to the
MetaM context later, so that all available free variables will be in their context.
-/
def _root_.unfoldHypothesis [Monad m] [MonadControlT MetaM m] [MonadNameGenerator m] [MonadError (ReaderT HypothesisContext m)] [Inhabited α]
    (hypProof : Expr) (tree : Expr) (pos : TreePos) (k : Expr → TreePos → ReaderT HypothesisContext m α) : m α :=
  HypothesisRec.recurse true tree pos (fun _pol tree pos => k tree pos) |>.run {hypProofM := pure (tree, hypProof)}




def getHypothesisRec (wantedPol : Bool) : TreeRecursor CoreM (TreeHyp × Expr × TreePos) where
  all _ _ _ _ _ _   := failure
  ex _ _ _ _ _ _    := failure
  inst _ _ _ _ _ _  := failure
  not _ _ _         := failure
  imp_right p pol tree k := do if wantedPol == pol then failure else return Bifunctor.fst (ImpRightWithHyp p pol tree) (← k)
  imp_left  p pol tree k := do if wantedPol == pol then failure else return Bifunctor.fst (ImpLeftWithHyp  p pol tree) (← k)
  and_right p pol tree k := do if wantedPol != pol then failure else return Bifunctor.fst (AndRightWithHyp p pol tree) (← k)
  and_left  p pol tree k := do if wantedPol != pol then failure else return Bifunctor.fst (AndLeftWithHyp  p pol tree) (← k)

/-
getHypothesis returns TreeHyp, which contains a proof and the type of the hypothesis,
and the replacement tree (since we may delete the hypothesis from the tree), and the remaining tree position in the hypothesis.
For example, if the state is `p ⇨ q ⇨ r` and we want to use `q` in `p`, then the replacement tree replacing `q ⇨ r` will be `r`.
We also return the subexpression position within `q` that the original position pointed to withing `q ⇨ r`
-/
def getHypothesis (delete? wantedPol pol : Bool) (tree : Expr) (pos : TreePos) : CoreM $ TreeHyp × Expr × TreePos :=
  (getHypothesisRec wantedPol).recurse pol tree pos fun pol tree pos => pure (MakeHyp delete? pol tree, tree, pos)




/-
TreeRecMeta does the recursion to the position of the target.
The nested MetaM' inside MetaM' may seem redundant, but it is very important,
since the outer action is fully run before the inner one can be reached.
The outer monad is used to introduce the relevant variables in the context, and do the isDefEq application.
The inner monad is used to build the TreeProof. For this, we need to decide which binders from the hypothesis, and which metavariables are bound where.
Note that during isDefEq, new metavariables may be created, and we need to account for all of them.
For this, we have the state in the MetaM' monad.

When we have an Exists binder in positive polarity or Forall binder in negative polarity, this variable is introduced as a metavariable (in the outer monad).
Then in the inner monad, we close this binder using the instantiation of this metavariable.
in front of this, we have to bind all variables that appear in this instantiation.
In addition, we want all free variables and knowns from the hypothesis to be bound whenever a 
side goal or existential is bound in positive polarity, because it may be useful for proving that goal or instantiating that variable.
-/
@[reducible] def M := ReaderT (MetaM' (TreeProof → MetaM' TreeProof)) MetaM'

def TreeRecMeta (hypInScope saveClosed : Bool) : TreeRecursor M TreeProof where
  imp_right := introProp true  false bindImpRight
  imp_left  := introProp true  true  bindImpLeft
  and_right := introProp false false bindAndRight
  and_left  := introProp false true  bindAndLeft
  not pol tree k := Functor.map (f := M) some <| withReader (Functor.map (· ∘ bindNot pol tree)) k

  all name u domain pol :=
    if pol
    then
      introFree name u domain pol bindForall
    else 
      introMeta name u domain pol

  ex name u domain pol := 
    if pol 
    then
      introMeta name u domain pol
    else
      introFree name u domain pol bindExists
  
  inst n u cls pol :=
    introFree n u cls pol bindInstance

where
  introProp (isImp isRev : Bool) (bind : Bool → Expr → Bool → Expr → TreeProof → TreeProof) (p : Expr) (pol : Bool) (tree : Expr) (k : M TreeProof) : OptionT M TreeProof :=
    Functor.map (f := M) some <|
    Function.swap withReader k (if hypInScope && (pol != (isImp && !isRev))
      then
        fun k => do
        let kleiski ← k
        let tree' := (if isRev then Function.swap else id) (mkApp2 (.const (if isImp then ``Imp else ``Tree.And) [])) p tree
        let {binders ..} ← get
        let (bindHyp, binders) := takeHypBinders true {} binders pol tree'
        modify fun s => { s with binders }
        return kleiski <=< bindHyp ∘ bind saveClosed p pol tree
      else
        Functor.map (· ∘ bind saveClosed p pol tree))

  introFree (name : Name) (u : Level) (domain : Expr) (pol : Bool)
      (bind : Name → Level → Expr → Expr → Bool → Expr → TreeProof → MetaM TreeProof) (tree : Expr) (k : Expr → M TreeProof) : OptionT M TreeProof :=
    Functor.map (f := M) some <|
    withLocalDeclD (`fvar ++ name) domain fun fvar =>
    withReader (Functor.map (· <=< liftMetaM ∘ bind name u domain fvar pol tree)) (k fvar) -- here somehow some free variable was not in the context
   
  introMeta (name : Name) (u : Level) (domain : Expr) (pol : Bool) (tree : Expr)
   (k : Expr → M TreeProof) : OptionT M TreeProof :=
    Functor.map (f := M) some <| do
    let mvar ← mkFreshExprMVar domain .synthetic (name)
    Function.swap withReader (k mvar) (fun k => do
      let assignment := Expr.eta (← instantiateMVars mvar)
      if let .mvar mvarId' := assignment then
        modify fun s => { s with mvarInfos := s.mvarInfos.insert mvarId' {name, u} }

      let kleiski ← k

      let {boundMVars, binders ..} ← get
      let mfvarsState := assignment.collectMFVars {}
      /- nonHypMVars are the metavariables that do not appear in any of the hypothesis metavariable assignments, and not in any earlier metavariable assignments,
      so these should be bound here. Recall that the hypothesis metavariables are present in `binders` -/
      let nonHypMVars := mfvarsState.MVarIds.filter (!boundMVars.contains ·)
      let nonHypBinders ← liftMetaM <| nonHypMVars.mapM mkMetaHypBinder

      let tree' := mkApp2 (.const (if pol then ``Tree.Exists else ``Tree.Forall) [u]) domain tree

      let (bindHyp, binders) := (if hypInScope then takeHypBinders (nonHypMVars.size != 0) mfvarsState else takeMVarHypBinders mfvarsState.toCollectMVarsState) binders pol tree'

      modify fun s => { s with boundMVars := boundMVars.insertMany nonHypMVars, binders }

      return kleiski <=< bindHyp
        <=< nonHypBinders.foldrM (revertHypBinder pol tree')
        ∘ introMVar mvar.mvarId! name u domain assignment pol tree)

/-
the arguments for a unification are:
hypothesis, and the position in that.
hypContext
goal, with position in that, and polarity.
-/
abbrev Unification := HypothesisContext → Expr → Expr → Bool → TreePos → Pos → Pos → MetaM' TreeProof 

partial def applyAux (hypProof : Expr) (hyp goal : Expr) (pol : Bool) (hypTreePos goalTreePos : TreePos) (hypPos goalPos : Pos) (unification : Unification) (saveClosed : Bool)
  : M TreeProof :=
  unfoldHypothesis hypProof hyp hypTreePos
    fun hyp hypTreePos hypContext =>
      (TreeRecMeta true saveClosed).recurse pol goal goalTreePos
        fun pol goal _ k => do
          let treeProof ← unification hypContext hyp goal pol hypTreePos hypPos goalPos
          let makeTreeProof ← k
          let treeProof ← (← get).binders.foldrM (fun binder => revertHypBinder pol goal binder) treeProof
          makeTreeProof treeProof
          -- return do (← get).binders.foldrM (fun binder => revertHypBinder pol goal binder) treeProof

partial def applyBound (hypTreePos goalTreePos : TreePos) (hypPos goalPos : Pos) (delete? : Bool) (unification : Unification) (saveClosed : Bool := false) (tree : Expr) : MetaM TreeProof := 
  let (treePos, hypTreePos, goalTreePos) := takeSharedPrefix hypTreePos goalTreePos
  ((TreeRecMeta false saveClosed).recurse true tree treePos
    fun pol tree _ => do

      let (p, goal, goalTreePos, goalPol, useHypProof, hypProof, hyp, hypTreePos) ← match tree, hypTreePos, goalTreePos with
      | imp_pattern p goal, 0::hypTreePos, 1::goalTreePos => do pure (p, goal, goalTreePos,  pol, UseHypImpRight, ← getHypothesis delete? (!pol) (!pol) p hypTreePos)
      | imp_pattern goal p, 1::hypTreePos, 0::goalTreePos => do pure (p, goal, goalTreePos, !pol, UseHypImpLeft , ← getHypothesis delete? (!pol)  pol   p hypTreePos)
      | and_pattern p goal, 0::hypTreePos, 1::goalTreePos => do pure (p, goal, goalTreePos,  pol, UseHypAndRight, ← getHypothesis delete?   pol   pol   p hypTreePos)
      | and_pattern goal p, 1::hypTreePos, 0::goalTreePos => do pure (p, goal, goalTreePos,  pol, UseHypAndLeft , ← getHypothesis delete?   pol   pol   p hypTreePos)
      | _, _, _ => throwError m! "cannot have hypothesis at {hypTreePos} and goal at {goalTreePos} in {tree}"

      withLocalDeclD `hyp hyp fun fvar => do
      let fvarId := fvar.fvarId!
      withReader (Functor.map (· ∘ useHypProof p hypProof pol goal fvarId)) do
        applyAux fvar hyp goal goalPol hypTreePos goalTreePos hypPos goalPos unification saveClosed
  ).run (pure pure) |>.run' {}
where
  takeSharedPrefix {α : Type} [BEq α] : List α → List α → List α × List α × List α
  | [], ys => ([], [], ys)
  | xs, [] => ([], xs, [])
  | xs'@(x::xs), ys'@(y::ys) =>
    if x == y
    then Bifunctor.fst (x :: ·) (takeSharedPrefix xs ys)
    else ([], xs', ys')


partial def applyUnbound (hypName : Name) (getHyp : Expr → MetaM Bool → MetaM (Expr × TreePos × Pos))
    (goalTreePos : TreePos) (goalPos : Pos) (unification : Unification) (tree : Expr) (saveClosed : Bool := false) : MetaM TreeProof := do
  let cinfo ← getConstInfo hypName
  let us ← mkFreshLevelMVarsFor cinfo
  let hypProof := .const hypName us
  let hyp := cinfo.instantiateTypeLevelParams us
  
  let (hyp, hypTreePos, hypPos) ← getHyp hyp $ getPolarity tree goalTreePos

  (applyAux hypProof hyp tree true hypTreePos goalTreePos hypPos goalPos unification saveClosed).run (pure pure) |>.run' {}


def synthMetaInstances (mvars : Array Expr) (force : Bool := false) : MetaM Unit := 
  if force
  then do
    for mvar in mvars do
      let mvarId := mvar.mvarId!
      unless ← isDefEq mvar (← synthInstance (← mvarId.getType)) do
        throwError m! "failed to assign synthesized instance of class {indentExpr (← mvarId.getType)} to {indentExpr mvar}"
  else do
    for mvar in mvars do
      let mvarId := mvar.mvarId!
      unless ← mvarId.isAssigned do
        mvarId.assign (← synthInstance (← mvarId.getType))

def treeApply (hypContext : HypothesisContext) (hyp goal : Expr) (pol : Bool) (hypTreePos : TreePos) (hypPos goalPos : Pos) : MetaM' TreeProof := do
  unless hypPos == [] do    
    throwError m! "cannot apply a subexpression: position {hypPos} in {hyp}"
  unless goalPos == [] do
    throwError m! "cannot apply in a subexpression: position {goalPos} in {goal}"
  match hypTreePos, hyp with
  | [], _ =>
    unless pol do
      throwError m! "cannot apply in negative position"
    let {metaIntro, instMetaIntro, hypProofM} := hypContext
    _ ← metaIntro
    let instMVars ← instMetaIntro
    if ← isDefEq goal hyp
    then
      synthMetaInstances instMVars
      let (_hyp, proof) ← hypProofM
      return {proof}
    else 
      throwError m! "couldn't unify hypothesis {hyp} with target {goal}"

  | [0], imp_pattern cond _ =>
    if pol then
      throwError m! "cannot apply a hypothesis of a hypothesis in positive position"
    let {metaIntro, instMetaIntro, hypProofM} := hypContext
    _ ← metaIntro
    let instMVars ← instMetaIntro
    if ← isDefEq goal cond then
      synthMetaInstances instMVars
      let (hyp, proof) ← hypProofM
      let imp_pattern _ newTree := hyp | panic! "imp_left didn't give imp_pattern"
      return {proof, newTree}
    else
      throwError m! "couldn't unify condition {cond} with target {goal}"
  | [1], not_pattern p =>
      if pol then
        throwError m! "cannot apply a negative in positive position"
      let {metaIntro, instMetaIntro, hypProofM} := hypContext
      _ ← metaIntro
      let instMVars ←instMetaIntro
      if ← isDefEq goal p then
        synthMetaInstances instMVars
        let (_, proof) ← hypProofM
        return {proof}
      else
        throwError m! "couldn't unify negative {p} with target {goal}"
  | _, _ => throwError "cannot apply a subexpression: subtree {hypTreePos} in {hyp}"

def getApplyPos (pos? : Option (TreePos × Pos)) (hyp : Expr) (goalPol : MetaM Bool) : MetaM (Expr × TreePos × Pos) := do
  let hypTree ← makeTree hyp
  let (treePos, pos) ← pos?.getDM do return (if ← goalPol then findTreePos hypTree else (findNegativeTreePos hypTree).getD [], [])
  return (← makeTreePath treePos hyp, treePos, pos)

open Elab.Tactic

/- the optional star indicates that the solved target should stay in the context as a hypothesis. -/
elab "tree_apply" s:("*")? hypPos:treePos goalPos:treePos : tactic => do
  let (hypTreePos, hypPos) := getSplitPosition hypPos
  let (goalTreePos, goalPos) := getSplitPosition goalPos
  workOnTree (applyBound hypTreePos goalTreePos hypPos goalPos true treeApply s.isSome)

elab "tree_apply'" s:("*")? hypPos:treePos goalPos:treePos : tactic => do
  let (hypTreePos, hypPos) := getSplitPosition hypPos
  let (goalTreePos, goalPos) := getSplitPosition goalPos
  workOnTree (applyBound hypTreePos goalTreePos hypPos goalPos false treeApply s.isSome)

elab "lib_apply" s:("*")? hypPos:(treePos)? hypName:ident goalPos:treePos : tactic => do
  let hypName ← getIdWithInfo hypName
  let (goalTreePos, goalPos) := getSplitPosition goalPos
  let hypPos := getSplitPosition <$> hypPos
  workOnTree (applyUnbound hypName (getApplyPos hypPos) goalTreePos goalPos treeApply · s.isSome)

open DiscrTree in
def librarySearchApply (saveClosed : Bool) (goalPos : List ℕ) (tree : Expr) : MetaM (Array (Array (Name × AssocList SubExpr.Pos Widget.DiffTag × String) × Nat)) := do
  let (goalTreePos, []) := splitPosition goalPos | return #[]
  let discrTrees ← getLibraryLemmas
  let results := if ← getPolarity tree goalTreePos then
    (← getSubExprUnify discrTrees.2.apply tree goalTreePos []) ++ (← getSubExprUnify discrTrees.1.apply tree goalTreePos [])
  else
    (← getSubExprUnify discrTrees.2.apply_rev tree goalTreePos []) ++ (← getSubExprUnify discrTrees.1.apply_rev tree goalTreePos [])

  let results ← filterLibraryResults results fun {name, treePos, pos, ..} => do
    try
      _ ← applyUnbound name (fun hyp _ => return (← makeTreePath treePos hyp, treePos, pos)) goalTreePos [] treeApply tree saveClosed
      return true
    catch _ =>
      return false

  return results.map $ Bifunctor.fst $ Array.map fun {name, treePos, pos, diffs} => (name, diffs, 
    s! "lib_apply {if saveClosed then "*" else ""} {printPosition treePos pos} {name} {goalPos}")


def logLibrarySearch (result : Array (Array (Name × AssocList SubExpr.Pos Widget.DiffTag × String) × Nat)) : MetaM Unit := do
  let result ← result.mapM fun (candidates, specific) => return (specific, ← candidates.mapM fun (name, _) => return m! "{name} : {(← getConstInfo name).type}")
  logInfo m! "{result}"


elab "try_lib_apply" goalPos:treePos : tactic => do
  let goalPos := getPosition goalPos
  let tree := (← getMainDecl).type
  logLibrarySearch (← librarySearchApply false goalPos tree)

set_option checkBinderAnnotations false in
abbrev Tree.infer {α : Prop} [i : α] := i



-- #exit
-- example (a b c : Nat) : a + b + c = a + (b + c) := by
--   try_lib_apply []




example (p q : Prop) : ((p → q) ∧ p) → (q → False) → False := by
  make_tree
  tree_apply [0,0,1] [1,0,0]
  tree_apply' [0] [1,0,0]
  tree_apply [1,0] [1,1]



example : ({α : Type 0} → {r : α → α → Prop} → [IsRefl α r] → (a : α) → r a a) → 3 = 3 := by
  make_tree
  tree_apply [0,1,1,1,1] [1]
  -- lib_apply refl [1]


lemma cantor_end : ∀ (X : Type u) (f : X → Set X), ∃ a : Set X, ∀ a_1 : X,
¬a_1 ∈ f a_1 ↔ a_1 ∈ a := by
  make_tree
  lib_apply [1,1,1,1] refl [1, 1, 1, 1, 2]



example :
  (∀ hh > 0, 0 < hh) → ∀ ε:Nat,
  0 < ε := by
  make_tree
  tree_apply [0,1,1] [1,1]
  sorry

example (p q : Prop) : (q → p) → ∃ n:Nat, p := by
  make_tree
  tree_apply [0,1] [1,1]
  sorry

example (p : Prop) : (∀ _n:Nat, p) → p := by
  make_tree
  tree_apply [0,1] [1]

example (p : Nat → Prop): (∀ m, (1=1 → p m)) → ∀ m:Nat, p m := by
  make_tree
  tree_apply [0,1,1] [1,1]
  rfl

example (p q : Prop) : p → (p → q) → q := by
  make_tree
  tree_apply [0] [1,0,0]
  -- q → q
  tree_apply [0] [1]

example (p q : Prop) : p → (p → q) → q := by
  make_tree
  tree_apply [1,0,1] [1,1]
  -- p → p
  tree_apply [0] [1]
  
example (p q : Prop) : p → (p → q) → q := by
  make_tree
  tree_apply [1,0,0] [0]
  -- p → p
  tree_apply [0] [1]

example (p q r : Prop) : (q → p) → (q ∧ r) → p := by
  make_tree
  tree_apply [1,0,0] [0,0]
  tree_apply [0] [1,1]

example (p q : Prop) : p ∧ (p → q) → q := by
  make_tree
  tree_apply [0,0] [0,1,0]
  -- q → q
  tree_apply [0] [1]
  
example (p q : Prop) : ((p → q) ∧ p) ∧ p → q := by
  make_tree
  tree_apply [0,1] [0,0,0,0]
  -- q → q
  tree_apply [0,0] [1]

example (p q : Prop) : (p → q) → p → q := by
  make_tree
  tree_apply [1,0] [0,0]
  -- q → q
  tree_apply [0] [1]
  
example (p q : Prop) : ((q → p) → p → q) → True := by
  make_tree
  tree_apply [0,1,0] [0,0,1]
  lib_apply trivial [1]

example (p q r s: Prop) : (p → q → r → s) → q → True := by
  make_tree
  tree_apply [0,1,0] [1,0]
  -- q → q
  lib_apply trivial [1]

example (p : Prop) : p → p := by
  make_tree
  tree_apply [0] [1]

example [Preorder α] (a b : α) : a < b → a ≤ b := by
  make_tree
  lib_apply le_of_lt [0]
  tree_apply [0] [1]
  
example [Preorder α] (a b : α) : a < b → a ≤ b := by
  make_tree
  lib_apply [1,1,1,1,1] le_of_lt [1]
  tree_apply [0] [1]
  
example [Preorder α] (a b : α) : a < b → a ≤ b := by
  make_tree
  lib_intro le_of_lt
  tree_apply [0,1,1,1,1] [1]

example : p → ¬ p → q := by
  make_tree
  tree_apply [1,0,1] [0]

example : ¬ p → p → q := by
  make_tree
  tree_apply [1,0] [0,1]

example : p → ¬ p → q := by
  make_tree
  tree_apply [0] [1,0,1]

example : ¬ p → p → q := by
  make_tree
  tree_apply [0,1] [1,0]

example : (p → False) → ¬ p := by
  make_tree
  tree_apply [0,0] [1,1]
  simp


/-
I was wondering what the exact way should be in which quantifiers are handled by the tree apply/rewrite moves.
The simplest example where this is non-trivial is this:
-/
-- set_option pp.all true in
example (p q r : Prop) : (p → q ∧ r) → q ∧ (p → r) := by
  make_tree
  tree_apply [0,1,1] [1,1,1]
  tree_apply [1,0] [1,1]
  exact (sorry : p)

/-
then applying the first r to the second r could have 3 different results that all make some sense:
· q ∧ p ⇨ p
· p ∧ q ⇨ q
· (p ⇨ q) ⇨ q ∧ p ⇨ p

which after a trivial simplification turn into
· q
· p
· (p ⇨ q) ⇨ q

The previous version did the first option, but I see arguments for both other versions.
The current version does the second option.
The first two options have the nice property that the order of quantifiers from the hypothesis is maintained.
The third option requires a 'skolemization' of the q in the hypothesis.
The big advantage of the third option is that it is more safe.
-/