import Tree
import PrintTree
open Tree Lean Meta


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
  | some {name, u} => return bindMVar mvarId type name u pol tree treeProof
  | none =>
    let name ← mkFreshUserName `m -- in the future make a more sophisticated name generator
    let u' ← getLevel type
    let u ← decLevel u'
    return bindMVar mvarId type name u pol tree treeProof


def revertHypBinder : HypBinder → Bool → Expr → TreeProof → MetaM' TreeProof
| .meta mvar type => bindMeta mvar type
| .free fvar name u type definition => (return bindFVar fvar name u type definition · · ·)
| .unknown fvar type     => (return bindUnknown type fvar · · ·)
| .known definition type => (return bindKnown type definition · · ·)

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

def Lean.Expr.collectMFVars (s : CollectMFVars.State) (e : Expr) : CollectMFVars.State :=
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
    := fun (kleisli, binders) => if isUsed then (kleisli <=< revertHypBinder binder pol tree, binders) else (kleisli, binders.push binder)



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
    := Bifunctor.fst (· <=< revertHypBinder binder pol tree)



/-
When we bind a metavariable in front of a target, we want to bind all free variables and knowns from the hypothesis binders in front of that.
When one such binder is bound, all binders before it must also be bound.
In addition, we must bind all metavariables from the hypothesis that we have a dependency on. This we keep track of with a HashSet MVarId

However, if the hypothesis is not in scope, we are not allowed to use free or known binders, so we only take the required meta binders.
-/
-- def takeHypBinders (mvarAssignment : Option Expr) (binders : Array HypBinder) (pol : Bool) (tree : Expr) : (TreeProof → MetaM' TreeProof) × Array HypBinder :=
--   let startContext := match mvarAssignment with | none => {} | some mvarAssignment => takeHypBinders.visit mvarAssignment {}
--   let (treeProofKleisli, s) := go.run startContext
--   (treeProofKleisli, s.unusedBinders)
-- where
--   go : takeHypBinders.Context → (TreeProof → MetaM' TreeProof) × Array HypBinder :=
--     binders.foldl (init := pure pure) fun f binder s =>
--       match binder with
--       | .meta mvar (type := type) .. =>
--         let isUsed := s.anyFVars || s.MVarIds.contains mvar
--         let s := if isUsed then { s with anyMVars := true } else s
--         push s.anyFVars binder type isUsed f

--       | .free fvar (type := type) .. =>
--         let isUsed := s.anyMVars
--         let s := if isUsed then { s with anyFVars := true} else s
--         push s.anyFVars binder type isUsed f

--       | .unknown (type := type) .. =>
--         let isUsed := s.anyFVars
--         push s.anyFVars binder type isUsed f

--       | .known (type := type) .. =>
--         let isUsed := s.anyMVars
--         let s := if isUsed then { s with anyFVars := true} else s
--         push s.anyFVars binder type isUsed f
    
--   push (anyFVars : Bool) (binder : HypBinder) (type : Expr) (isUsed : Bool) (f : takeHypBinders.Context → (TreeProof → MetaM' TreeProof) × Array HypBinder)
--     : takeHypBinders.Context → (TreeProof → MetaM' TreeProof) × Array HypBinder := fun s =>
--     if isUsed
--     then
--       unless anyFVars do
--         modify (takeHypBinders.visit type)
--       let treeProofKleisli ← f
--       return treeProofKleisli <=< revertHypBinder binder pol tree
--     else
--       let treeProofKleisli ← f
--       modify (fun s => { s with unusedBinders := s.unusedBinders.push binder})
--       return treeProofKleisli




structure HypothesisContext where
  hypProofM : MetaM' (Expr × Expr)
  metaIntro : MetaM (Array Expr) := pure #[]
  instMetaIntro : MetaM (Array Expr) := pure #[]


def HypothesisRec : OptionRecursor (ReaderT HypothesisContext MetaM' α) where
  inst _u cls _pol _tree k := some do
    let mvarId ← mkFreshMVarId
    let mvar := .mvar mvarId
    withReader (fun c => { c with
      instMetaIntro := return (← c.instMetaIntro).push (← mkFreshExprMVarWithId mvarId cls (kind := .synthetic))
      hypProofM := do
        let (instance_pattern _u _domain tree, hypProof) ← c.hypProofM | panic! ""

        let assignment ← instantiateMVars mvar
        
        let newMVars := ((assignment.collectMVars {}).result).filter (!(← get).boundMVars.contains ·)
        let newBinders ← liftMetaM <| newMVars.mapM mkMetaHypBinder
        modify fun s => { s with
          boundMVars := s.boundMVars.insertMany newMVars
          binders := s.binders ++ newBinders
          }

        return (tree.instantiate1 assignment, .app hypProof assignment)
    }) do
    k mvar
  all name _u domain _pol _tree k := some do
    let mvarId ← mkFreshMVarId
    let mvar := .mvar mvarId
    withReader (fun c => { c with
      metaIntro := return (← c.metaIntro).push (← mkFreshExprMVarWithId mvarId domain (kind := .natural) (userName := name))
      hypProofM := do
        let (forall_pattern name u _domain tree, hypProof) ← c.hypProofM | panic! ""
        let assignment ← instantiateMVars mvar

        if let .mvar mvarId' := assignment then
          modify fun s => let (mvarInfos, duplicate) := s.mvarInfos.insert' mvarId' {name, u}; if duplicate then s else { s with mvarInfos }

        let newMVars := ((assignment.collectMVars {}).result).filter (!(← get).boundMVars.contains ·)
        let newBinders ← liftMetaM <| newMVars.mapM mkMetaHypBinder
        modify fun s => { s with
          boundMVars := s.boundMVars.insertMany newMVars
          binders := s.binders ++ newBinders
          }
        return (tree.instantiate1 assignment, .app hypProof assignment)
      }) do
    k mvar
    

  ex name u domain _pol _tree k := some do
    withLocalDeclD name domain fun fvar => do
    let fvarId := fvar.fvarId!
    let u' := .succ u
    withReader (fun c => { c with
      hypProofM := do
        let (exists_pattern name u domain tree, hypProof) ← c.hypProofM | panic! ""
        let lamTree := .lam name domain tree .default
        addBinder (.free fvarId name u domain (mkApp3 (.const ``Classical.choose [u']) domain lamTree hypProof))
        return (tree.instantiate1 fvar, mkApp3 (.const ``Classical.choose_spec [u']) domain lamTree hypProof)
    }) do
    k fvar
    

  imp_right p _pol _tree k := some do
    withLocalDeclD `unknown p fun fvar => do
    let fvarId := fvar.fvarId!
    withReader (fun c => { c with
      hypProofM := do
        let (imp_pattern p tree, hypProof) ← c.hypProofM | panic! ""
        addBinder (.unknown fvarId p)
        return (tree, .app hypProof fvar)
    }) do
    k

  and_right _p _pol _tree k := some do
    withReader (fun c => { c with
      hypProofM := do
        let (and_pattern p tree, hypProof) ← c.hypProofM | panic! ""
        addBinder (.known (.proj `And 0 hypProof) p)
        return (tree, .proj `And 1 hypProof)
    }) do
    k
    
  and_left _p _pol _tree k := some do
    withReader (fun c => { c with
      hypProofM := do
        let (and_pattern tree p, hypProof) ← c.hypProofM | panic! ""
        addBinder (.known (.proj `And 1 hypProof) p)
        return (tree, .proj `And 0 hypProof)
    }) do
    k
    
  imp_left _p _pol _tree _k := none --some <| throwError m!"{tree} → {p}: can only move to the right of an implication when unfolding a hypothesis"

where
  addBinder (hypBinder : HypBinder) : MetaM' Unit := do
    modify fun s => { s with binders := s.binders.push hypBinder }


/- 
Run the inner MetaM' monad on the inner hypothesis-tree, and the remaining tree position, and the HypothesisContext.
unfoldHypothesis adds free variables into the context for the Exists and Imp binders in the hypothesis-tree,
and the metavariables for Forall and Instance binders are stored in the HypothesisContext. They will be added to the
MetaM context later, so that all available free variables will be in their context.
-/
def _root_.unfoldHypothesis [Inhabited α] (hypProof : Expr) (tree : Expr) (pos : List TreeBinderKind) (k : Expr → List TreeBinderKind → ReaderT HypothesisContext MetaM' α) : MetaM' α :=
  HypothesisRec.recurse true tree pos (fun _pol tree path => k tree path) |>.run {hypProofM := pure (tree, hypProof)}




def getHypothesisRec (wantedPol : Bool) : OptionRecursor (TreeHyp × Expr × List TreeBinderKind) where
  all _ _ _ _ _ _ := none
  ex  _ _ _ _ _ _ := none
  inst _ _ _ _ _  := none
  imp_right p pol tree k := if wantedPol == pol then none else some <| Bifunctor.fst (ImpRightWithHyp p pol tree) k
  imp_left  p pol tree k := if wantedPol == pol then none else some <| Bifunctor.fst (ImpLeftWithHyp  p pol tree) k
  and_right p pol tree k := if wantedPol != pol then none else some <| Bifunctor.fst (AndRightWithHyp p pol tree) k
  and_left  p pol tree k := if wantedPol != pol then none else some <| Bifunctor.fst (AndLeftWithHyp  p pol tree) k

/-
getHypothesis returns TreeHyp, which contains a proof and the type of the hypothesis,
and the replacement tree (since we may delete the hypothesis from the tree), and the remaining tree position in the hypothesis.
For example, if the state is `p ⇨ q ⇨ r` and we want to use `q` in `p`, then the replacement tree will be `r`,
and the remaining tree position is the original one with the head `[.imp_left]` removed.
-/
def getHypothesis (delete? wantedPol pol : Bool) (tree : Expr) (path : List TreeBinderKind) : TreeHyp × Expr × List TreeBinderKind :=
  (getHypothesisRec wantedPol).recurse pol tree path fun pol tree path => (MakeHyp delete? pol tree, tree, path)




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
def TreeRecMeta (hypInScope : Bool) : Recursor (MetaM' (MetaM' TreeProof)) where
  imp_right := introProp true false bindImpRight
  imp_left  := introProp true true bindImpLeft
  and_right := introProp false false bindAndRight
  and_left  := introProp false true bindAndLeft

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
  
  inst u cls pol :=
    introFree `_inst u cls pol bindInstance

where
  introProp (isImp isRev : Bool) (bind : Expr → Bool → Expr → TreeProof → TreeProof) (p : Expr) (pol : Bool) (tree : Expr) : MetaM' (MetaM' TreeProof) → MetaM' (MetaM' TreeProof) :=
    Functor.map <| if hypInScope && (pol != (isImp && !isRev))
    then
      fun k => do
      let tree' := (if isRev then Function.swap else id) (mkApp2 (.const (if isImp then ``Imp else ``Tree.And) [])) p tree
      let {binders ..} ← get
      let (bindHyp, binders) := takeHypBinders true {} binders pol tree'
      modify fun s => { s with binders }
      let treeProof ← k
      let treeProof := bind p pol tree treeProof
      bindHyp treeProof
    else
      Functor.map <| bind p pol tree

  introFree (name : Name) (u : Level) (domain : Expr) (pol : Bool)
      (bind : Name → Level → Expr → Expr → Bool → Expr → TreeProof → TreeProof) (tree : Expr) (k : Expr → MetaM' (MetaM' TreeProof)) : MetaM' (MetaM' TreeProof) :=
    withLocalDeclD (`fvar ++ name) domain fun fvar => do
    let treeProofM ← k fvar
    return bind name u domain fvar pol tree <$> treeProofM

  introMeta (name : Name) (u : Level) (domain : Expr) (pol : Bool) (tree : Expr)
   (k : Expr → MetaM' (MetaM' TreeProof)) : MetaM' (MetaM' TreeProof) := do
    let mvar ← mkFreshExprMVar domain .synthetic (`mvar ++ name)
    let k ← k mvar
    let assignment ← instantiateMVars mvar
    if let .mvar mvarId' := assignment then
      modify fun s => { s with mvarInfos := s.mvarInfos.insert mvarId' {name, u} }
      
    return do
      let tree' := mkApp2 (.const (if pol then ``Tree.Exists else ``Tree.Forall) [u]) domain tree

      let {boundMVars, binders ..} ← get
      let mfvarsState := assignment.collectMFVars {}
      let nonHypMVars := mfvarsState.MVarIds.filter (!boundMVars.contains ·)
      let nonHypBinders ← liftMetaM <| nonHypMVars.mapM mkMetaHypBinder

      let (bindHyp, binders) := (if hypInScope then takeHypBinders (nonHypMVars.size != 0) mfvarsState else takeMVarHypBinders mfvarsState.toCollectMVarsState) binders pol tree'

      modify fun s => { s with boundMVars := boundMVars.insertMany nonHypMVars, binders }

      let treeProof ← k
      let treeProof := introMVar mvar.mvarId! name u domain assignment pol tree treeProof
      let treeProof ← nonHypBinders.foldrM (fun hypBinder => revertHypBinder hypBinder pol tree') treeProof
      let treeProof ← bindHyp treeProof
      return treeProof


/-
the arguments for a unification are:
hypothesis, and the path and the position in that.
hypContext
goal, with position in that, and polarity.
-/
abbrev UnificationProof := HypothesisContext → Expr → Expr → Bool → List TreeBinderKind → List Nat → List Nat → MetaM' TreeProof 

partial def applyAux (hypProof : Expr) (hyp goal : Expr) (pol : Bool) (hypPath goalPath : List TreeBinderKind) (hypPos goalPos : List Nat) (unification : UnificationProof)
  : MetaM' (MetaM' TreeProof) :=
  unfoldHypothesis hypProof hyp hypPath
    fun hyp hypPath hypContext =>
      (TreeRecMeta true).recurseM pol goal goalPath
        fun pol goal => do
          let treeProof ← unification hypContext hyp goal pol hypPath hypPos goalPos
          return do (← get).binders.foldrM (fun binder => revertHypBinder binder pol goal) treeProof

partial def applyBound (hypPos goalPos : List Nat) (delete? : Bool) (unification : UnificationProof) (tree : Expr) : MetaM TreeProof := (do
  let (hypPath , hypPos ) := positionToPath hypPos tree
  let (goalPath, goalPos) := positionToPath goalPos tree
  let (path, hypPath, goalPath) := takeSharedPrefix hypPath goalPath
  let treeProofM ← (TreeRecMeta false).recurseM true tree path
    fun pol tree => do

      let (p, goal, goalPath, goalPol, useHypProof, hypProof, hyp, hypPath) ← match tree, hypPath, goalPath with
        | imp_pattern p goal, .imp_left ::hypPath, .imp_right::goalPath => pure (p, goal, goalPath,  pol, UseHypImpRight, getHypothesis delete? (!pol) (!pol) p hypPath)
        | imp_pattern goal p, .imp_right::hypPath, .imp_left ::goalPath => pure (p, goal, goalPath, !pol, UseHypImpLeft,  getHypothesis delete? (!pol)  pol  p hypPath)
        | and_pattern p goal, .and_left ::hypPath, .and_right::goalPath => pure (p, goal, goalPath,  pol, UseHypAndRight, getHypothesis delete?   pol   pol  p hypPath)
        | and_pattern goal p, .and_right::hypPath, .and_left ::goalPath => pure (p, goal, goalPath,  pol, UseHypAndLeft,  getHypothesis delete?   pol   pol  p hypPath)
        | _, _, _ => throwError m!"cannot have hypothesis at {hypPath} and goal at {goalPath} in {tree}"

      withLocalDeclD `hyp hyp fun fvar => do
      let fvarId := fvar.fvarId!
      let treeProofM ← applyAux (.fvar fvarId) hyp goal goalPol hypPath goalPath hypPos goalPos unification
      return useHypProof p hypProof pol goal fvarId <$> treeProofM
  
  treeProofM : MetaM' _).run' {}
where
  takeSharedPrefix {α : Type} [BEq α] : List α → List α → List α × List α × List α
  | [], ys => ([], [], ys)
  | xs, [] => ([], xs, [])
  | xs'@(x::xs), ys'@(y::ys) =>
    if x == y
    then Bifunctor.fst (x :: ·) (takeSharedPrefix xs ys)
    else ([], xs', ys')



partial def applyUnbound (hypName : Name) (getHypPos : Expr → List TreeBinderKind → List TreeBinderKind × List Nat) (goalPos : List Nat) (unification : UnificationProof) (tree : Expr) : MetaM TreeProof := (do
  let (goalPath, goalPos) := positionToPath goalPos tree
  let hypProof ← mkConstWithFreshMVarLevels hypName
  let hyp ← makeTree (← inferType hypProof)
  let (hypPath, hypPos) := getHypPos hyp goalPath

  let treeProofM ← applyAux hypProof hyp tree true hypPath goalPath hypPos goalPos unification
  treeProofM : MetaM' _).run' {}

-- partial def applyUnbound' (hypName : Name) (goalPos : List Nat) (unification : UnificationProof) (tree : Expr) : MetaM TreeProof := (do
--   let (goalPath, goalPos) := positionToPath goalPos tree
--   let hypProof ← mkConstWithFreshMVarLevels hypName
--   let hyp ← makeTree (← inferType hypProof)

--   let mut hypPath := getPath hyp
--   let polarity := PathToPolarity goalPath
--   if !polarity then
--     let rec go : List TreeBinderKind → Option (List TreeBinderKind)
--       | x::xs => match x, go xs with
--         | x         , some ys => some (x::ys)
--         | .imp_right, none    => some [.imp_left]
--         | _         , none    => none
--       | [] => none
--     hypPath ← (go hypPath).getDM do throwError m! "when applying in negative position, the library result has to have a hypothesis"

--   let treeProofM ← applyAux hypProof hyp tree true hypPath goalPath goalPos unification
--   treeProofM : MetaM' _).run' {}

def synthMetaInstances (mvars : Array Expr) (force : Bool := false) : MetaM Unit := 
  if force
  then do
    for mvar in mvars do
      let mvarId := mvar.mvarId!
      unless ← isDefEq mvar (← synthInstance (← mvarId.getType)) do
        throwError m!"failed to assign synthesized instance {indentExpr (← mvarId.getType)}"
  else do
    for mvar in mvars do
      let mvarId := mvar.mvarId!
      unless ← mvarId.isAssigned do
        mvarId.assign (← synthInstance (← mvarId.getType))

def treeApply (hypContext : HypothesisContext) (hyp goal : Expr) (pol : Bool) (hypPath : List TreeBinderKind) (hypPos goalPos : List Nat) : MetaM' TreeProof := do
  unless hypPos == [] do    
    throwError m!"cannot apply a subexpression: position {hypPos} in {hyp}"
  unless goalPos == [] do
    throwError m!"cannot apply in a subexpression: position {goalPos} in {goal}"
  match hypPath with
  | [] =>
    unless pol do
      throwError m!"cannot apply in negative position"
    let {metaIntro, instMetaIntro, hypProofM} := hypContext
    _ ← metaIntro
    let instMVars ← instMetaIntro
    if ← isDefEq goal hyp
    then
      synthMetaInstances instMVars
      let (_hyp, proof) ← hypProofM
      return {proof}
    else 
      throwError m!"couldn't unify hypothesis {hyp} with target {goal}"

  | [.imp_left] =>
    if pol then
      throwError m!"cannot apply a hypothesis of a hypothesis in positive position"
    let {metaIntro, instMetaIntro, hypProofM} := hypContext
    _ ← metaIntro
    let instMVars ← instMetaIntro
    let imp_pattern cond _ := hyp | panic! "imp_left didn't give imp_pattern"
    if ← isDefEq goal cond then
      synthMetaInstances instMVars
      let (hyp, proof) ← hypProofM
      let imp_pattern _ newTree := hyp | panic! "imp_left didn't give imp_pattern"
      return {proof, newTree}
    else
      throwError m!"couldn't unify condition {cond} with target {goal}"
  | _ => throwError "cannot apply a subexpression: subtree {hypPath} in {hyp}"

def getApplyPos (hyp : Expr) (goalPath : List TreeBinderKind) : List TreeBinderKind × List Nat :=
  (if PathToPolarity goalPath then getPath hyp else (getPathToHyp hyp).getD [], [])

open Elab.Tactic

elab "tree_apply" hypPos:treePos goalPos:treePos : tactic => do
  let hypPos := get_positions hypPos
  let goalPos := get_positions goalPos
  workOnTree (applyBound hypPos goalPos true treeApply)

elab "tree_apply'" hypPos:treePos goalPos:treePos : tactic => do
  let hypPos := get_positions hypPos
  let goalPos := get_positions goalPos
  workOnTree (applyBound hypPos goalPos false treeApply)

elab "lib_apply" hypName:ident goalPos:treePos : tactic => do
  let hypName := hypName.getId
  let goalPos := get_positions goalPos
  workOnTree (applyUnbound hypName getApplyPos goalPos treeApply)


example (p q : Prop) : ((p → q) ∧ p) → (q → False) → False := by
  make_tree
  tree_apply [0,1,0,1,1] [1,0,1,0,1]
  tree_apply' [0,1] [1,0,1,0,1]
  tree_apply [1,0,1] [1,1]



example : ({α : Type 0} → {r : α → α → Prop} → [IsRefl α r] → (a : α) → r a a) → 3 = 3 := by
  make_tree
  tree_apply [0,1,1,1,1,1,1,1,1,1] [1]
  -- lib_apply refl [1]

set_option checkBinderAnnotations false in
abbrev Tree.infer {α : Prop} [i : α] := i

example :
  (∀ hh > 0, 0 < hh) → ∀ ε:Nat,
  0 < ε := by
  make_tree
  tree_apply [0,1,1,1,1] [1,1,1]
  sorry

example (p q : Prop) : (q → p) → ∃ n:Nat, p := by
  make_tree
  tree_apply [0,1,1] [1,1,1]
  sorry

example (p : Prop) : (∀ _n:Nat, p) → p := by
  make_tree
  tree_apply [0,1,1,1] [1]
  lib_apply Tree.infer []

example (p : Nat → Prop): (∀ m, (1=1 → p m)) → ∀ m:Nat, p m := by
  make_tree
  tree_apply [0,1,1,1,1] [1,1,1]
  rfl

example (p q : Prop) : p → (p → q) → q := by
  make_tree
  tree_apply [0,1] [1,0,1,0,1]
  -- q → q
  tree_apply [0,1] [1]

example (p q : Prop) : p → (p → q) → q := by
  make_tree
  tree_apply [1,0,1,1] [1,1]
  -- p → p
  tree_apply [0,1] [1]
  
example (p q : Prop) : p → (p → q) → q := by
  make_tree
  tree_apply [1,0,1,0,1] [0,1]
  -- p → p
  tree_apply [0,1] [1]

example (p q r : Prop) : (q → p) → (q ∧ r) → p := by
  make_tree
  tree_apply [1,0,1,0,1] [0,1,0,1]
  tree_apply [0,1] [1,1]

example (p q : Prop) : p ∧ (p → q) → q := by
  make_tree
  tree_apply [0,1,0,1] [0,1,1,0,1]
  -- q → q
  tree_apply [0,1] [1]
  
example (p q : Prop) : ((p → q) ∧ p) ∧ p → q := by
  make_tree
  tree_apply [0,1,1] [0,1,0,1,0,1,0,1]
  -- q → q
  tree_apply [0,1,0,1] [1]

example (p q : Prop) : (p → q) → p → q := by
  make_tree
  tree_apply [1,0,1] [0,1,0,1]
  -- q → q
  tree_apply [0,1] [1]
  
example (p q : Prop) : ((q → p) → p → q) → True := by
  make_tree
  tree_apply [0,1,1,0,1] [0,1,0,1,1]
  lib_apply trivial [1]

example (p q r s: Prop) : (p → q → r → s) → q → True := by
  make_tree
  tree_apply [0,1,1,0,1] [1,0,1]
  -- q → q
  lib_apply trivial [1]

example (p : Prop) : p → p := by
  make_tree
  tree_apply [0,1] [1]

example [Preorder α] (a b : α) : a < b → a ≤ b := by
  make_tree
  lib_apply le_of_lt [0,1]
  tree_apply [0,1] [1]
  
example [Preorder α] (a b : α) : a < b → a ≤ b := by
  make_tree
  lib_apply le_of_lt [1]
  tree_apply [0,1] [1]
  
example [Preorder α] (a b : α) : a < b → a ≤ b := by
  make_tree
  lib_intro le_of_lt
  tree_apply [0,1,1,1,1,1,1,1,1,1] [1]

/-
I was wondering what the exact way should be in which quantifiers are handled by the tree apply/rewrite moves.
The simplest example where this is non-trivial is this:
-/
-- set_option pp.all true in
example (p q r : Prop) : (p → q ∧ r) → q ∧ (p → r) := by
  make_tree
  tree_apply [0,1,1,1] [1,1,1]
  tree_apply [1,0,1] [1,1]
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