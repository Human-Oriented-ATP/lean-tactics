import Tree
import PrintTree
open Tree Lean Meta

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


namespace takeHypBinders

structure State where
  visitedExpr   : ExprSet         := {}
  FVarIds       : HashSet FVarId  := {}
  MVarIds       : HashSet MVarId  := {}
  anyFVars      : Bool            := false
  unusedBinders : Array HypBinder := #[]

instance : Inhabited State := ⟨{}⟩

abbrev Visitor := State → State

mutual
  partial def visit (e : Expr) : Visitor := fun s =>
    if (!e.hasMVar && !e.hasFVar) || s.visitedExpr.contains e then s
    else main e { s with visitedExpr := s.visitedExpr.insert e }

  partial def main : Expr → Visitor
    | Expr.proj _ _ e      => visit e
    | Expr.forallE _ d b _ => visit b ∘ visit d
    | Expr.lam _ d b _     => visit b ∘ visit d
    | Expr.letE _ t v b _  => visit b ∘ visit v ∘ visit t
    | Expr.app f a         => visit a ∘ visit f
    | Expr.mdata _ b       => visit b
    | Expr.mvar mvarId     => fun s => { s with MVarIds := s.MVarIds.insert mvarId }
    | Expr.fvar fvarId     => fun s => { s with FVarIds := s.FVarIds.insert fvarId }
    | _                    => id
end
end takeHypBinders

def takeHypBinders (mvarAssignment : Expr) (binders : Array HypBinder) (pol : Bool) (tree : Expr) : (TreeProof → MetaM' TreeProof) × Array HypBinder :=
  let (treeProofKleisli, s) := go.run (takeHypBinders.visit mvarAssignment {})
  (treeProofKleisli, s.unusedBinders)
where
  go : StateM takeHypBinders.State (TreeProof → MetaM' TreeProof) :=
    binders.foldl (init := pure pure) fun treeProofKleisliM binder => do
      let s ← get
      match binder with
      | .meta mvar (type := type) .. =>
        let isUsed := s.anyFVars || s.MVarIds.contains mvar
        push binder type isUsed treeProofKleisliM
      | .free fvar (type := type) .. =>
        let isUsed := s.FVarIds.contains fvar
        if isUsed then
          set { s with anyFVars := true}
        push binder type isUsed treeProofKleisliM
      | .unknown (type := type) .. =>
        let isUsed := s.anyFVars
        push binder type isUsed treeProofKleisliM

      | .known (type := type) .. =>
        let isUsed := s.anyFVars
        push binder type isUsed treeProofKleisliM
    
  push (binder : HypBinder) (type : Expr) (isUsed : Bool) (treeProofKleisliM : StateM takeHypBinders.State (TreeProof → MetaM' TreeProof)) : StateM takeHypBinders.State (TreeProof → MetaM' TreeProof) := do
    if isUsed
    then
      modify (takeHypBinders.visit type)
      let treeProofKleisli ← treeProofKleisliM
      return treeProofKleisli <=< revertHypBinder binder pol tree
    else
      let treeProofKleisli ← treeProofKleisliM
      modify (fun s => { s with unusedBinders := s.unusedBinders.push binder})
      return treeProofKleisli



structure takeKnownHypBinders.State where
  treeProofKleisli  : TreeProof → MetaM' TreeProof  := pure
  anyUnknowns       : Bool                          := false
  unusedBinders     : Array HypBinder               := #[]

def takeKnownHypBinders (binders : Array HypBinder) (pol : Bool) (tree : Expr) : (TreeProof → MetaM' TreeProof) × Array HypBinder :=
  (go.treeProofKleisli, go.unusedBinders)
where
  go : takeKnownHypBinders.State :=
    binders.foldl (init := {}) fun s binder =>
      if s.anyUnknowns
      then
        { s with unusedBinders := s.unusedBinders.push binder}
      else
        match binder with
        | .known .. => { s with
          treeProofKleisli := s.treeProofKleisli <=< revertHypBinder binder pol tree}
        | _ => { s with
          unusedBinders := s.unusedBinders.push binder
          anyUnknowns := true }





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

def _root_.unfoldHypothesis [Inhabited α] (hypProof : Expr) (tree : Expr) (pos : List TreeBinderKind) (k : Expr → List TreeBinderKind → ReaderT HypothesisContext MetaM' α) : MetaM' α :=
  HypothesisRec.recurse true tree pos (fun _pol tree path => k tree path) |>.run {hypProofM := pure (tree, hypProof)}




def getHypothesisRec (hypPol : Bool) : OptionRecursor (TreeHyp × Bool × Expr × List TreeBinderKind) where
  all _ _ _ _ _ _ := none
  ex  _ _ _ _ _ _ := none
  inst _ _ _ _ _  := none
  imp_right p pol tree k := if  hypPol then none else some <| Bifunctor.fst (ImpRightWithHyp p pol tree) k
  imp_left  p pol tree k := if  hypPol then none else some <| Bifunctor.fst (ImpLeftWithHyp  p pol tree) k
  and_right p pol tree k := if !hypPol then none else some <| Bifunctor.fst (AndRightWithHyp p pol tree) k
  and_left  p pol tree k := if !hypPol then none else some <| Bifunctor.fst (AndLeftWithHyp  p pol tree) k


def getHypothesis (delete? hypPol pol : Bool) (tree : Expr) (path : List TreeBinderKind) : TreeHyp × Bool × Expr × List TreeBinderKind :=
  (getHypothesisRec hypPol).recurse pol tree path fun pol tree path => (MakeHyp delete? pol tree, pol, tree, path)






def TreeRecMeta (hypInScope : Bool) : Recursor (MetaM' (MetaM' TreeProof)) where
  imp_right p pol tree := Functor.map <| Functor.map <| bindImpRight p none pol tree
  imp_left  p pol tree := Functor.map <| Functor.map <| bindImpLeft  p      pol tree
  and_right p pol tree := Functor.map <| Functor.map <| bindAndRight p none pol tree
  and_left  p pol tree := Functor.map <| Functor.map <| bindAndLeft  p      pol tree

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

      let {boundMVars, binders ..} ← get
      let nonHypMVars := ((assignment.collectMVars {}).result).filter (!boundMVars.contains ·)
      let nonHypBinders ← liftMetaM <| nonHypMVars.mapM mkMetaHypBinder

      let type := mkApp2 (.const ``Tree.Exists [u]) domain tree
      let bindNonHyp := nonHypBinders.foldrM (fun hypBinder => revertHypBinder hypBinder pol type)
      let (bindHyp, binders) := takeHypBinders assignment binders pol type
      let (bindKnownHyp, binders) := if hypInScope then takeKnownHypBinders binders pol type else (pure, binders)

      modify fun s => { s with boundMVars := boundMVars.insertMany nonHypMVars, binders }

      let treeProof ← k
      let treeProof := introMVar mvar.mvarId! name u domain assignment pol tree treeProof
      let treeProof ← bindNonHyp treeProof
      let treeProof ← bindKnownHyp treeProof
      let treeProof ← bindHyp treeProof
      return treeProof


/-
the arguments for a unification are:
hypothesis, and the path and the position in that.
hypContext
goal, with position in that, and polarity.
-/
-- (hypContext : HypothesisContext) (hypothesis goal : Expr) (pol : Bool) (hypPath : List TreeBinderKind) (hypPos goalPos : List Nat)
-- abbrev UnificationProof := List TreeBinderKind → List Nat → Expr → HypothesisContext → List Nat → Bool → Expr → MetaM' TreeProof
abbrev UnificationProof := HypothesisContext → Expr → Expr → Bool →  List TreeBinderKind → List Nat → List Nat → MetaM' TreeProof 

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

      let (p, goal, goalPath, goalPol, useHypProof, hypProof, _hypPol, hyp, hypPath) ← match tree, hypPath, goalPath with
        | imp_pattern p goal, .imp_left ::hypPath, .imp_right::goalPath => pure (p, goal, goalPath,  pol, UseHypImpRight, getHypothesis delete? true (!pol) p hypPath)
        | imp_pattern goal p, .imp_right::hypPath, .imp_left ::goalPath => pure (p, goal, goalPath, !pol, UseHypImpLeft,  getHypothesis delete? false  pol  p hypPath)
        | and_pattern p goal, .and_left ::hypPath, .and_right::goalPath => pure (p, goal, goalPath,  pol, UseHypAndRight, getHypothesis delete? true   pol  p hypPath)
        | and_pattern goal p, .and_right::hypPath, .and_left ::goalPath => pure (p, goal, goalPath,  pol, UseHypAndLeft,  getHypothesis delete? true   pol  p hypPath)
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

def treeApply (hypContext : HypothesisContext) (hypothesis goal : Expr) (pol : Bool) (hypPath : List TreeBinderKind) (hypPos goalPos : List Nat) : MetaM' TreeProof := do
  unless hypPos == [] do    
    throwError m!"cannot apply a subexpression: position {hypPos} in {hypothesis}"
  unless goalPos == [] do
    throwError m!"cannot apply in a subexpression: position {goalPos} in {goal}"
  match hypPath with
  | [] =>
    unless pol do
      throwError m!"cannot apply in negative position"
    let {metaIntro, instMetaIntro, hypProofM} := hypContext
    _ ← metaIntro
    let instMVars ← instMetaIntro
    if ← isDefEq goal hypothesis
    then
      synthMetaInstances instMVars
      let (_hyp, proof) ← hypProofM
      return {proof}
    else 
      throwError m!"couldn't unify hypothesis {hypothesis} with target {goal}"
  
  | _ => throwError "cannot apply a subexpression: subtree {hypPath} in {hypothesis}"

def getApplyPos (hyp : Expr) (goalPath : List TreeBinderKind) : List TreeBinderKind × List Nat :=
  (if PathToPolarity goalPath then getPath hyp else panic! "", [])

open Elab.Tactic

syntax (name := tree_apply) "tree_apply" treePos treePos : tactic

@[tactic tree_apply]
def evalTreeApply : Tactic := fun stx => do
  let hypPos := get_positions stx[1]
  let goalPos := get_positions stx[2]
  workOnTree (applyBound hypPos goalPos true treeApply)

syntax (name := lib_apply) "lib_apply" ident treePos : tactic

@[tactic lib_apply]
def evalLibApply : Tactic := fun stx => do
  let hypName := stx[1].getId
  let goalPos := get_positions stx[2]
  workOnTree (applyUnbound hypName getApplyPos goalPos treeApply)


example (p q : Prop) : ((p → q) ∧ p) → (q → False) → False := by
  make_tree
  tree_apply [0,1,0,1,1] [1,0,1,0,1]
  tree_apply [0,1] [1,0,1,0,1]
  tree_apply [0,1] [1]

def Tree.rfl [Nonempty α] : Tree.Forall α fun a => a = a := IsRefl.refl


example : ({α : Type 0} → {r : α → α → Prop} → [IsRefl α r] → (a : α) → r a a) → 3 = 3 := by
  make_tree
  tree_apply [0,1,1,1,1,1,1,1,1,1] [1]
  -- lib_apply refl [1]
  



        
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
  use default

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

example (p : Prop) : p → p := by
  make_tree
  tree_apply [0,1] [1]



/-
I was wondering what the exact way should be in which quantifiers are handled by the tree apply/rewrite moves.
The simplest example where this is non-trivial is this:
-/

example (p q : Prop) : (p → q ∧ r) → q ∧ (p → r) := by
  make_tree
  tree_apply [0,1,1,1] [1,1,1]
  tree_apply [1,0,1] [1,1]
  exact (sorry : q)

/-
then applying the first r to the second r could have 3 different results that all make some sense:
· q ∧ p ⇨ p
· p ∧ q ⇨ q
· (p ⇨ q) ⇨ q ∧ p ⇨ p

which after a trivial simplification turn into
· q
· p
· (p ⇨ q) ⇨ q

The current version does the first option, but I see arguments for both other versions.
The first two options have the nice property that the order of quantifiers from the hypothesis is maintained.
The third option requires a 'skolemization' of the q in the hypothesis.
The big advantage of the third option is that it is more safe.
-/