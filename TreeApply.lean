import Tree
import PrintTree
import Mathlib

open Tree Lean Meta

inductive HypBinder where
| meta (mvarId : MVarId) (type : Expr) : HypBinder
| free (fvarId : FVarId) (name : Name) (u : Level) (type inst definition : Expr) : HypBinder
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
  inst : Expr

structure HypBinderState where
  binders : Array HypBinder := #[]
  boundMVars : HashSet MVarId := {}
  mvarInfos : HashMap MVarId MvarInfo := {}

abbrev MetaM' := StateRefT HypBinderState MetaM

def bindMVar (mvarId : MVarId) (type : Expr) (pol : Bool) (tree : Expr) (treeProof : TreeProof) : MetaM' TreeProof := do
  match (← get).mvarInfos.find? mvarId with
  | some {name, u, inst} => return bindMVarWithInst mvarId type name u inst pol tree treeProof
  | none =>
    let name ← mkFreshUserName `m -- in the future make a more sophisticated name generator
    let u' ← getLevel type
    let u ← decLevel u'
    if let some inst ← synthInstance? (mkApp (.const ``Nonempty [u']) type)
      then return bindMVarWithInst mvarId type name u inst pol tree treeProof
    else
      return bindMVarWithoutInst mvarId type name u pol tree treeProof


def revertHypBinder : HypBinder → Bool → Expr → TreeProof → MetaM' TreeProof
| .meta mvar type => bindMVar mvar type
| .free fvar name u type inst definition => (return bindFVar fvar name u type inst definition · · ·)
| .unknown fvar type     => (return bindUnknown type fvar · · ·)
| .known definition type => (return bindKnown type definition · · ·)


namespace takeHypBinders

structure State where
  visitedExpr  : ExprSet      := {}
  FVarIds      : HashSet FVarId := {}
  MVarIds      : HashSet MVarId := {}
  anyFVars     : Bool := false
  unusedBinders   : Array HypBinder := #[]

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

def _root_.takeHypBinders (mvarAssignment : Expr) (binders : Array HypBinder) (pol : Bool) (tree : Expr) : (TreeProof → MetaM' TreeProof) × Array HypBinder :=
  let (treeProofFunc, s) := go.run (visit mvarAssignment {})
  (treeProofFunc, s.unusedBinders)
where
  go : StateM State (TreeProof → MetaM' TreeProof) :=
    binders.foldl (init := pure pure) fun unusedBinders binder => do
      let s ← get
      match binder with
      | .meta mvar (type := type) .. =>
        let isUsed := s.anyFVars || s.MVarIds.contains mvar
        push binder type isUsed unusedBinders
      | .free fvar (type := type) .. =>
        let isUsed := s.FVarIds.contains fvar
        if isUsed then
          set { s with anyFVars := true}
        push binder type isUsed unusedBinders
      | .unknown (type := type) .. =>
        let isUsed := s.anyFVars
        push binder type isUsed unusedBinders

      | .known (type := type) .. =>
        let isUsed := s.anyFVars
        push binder type isUsed unusedBinders
    
  push (binder : HypBinder) (type : Expr) (isUsed : Bool) (treeProofFuncM : StateM State (TreeProof → MetaM' TreeProof)) : StateM State (TreeProof → MetaM' TreeProof) := do
    if isUsed
    then
      modify (visit type)
      let treeProofFunc ← treeProofFuncM
      return revertHypBinder binder pol tree >=> treeProofFunc
    else
      let treeProofFunc ← treeProofFuncM
      modify (fun s => { s with unusedBinders := s.unusedBinders.push binder})
      return treeProofFunc

end takeHypBinders



namespace UnfoldHypothesis


structure Context where
  hypProofM : MetaM' (Expr × Expr)
  metaIntro : MetaM Unit := pure ()


def Rec : Recursor (ReaderT Context MetaM' (MetaM' TreeProof)) where
  all name _u domain _inst _pol _tree k := do
    let mvarId ← mkFreshMVarId
    let mvar := .mvar mvarId
    withReader (fun {hypProofM, metaIntro} => {
      metaIntro := do
        metaIntro
        _ ← mkFreshExprMVarWithId mvarId domain (kind := .synthetic) (userName := name)
      hypProofM := do
        let (forall_pattern name u _domain inst tree, hypProof) ← hypProofM | panic! ""
        let assignment ← instantiateMVars mvar
        let tree := tree.instantiate1 assignment

        if let .mvar mvarId' := assignment then
          modify fun s => let (mvarInfos, duplicate) := s.mvarInfos.insert' mvarId' {name, u, inst}; if duplicate then s else { s with mvarInfos }

        let newMVars := ((assignment.collectMVars {}).result).filter (!(← get).boundMVars.contains ·)
        let newBinders ← liftMetaM <| newMVars.mapM mkMetaHypBinder
        modify fun s => { s with
          boundMVars := s.boundMVars.insertMany newMVars
          binders := s.binders ++ newBinders
          }
        return (tree, .app hypProof assignment)
      }) do
    k mvar
    

  ex name u domain _inst _pol _tree k := do
    withLocalDeclD name domain fun fvar => do
    let fvarId := fvar.fvarId!
    let u' := .succ u
    withReader (fun c => { c with
      hypProofM := do
        let (exists_pattern name u domain inst tree, hypProof) ← c.hypProofM | panic! ""
        let lamTree := .lam name domain tree .default
        let tree := tree.instantiate1 fvar
        addBinder (.free fvarId name u domain inst (mkApp3 (.const ``Classical.choose [u']) domain lamTree hypProof))
        return (tree, mkApp3 (.const ``Classical.choose_spec [u']) domain lamTree hypProof)
    }) do
    k fvar
    

  imp_right _p _pol _tree k := do
    let fvarId ← mkFreshFVarId
    let fvar := .fvar fvarId
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
    
  imp_left p _pol tree _k := throwError m!"{tree} → {p}: can only move to the right of an implication when unfolding a hypothesis"
  and_left p _pol tree _k := throwError m!"{tree} ∧ {p}: can only move to the right of a conjunction when unfolding a hypothesis"

where
  addBinder (hypBinder : HypBinder) : MetaM' Unit := do
      modify fun s => { s with binders := s.binders.push hypBinder }

def _root_.unfoldHypothesis (hypProof : Expr) (pol : Bool) (tree : Expr) (pos : List TreeNodeKind) (k : Expr → ReaderT Context MetaM' (MetaM' TreeProof)) : MetaM' (MetaM' TreeProof) :=
  Rec.recM pol tree pos (fun _pol => k) |>.run {hypProofM := pure (tree, hypProof)}


end UnfoldHypothesis


-- abbrev M {m : Type → Type}:= m (MetaM' TreeProof)


--  {m : Type → Type} [Monad m] [MonadControlT MetaM m] [MonadLiftT MetaM m] 
def introMetaBinders: Recursor (MetaM' (MetaM' TreeProof)) where
  imp_right p pol tree := Functor.map <| Functor.map <| bindImpRight p none pol tree
  imp_left  p pol tree := Functor.map <| Functor.map <| bindImpLeft  p      pol tree
  and_right p pol tree := Functor.map <| Functor.map <| bindAndRight p none pol tree
  and_left  p pol tree := Functor.map <| Functor.map <| bindAndLeft  p      pol tree

  all name u domain inst pol :=
    if pol
    then
      introFree name u domain inst pol bindForall
    else 
      introMeta name u domain inst pol

  ex name u domain inst pol := 
    if pol 
    then
      introMeta name u domain inst pol
    else
      introFree name u domain inst pol bindExists
where
  introFree (name : Name) (u : Level) (domain inst : Expr) (pol : Bool)
      (bind : Name → Level → Expr → Expr → Expr → Bool → Expr → TreeProof → TreeProof) (tree : Expr) (k : Expr → MetaM' (MetaM' TreeProof)) : MetaM' (MetaM' TreeProof) :=
    withLocalDeclD (`fvar ++ name) domain fun fvar => do
    let treeProofM ← k fvar
    return bind name u domain inst fvar pol tree <$> treeProofM

  introMeta (name : Name) (u : Level) (domain inst : Expr) (pol : Bool) (tree : Expr)
   (k : Expr → MetaM' (MetaM' TreeProof)) : MetaM' (MetaM' TreeProof) := do
    let mvar ← mkFreshExprMVar domain .synthetic (`mvar ++ name)
    let k ← k mvar
    let assignment ← instantiateMVars mvar
    if let .mvar mvarId' := assignment then
      modify fun s => { s with mvarInfos := s.mvarInfos.insert mvarId' {name, u, inst} }
      
    return do

      let {boundMVars, binders ..} ← get
      let nonHypMVars := ((assignment.collectMVars {}).result).filter (!boundMVars.contains ·)
      let nonHypBinders ← liftMetaM <| nonHypMVars.mapM mkMetaHypBinder

      let type := mkApp3 (.const ``Tree.Exists [u]) domain inst tree
      let bindNonHyp := nonHypBinders.foldl (init := pure) (fun arrow hypBinder => revertHypBinder hypBinder pol type >=> arrow)
      let (bindHyp, binders) := takeHypBinders assignment binders pol type

      modify fun s => { s with boundMVars := boundMVars.insertMany nonHypMVars, binders }

      let treeProof ← k
      let treeProof := introMVar mvar.mvarId! u domain inst assignment pol tree treeProof
      let treeProof ← bindNonHyp treeProof
      let treeProof ← bindHyp treeProof
      return treeProof

def List.takeSharedPrefix [BEq α]: List α → List α → List α × List α × List α
| [], ys => ([], [], ys)
| xs, [] => ([], xs, [])
| xs'@(x::xs), ys'@(y::ys) => if x == y
  then Bifunctor.fst (x :: ·) (takeSharedPrefix xs ys)
  else ([], xs', ys')

abbrev UnificationProof := Expr → MetaM' (Expr × Expr) → List Nat → Bool → Expr → MetaM' TreeProof

partial def applyAux (hypProof : Expr) (hypothesis tree : Expr) (pol : Bool) (hypPath goalPath : List TreeNodeKind) (goalPos : List Nat) (unification : UnificationProof) :
  MetaM' (MetaM' TreeProof) := do
  let result ← unfoldHypothesis hypProof pol hypothesis hypPath
    fun hypothesis {hypProofM, metaIntro} => do
      let result ← introMetaBinders.recM pol tree goalPath
        fun pos tree => (do
          metaIntro
          let treeProof ← unification hypothesis hypProofM goalPos pos tree
          return (do
            let mut treeProof ← instantiateTreeMVars treeProof
            for binder in (← get).binders.reverse do
              treeProof ← revertHypBinder binder pol tree treeProof
            return treeProof))
      return result

  return result

-- see private Lean.Meta.mkFun
partial def applyUnbound (hypName : Name) (goalPos : List Nat) (tree : Expr) (unification : UnificationProof) : MetaM TreeProof := (do
  let (goalPath, goalPos) := positionToNodes goalPos tree
  let cinfo ← getConstInfo hypName
  let us ← cinfo.levelParams.mapM fun _ => mkFreshLevelMVar
  let hypProof := mkConst hypName us
  let hyp ← Core.instantiateTypeLevelParams cinfo us
  let hyp ← makeTree hyp
  let nodes := getNodes hyp

  let treeProofM ← applyAux hypProof hyp tree true nodes goalPath goalPos unification
  treeProofM : MetaM' _).run' {}

partial def applyBound (hypPos goalPos : List Nat) (tree : Expr) (delete : Bool) (unification : UnificationProof) : MetaM TreeProof := (do
  let hypPath ← positionToNodes! hypPos tree
  let (goalPath, goalPos) := positionToNodes goalPos tree
  let (path, hypPath, goalPath) := hypPath.takeSharedPrefix goalPath
  let treeProofM ← introMetaBinders.recM true tree path
    fun pol tree => do

      let hypFVarId ← mkFreshFVarId

        
      match tree, hypPath, goalPath with
      | imp_pattern p tree, .imp_left::hypPath, .imp_right::goalPath => do
        let treeProofM ← applyAux (.fvar hypFVarId) p tree pol hypPath goalPath goalPos unification
        return bindUsedImp p hypFVarId delete pol tree <$> treeProofM
      -- | and_pattern p tree, .and_left::hypPath, .and_right::goalPath =>
      --   (Functor.map <| Functor.map <| bindUsedAnd p hypFVarId false pol tree) (go p tree hypPath goalPath)
      | _, _, _ => throwError m!"cannot have hypothesis at {hypPath} and goal at {goalPath} in {tree}"
  
  let x ← treeProofM
  -- logInfo m!"{x.proof}, {indentExpr <$> x.newTree}"
  return x : MetaM' _).run' {}


def defaultUnification (hypothesis : Expr) (proofM : MetaM' (Expr × Expr)) (pos : List Nat) (_pol : Bool) (target : Expr) : MetaM' TreeProof := do
  unless pos == [] do
    throwError m!"cannot apply in a subexpression: position {pos} in {target}"
  if ← isDefEq target hypothesis
  then
    let (_hyp, proof) ← proofM
    return {proof}
  else 
    throwError m!"couldn't unify hypothesis {hypothesis} with target {target}"



open Elab Tactic

syntax (name := tree_apply) "tree_apply" treePos treePos : tactic

@[tactic tree_apply]
def evalRewriteSeq : Tactic := fun stx => do
  let hypPos := get_positions stx[1]
  let goalPos := get_positions stx[2]
  workOnTree (applyBound hypPos goalPos · true defaultUnification)


-- set_option pp.explicit true
def d := Dist.dist (α := ℝ)
example : ∀ f : ℝ → ℝ,
  (∀ ε > 0, ∃ δ, ∀ x y, d x y < δ → d (f x) (f y) < ε) →
  ∀ x, ∀ ε > 0, ∃ δ, ∀ y, d x y < δ → d (f x) (f y) < ε := by
  make_tree
  tree_apply [1,1,0,1,1,1,1,1,1,1,1] [1,1,1,1,1,1,1,1,1,1]
  tree_apply [1,1,1,1,1,1,0,1] [1,1,1,1,1,1,1]

  
  
  
-- set_option pp.explicit true
example : --∀ f : ℝ → ℝ,
  (∀ hh > 0, 0 < hh) → ∀ ε:Nat,
  0 < ε := by
  make_tree
  tree_apply [0,1,1,1,1] [1,1,1]
  sorry

example (p q : Prop) : (∃ n:Nat, q → p) → ∃ n:Nat, p := by
  make_tree
  tree_apply [0,1,1,1,1] [1,1,1]
  sorry

example (p : Prop) : (∀ n:Nat, p) → p := by
  make_tree
  tree_apply [0,1,1,1] [1]

example (p : Nat → Prop): (∀ m, (1=1 → p m)) → ∀ m:Nat, p m := by
  make_tree
  tree_apply [0,1,1,1,1] [1,1,1]
  -- ∀ m, 1 = 1
  exact fun _ => rfl

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
