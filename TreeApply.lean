import Tree
import PrintTree
import Mathlib.Topology.MetricSpace.Basic
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
  -- FVarIds           : HashSet FVarId                := {}
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
        -- | .free fvar .. => { s with
        --   unusedBinders := s.unusedBinders.push binder
        --   FVarIds := s.FVarIds.insert fvar }
        | _ => { s with
          unusedBinders := s.unusedBinders.push binder
          anyUnknowns := true }



namespace UnfoldHypothesis


structure Context where
  hypProofM : MetaM' (Expr × Expr)
  metaIntro : MetaM (Array Expr) := pure #[]


def Rec : Recursor (ReaderT Context MetaM' α) where
  all name _u domain _inst _pol _tree k := do
    let mvarId ← mkFreshMVarId
    let mvar := .mvar mvarId
    withReader (fun {hypProofM, metaIntro} => {
      metaIntro := return (← metaIntro).push (← mkFreshExprMVarWithId mvarId domain (kind := .synthetic) (userName := name))
      hypProofM := do
        let (forall_pattern name u _domain inst tree, hypProof) ← hypProofM | panic! ""
        let assignment ← instantiateMVars mvar

        if let .mvar mvarId' := assignment then
          modify fun s => let (mvarInfos, duplicate) := s.mvarInfos.insert' mvarId' {name, u, inst}; if duplicate then s else { s with mvarInfos }

        let newMVars := ((assignment.collectMVars {}).result).filter (!(← get).boundMVars.contains ·)
        let newBinders ← liftMetaM <| newMVars.mapM mkMetaHypBinder
        modify fun s => { s with
          boundMVars := s.boundMVars.insertMany newMVars
          binders := s.binders ++ newBinders
          }
        return (tree.instantiate1 assignment, .app hypProof assignment)
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
        addBinder (.free fvarId name u domain inst (mkApp3 (.const ``Classical.choose [u']) domain lamTree hypProof))
        return (tree.instantiate1 fvar, mkApp3 (.const ``Classical.choose_spec [u']) domain lamTree hypProof)
    }) do
    k fvar
    

  imp_right p _pol _tree k := do
    -- let fvarId ← mkFreshFVarId
    -- let fvar := .fvar fvarId
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
    
  imp_left p _pol tree _k := throwError m!"{tree} → {p}: can only move to the right of an implication when unfolding a hypothesis"
  and_left p _pol tree _k := throwError m!"{tree} ∧ {p}: can only move to the right of a conjunction when unfolding a hypothesis"

where
  addBinder (hypBinder : HypBinder) : MetaM' Unit := do
      modify fun s => { s with binders := s.binders.push hypBinder }

def _root_.unfoldHypothesis [Inhabited α] (hypProof : Expr) (tree : Expr) (pos : List TreeNodeKind) (k : Expr → ReaderT Context MetaM' α) : MetaM' α :=
  Rec.recurseM true tree pos (fun _pol => k) |>.run {hypProofM := pure (tree, hypProof)}

-- make a function wich takes the hypothesistree and the hypothesis path. It produces the hypothesis that we will use, and the path inside that, also building the proof.
-- if I make everything one big recursion, then I will need to keep track of the inner TreeProof
end UnfoldHypothesis

def getHypothesisRec (hypPol : Bool) : OptionRecursor (TreeHyp × Bool × Expr × List TreeNodeKind) where
  all _ _ _ _ _ _ _ := none
  ex  _ _ _ _ _ _ _ := none
  imp_right p pol tree k := if  hypPol then none else some <| Bifunctor.fst (ImpRightWithHyp p pol tree) k
  imp_left  p pol tree k := if  hypPol then none else some <| Bifunctor.fst (ImpLeftWithHyp  p pol tree) k
  and_right p pol tree k := if !hypPol then none else some <| Bifunctor.fst (AndRightWithHyp p pol tree) k
  and_left  p pol tree k := if !hypPol then none else some <| Bifunctor.fst (AndLeftWithHyp  p pol tree) k


def getHypothesis (delete? hypPol pol : Bool) (tree : Expr) (path : List TreeNodeKind) : TreeHyp × Bool × Expr × List TreeNodeKind :=
  (getHypothesisRec hypPol).recurse pol tree path fun pol tree path => (MakeHyp delete? pol tree, pol, tree, path)




def TreeRecMeta (hypInScope : Bool) : Recursor (MetaM' (MetaM' TreeProof)) where
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
      let bindNonHyp := nonHypBinders.foldrM (fun hypBinder => revertHypBinder hypBinder pol type)
      let (bindHyp, binders) := takeHypBinders assignment binders pol type
      let (bindKnownHyp, binders) := if hypInScope then takeKnownHypBinders binders pol type else (pure, binders)

      modify fun s => { s with boundMVars := boundMVars.insertMany nonHypMVars, binders }

      let treeProof ← k
      let treeProof := introMVar mvar.mvarId! name u domain inst assignment pol tree treeProof
      let treeProof ← bindNonHyp treeProof
      let treeProof ← bindKnownHyp treeProof
      let treeProof ← bindHyp treeProof
      return treeProof



abbrev UnificationProof := Expr → MetaM (Array Expr) → MetaM' (Expr × Expr) → List Nat → Bool → Expr → MetaM' TreeProof

partial def applyAux (hypProof : Expr) (hypothesis tree : Expr) (pol : Bool) (hypPath goalPath : List TreeNodeKind) (goalPos : List Nat) (unification : UnificationProof)
  : MetaM' (MetaM' TreeProof) :=
  unfoldHypothesis hypProof hypothesis hypPath
    fun hypothesis {hypProofM, metaIntro} =>
      (TreeRecMeta true).recurseM pol tree goalPath
        fun pos tree => do
          let treeProof ← unification hypothesis metaIntro hypProofM goalPos pos tree
          return do (← get).binders.foldrM (fun binder => revertHypBinder binder pol tree) treeProof

partial def applyBound (hypPos goalPos : List Nat) (tree : Expr) (delete? : Bool) (unification : UnificationProof) : MetaM TreeProof := (do
  let hypPath ← positionToPath! hypPos tree
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

      -- let fvarId ← mkFreshFVarId
      withLocalDeclD `hyp hyp fun fvar => do
      let fvarId := fvar.fvarId!
      let treeProofM ← applyAux (.fvar fvarId) hyp goal goalPol hypPath goalPath goalPos unification
      return useHypProof p hypProof pol goal fvarId <$> treeProofM
  
  let x ← treeProofM
  -- logInfo m!"{x.proof}, {indentExpr <$> x.newTree}"
  return x : MetaM' _).run' {}
where
  takeSharedPrefix {α : Type} [BEq α] : List α → List α → List α × List α × List α
  | [], ys => ([], [], ys)
  | xs, [] => ([], xs, [])
  | xs'@(x::xs), ys'@(y::ys) =>
    if x == y
    then Bifunctor.fst (x :: ·) (takeSharedPrefix xs ys)
    else ([], xs', ys')



partial def applyUnbound (hypName : Name) (goalPos : List Nat) (tree : Expr) (unification : UnificationProof) : MetaM TreeProof := (do
  let (goalPath, goalPos) := positionToPath goalPos tree
  let hypProof ← mkConstWithFreshMVarLevels hypName
  let hyp ← makeTreeWithSillyNonemptyInstances (← inferType hypProof)
  logInfo m!"{hyp}"

  let treeProofM ← applyAux hypProof hyp tree true (getPath hyp) goalPath goalPos unification
  treeProofM : MetaM' _).run' {}


def treeApply (hypothesis : Expr) (metaIntro : MetaM (Array Expr)) (proofM : MetaM' (Expr × Expr)) (pos : List Nat) (pol : Bool) (target : Expr) : MetaM' TreeProof := do
  unless pos == [] do
    throwError m!"cannot apply in a subexpression: position {pos} in {target}"
  unless pol do
    throwError m!"cannot apply in negative position"
  _ ← metaIntro
  if ← isDefEq target hypothesis
  then
    let (_hyp, proof) ← proofM
    return {proof}
  else 
    throwError m!"couldn't unify hypothesis {hypothesis} with target {target}"


open Elab Tactic

syntax (name := tree_apply) "tree_apply" treePos treePos : tactic

@[tactic tree_apply]
def evalTreeApply : Tactic := fun stx => do
  let hypPos := get_positions stx[1]
  let goalPos := get_positions stx[2]
  workOnTree (applyBound hypPos goalPos · true treeApply)

syntax (name := lib_apply) "lib_apply" ident treePos : tactic

@[tactic lib_apply]
def evalLibApply : Tactic := fun stx => do
  let hypPos := stx[1].getId
  let goalPos := get_positions stx[2]
  workOnTree (applyUnbound hypPos goalPos · treeApply)


example (p q : Prop) : (p ∧ (p → q)) → (q → False) → False := by
  make_tree
  tree_apply [0,1,1,1] [1,0,1,0,1]
  sorry

def Tree.rfl [Nonempty α] : Tree.Forall fun a : α => a = a := IsRefl.refl
-- set_option pp.all true in
-- example : 3 = 3 := by
--   make_tree
--   lib_apply Tree.rfl []
  
variable (p q r : Prop)



-- def d := Dist.dist (α := ℝ)
example (d : ℝ → ℝ → ℝ) : ∀ f : ℝ → ℝ,
  (∀ ε > 0, ∃ δ > 0, ∀ x y, d x y < δ → d (f x) (f y) < ε) →
  ∀ x, ∀ ε > 0, ∃ δ > 0, ∀ y, d x y < δ → d (f x) (f y) < ε := by
  make_tree
  tree_apply [1,1,0,1,1,1,1,1,1,1,1,1] [1,1,1,1,1,1,1,1,1,1,1]
  tree_apply [1,1,0,1] [1,1,1,0,1]
  tree_apply [1,1,0,1] [1,1,1]


example :
  (∀ hh > 0, 0 < hh) → ∀ ε:Nat,
  0 < ε := by
  make_tree
  tree_apply [0,1,1,1,1] [1,1,1]
  sorry

example (p q : Prop) : (∃ n:Nat, q → p) → ∃ n:Nat, p := by
  make_tree
  tree_apply [0,1,1,1,1] [1,1,1]
  sorry

example (p : Prop) : (∀ _n:Nat, p) → p := by
  make_tree
  tree_apply [0,1,1,1] [1]

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
  
  example (p q : Prop) : (p → q) ∧ p → q := by
  make_tree
  tree_apply [0,1,1] [0,1,0,1,0,1]
  -- q → q
  tree_apply [0,1] [1]

  example (p q : Prop) : (p → q) → p → q := by
  make_tree
  tree_apply [1,0,1] [0,1,0,1]
  -- q → q
  tree_apply [0,1] [1]

example (p : Prop) : p → p := by
  make_tree
  tree_apply [0,1] [1]