import Lean
import Mathlib.Logic.Basic
import Mathlib.Control.Bifunctor

namespace Tree

def Imp (p q : Prop) := p → q
def And (p q : Prop) := p ∧ q

def Imp' {p : Prop} (q : p → Prop) := ∀ h : p, q h
def And' {α : Prop} (β : α → Prop) := ∃ a : α, β a

def Forall {α : Type u} [Nonempty α] (p : α → Prop) : Prop := ∀ a : α, p a
def Exists {α : Type u} [Nonempty α] (p : α → Prop) : Prop := ∃ a : α, p a



open Lean Meta


structure TreeProof where
  newTree : Option Expr := none
  proof : Expr
deriving Inhabited

structure ClosedTreeProof where
  proof : Expr


section nonDependent

private def bindPropBinder (p : Expr) (fvar? : Option FVarId) (isImp : Option Bool) (isRev : Bool) (imp_lemma imp_lemma' close_lemma close_lemma' : Name) (pol : Bool) (tree : Expr) : TreeProof → TreeProof :=
  fun {newTree, proof} =>
  let proof := match fvar? with
    | none => proof
    | some fvar => .lam `h p (proof.abstract #[.fvar fvar]) .default
  match newTree with
  | none =>
    let isClosedProof := match isImp with
      | none => true
      | some isImp => isImp == pol
    {
    newTree := if isClosedProof then none else p,
    proof := mkApp3 (.const (if pol then close_lemma else close_lemma') []) p tree proof}

  | some newTree => {
    newTree := match isImp with | none => newTree | some isImp => (if isRev then Function.swap else id) (mkApp2 (.const (if isImp then ``Imp else ``And) [])) p newTree,
    proof := mkApp4 (.const (if pol then imp_lemma else imp_lemma') []) p tree newTree proof}

variable {p old new : Prop}

lemma imp_right  (h : new → old) : Imp p new → Imp p old := (h ∘ ·)
lemma imp_right' (h : old → new) : Imp p old → Imp p new := (h ∘ ·)
lemma closed_imp_right  (h : old) : Imp p old     := fun _hp => h

lemma imp_dep  (h : p → new → old) : Imp p new → Imp p old := fun g hp => h hp (g hp)
lemma imp_dep' (h : p → old → new) : Imp p old → Imp p new := fun g hp => h hp (g hp)
lemma closed_imp_dep  (h : p → old) : Imp p old     := h

def bindImpRight (p : Expr) (fvar? : Option FVarId) : Bool → Expr → TreeProof → TreeProof :=
  if fvar? == none 
  then bindPropBinder p fvar? true false ``imp_right ``imp_right' ``closed_imp_right .anonymous
  else bindPropBinder p fvar? true false ``imp_dep   ``imp_dep'   ``closed_imp_dep   .anonymous

lemma and_right  (h : new → old) : And p new → And p old := And.imp_right h
lemma and_right' (h : old → new) : And p old → And p new := And.imp_right h
lemma closed_and_right  (h : old) : p → And p old := fun hp => ⟨hp, h⟩

lemma and_dep  (h : p → new → old) : And p new → And p old := fun ⟨hp, g⟩ => ⟨hp, h hp g⟩
lemma and_dep' (h : p → old → new) : And p old → And p new := fun ⟨hp, g⟩ => ⟨hp, h hp g⟩
lemma closed_and_dep  (h : p → old) : p → And p old := fun hp => ⟨hp, h hp⟩

def bindAndRight (p : Expr) (fvar? : Option FVarId) : Bool → Expr → TreeProof → TreeProof :=
  if fvar? == none 
  then bindPropBinder p fvar? false false ``and_right ``and_right' ``closed_and_right .anonymous
  else bindPropBinder p fvar? false false ``and_dep   ``and_dep'   ``closed_and_dep   .anonymous

lemma imp_left   (h : old → new) : Imp new p → Imp old p := (· ∘ h)
lemma imp_left'  (h : new → old) : Imp old p → Imp new p := (· ∘ h)
lemma closed_imp_left'  (h : old) : Imp old p → p := fun g => g h

def bindImpLeft (p : Expr) : Bool → Expr → TreeProof → TreeProof :=
  bindPropBinder p none true true ``imp_left ``imp_left' .anonymous ``closed_imp_left'

lemma and_left   (h : new → old) : And new p → And old p := And.imp_left h
lemma and_left'  (h : old → new) : And old p → And new p := And.imp_left h
lemma closed_and_left   (h : old) : p → And old p := fun hp => ⟨h, hp⟩

def bindAndLeft (p : Expr) : Bool → Expr → TreeProof → TreeProof :=
  bindPropBinder p none false true ``and_left ``and_left' ``closed_and_left .anonymous


lemma imp_use  (h : p → new → old) : new → Imp p old := fun g hp => h hp g
alias closed_imp_dep ← closed_imp_use

def bindUsedImp (p : Expr) (fvar : FVarId) (delete? : Bool) (pol : Bool) : Expr → TreeProof → TreeProof := 
  if delete? && pol
  then bindPropBinder p fvar none false ``imp_use .anonymous ``closed_imp_use .anonymous pol
  else bindImpRight p fvar pol


lemma and_make  (h : p → new → old) : And p new → old := fun ⟨g, f⟩ => h g f
lemma imp_make' (h : p → old → new) : old → Imp p new := fun g f => h f g
lemma closed_and_make  (h : p → old) : p → old := h

def bindUnknown (p : Expr) (fvar : FVarId) (pol : Bool) : Expr → TreeProof → TreeProof :=
  bindPropBinder p fvar (!pol) false ``and_make ``imp_make' ``closed_and_make .anonymous pol


lemma imp_make  (hp : p) (h : new → old) : Imp p new → old := fun g => h (g hp)
lemma and_make' (hp : p) (h : old → new) : old → And p new := fun g => ⟨hp, h g⟩

def bindKnown (p definition : Expr) (pol : Bool) (tree : Expr) : TreeProof → TreeProof :=
  fun {newTree, proof} => match newTree with
  | some newTree => {
    newTree := mkApp2 (.const (if pol then ``Imp else ``And) []) p newTree,
    proof := mkApp5 (.const (if pol then ``imp_make else ``and_make') []) p tree newTree definition proof}
  | none => {proof}

end nonDependent




section typeBinders
variable {α : Type u} [inst : Nonempty α] {old new : α → Prop}

def bindTypeBinder (name : Name) (u : Level) (domain inst var : Expr) (isForall : Option Bool) (imp_lemma imp_lemma' close_lemma close_lemma' : Name) (pol : Bool) (tree : Expr) : TreeProof → TreeProof :=
  fun {newTree, proof} =>
  let mkLam b := .lam name domain (b.abstract #[var]) .default
  let proof   := mkLam proof
  match newTree with
  | none => {proof := mkApp4 (.const (if pol then close_lemma else close_lemma') [u]) domain inst tree proof}
  | some newTree =>
    let newTree := mkLam newTree
    {
    newTree := match isForall with
      | none => newTree
      | some isForall => mkApp3 (.const (if isForall then ``Forall else ``Exists) [u]) domain inst newTree,
    proof := mkApp5 (.const (if pol then imp_lemma else imp_lemma') [u]) domain inst tree newTree proof}


lemma forall_imp  (h : ∀ a, new a → old a) : Forall new → Forall old := _root_.forall_imp h
lemma forall_imp' (h : ∀ a, old a → new a) : Forall old → Forall new := _root_.forall_imp h
lemma closed_forall_imp (h : ∀ a, old a) : Forall old := h
lemma closed_forall_imp' (h : ∀ a, ¬ old a) : ¬ Forall old := let ⟨a⟩ := inst; fun g => h a (g a)

def bindForall (name : Name) (u : Level) (domain inst var : Expr) : Bool → Expr → TreeProof → TreeProof :=
  bindTypeBinder name u domain inst var true ``forall_imp ``forall_imp' ``closed_forall_imp ``closed_forall_imp'

lemma exists_imp  (h : ∀ a, new a → old a) : Exists new → Exists old := Exists.imp h
lemma exists_imp' (h : ∀ a, old a → new a) : Exists old → Exists new := Exists.imp h
lemma closed_exists_imp (h : ∀ a, old a) : Exists old := let ⟨a⟩ := inst; ⟨a, h a⟩
lemma closed_exists_imp' (h : ∀ a, ¬ old a) : ¬ Exists old := fun ⟨a, ha⟩ => h a ha

def bindExists (name : Name) (u : Level) (domain inst var : Expr) : Bool → Expr → TreeProof → TreeProof :=
  bindTypeBinder name u domain inst var false ``exists_imp ``exists_imp' ``closed_exists_imp ``closed_exists_imp'


variable {old : Prop} {new : α → Prop}

lemma forall_make  (a : α) (h : new a → old) : Forall new → old := fun g => h (g a)
lemma exists_make' (a : α) (h : old → new a) : old → Exists new := fun g => ⟨a, h g⟩

def bindFVar (fvar : FVarId) (name : Name) (u : Level) (domain inst definition : Expr) (pol : Bool) (tree : Expr) : TreeProof → TreeProof :=
  fun {newTree, proof} => match newTree with
  | none => {proof}
  | some newTree =>
    let mkLam b := .lam name domain (b.abstract #[.fvar fvar]) .default
    let newTree := mkLam newTree
    {
    newTree := mkApp3 (.const (if pol then ``Forall      else ``Exists      ) [u]) domain inst newTree,
    proof   := mkApp6 (.const (if pol then ``forall_make else ``exists_make') [u]) domain inst tree newTree definition proof}

lemma forall_make' (h : ∀ a, old → new a) : old → Forall new := fun g a => h a g
lemma exists_make  (h : ∀ a, new a → old) : Exists new → old := fun ⟨a, g⟩ => h a g

-- in the case where we close the goal, we need to use the instance to show that the metavariable can indeed be filled in.

def bindMVarWithInst (mvarId : MVarId) (type : Expr) (name : Name) (u : Level) (inst : Expr) (pol : Bool) (tree : Expr) : TreeProof → TreeProof := 
  fun treeProof@{newTree, proof} => match newTree with
  | none => {proof := proof.replaceFVar (.mvar mvarId) (mkApp2 (.const ``Classical.choice [.succ u]) type inst)}
  | some _ =>
  bindTypeBinder name u type inst (.mvar mvarId) (!pol) ``exists_make ``forall_make' .anonymous .anonymous pol tree treeProof

lemma instance_forall_make' (h : ∀ a, old → new a) : old → Imp' (fun inst => @Forall α inst new) := fun g _ a => h a g
lemma instance_exists_make  (h : ∀ a, new a → old) : And' (fun inst => @Exists α inst new) → old := fun ⟨_, a, g⟩ => h a g

lemma instance_choose_mvar  (h : ∀ _ : α, old  ) : Nonempty α → old   := fun   inst => h (Classical.choice inst)
lemma instance_choose_mvar' (h : ∀ _ : α, ¬ old) : old → ¬ Nonempty α := fun g inst => h (Classical.choice inst) g

def bindMVarWithoutInst (mvarId : MVarId) (type : Expr) (name : Name) (u : Level) (pol : Bool) (tree : Expr) : TreeProof → TreeProof := 
  fun {newTree, proof} => match newTree with
  | none => panic! "still have to implement"
  | some newTree =>
    let mkLam b := .lam name type (b.abstract #[.mvar mvarId]) .default
    let newTree := mkLam newTree
    let proof   := mkLam proof
    {
      newTree := mkApp2 (.const (if pol then ``Tree.Exists          else ``Forall               ) [u]) type newTree,
      proof   := mkApp4 (.const (if pol then ``instance_exists_make else ``instance_forall_make') [u]) type tree newTree proof}




variable {old : α → Prop} {new : Prop}

-- this is for (assigned) metavariables that come from the target
lemma destroy_exists (a : α) (h : new → old a) : new → Exists old := fun g => ⟨a, h g⟩
lemma destroy_forall (a : α) (h : old a → new) : Forall old → new := fun g => h (g a)

lemma closed_destroy_exists (a : α) (h : old a) : Exists old := ⟨a, h⟩
lemma closed_destroy_forall (a : α) (h : ¬ old a) : ¬ Forall old := fun g => h (g a)

def introMVar (mvarId : MVarId) (u : Level) (type inst assignment : Expr) (pol : Bool) (tree : Expr) : TreeProof → TreeProof :=
  fun {newTree, proof} =>
  let instantiateMVar e := e.replaceFVar (.mvar mvarId) assignment
  let proof := instantiateMVar proof
  match newTree with
  | none => {proof := mkApp5 (.const (if pol then ``closed_destroy_exists else ``closed_destroy_forall) [u]) type inst tree assignment proof}
  | some newTree =>
    let newTree := instantiateMVar newTree
    {newTree, proof := mkApp6 (.const (if pol then ``destroy_exists else ``destroy_forall) [u]) type inst tree newTree assignment proof}

def instantiateTreeMVars (treeProof : TreeProof) : MetaM TreeProof :=
  return {
    newTree := ← match treeProof.newTree with
      | none => pure none
      | some newTree => some <$> instantiateMVars newTree
    proof := ← instantiateMVars treeProof.proof
  }

end typeBinders


@[match_pattern]
def imp_pattern (p q : Expr) : Expr :=
  mkApp2 (.const ``Imp []) p q
@[match_pattern]
def and_pattern (p q : Expr) : Expr :=
  mkApp2 (.const ``And []) p q
@[match_pattern]
def regular_and_pattern (p q : Expr) : Expr :=
  mkApp2 (.const `And []) p q

@[match_pattern]
def imp'_pattern (name : Name) (u : Level) (domain : Expr) {domain' : Expr} (inst body : Expr) : Expr :=
  mkApp3 (.const ``Imp' [u]) domain' inst (.lam name domain body .default)
@[match_pattern]
def and'_pattern (name : Name) (u : Level) (domain : Expr) {domain' : Expr} (inst body : Expr) : Expr :=
  mkApp3 (.const ``And' [u]) domain' inst (.lam name domain body .default)

@[match_pattern]
def forall_pattern (name : Name) (u : Level) (domain : Expr) {domain' : Expr} (inst body : Expr) : Expr :=
  mkApp3 (.const ``Forall [u]) domain' inst (.lam name domain body .default)
@[match_pattern]
def exists_pattern (name : Name) (u : Level) (domain : Expr) {domain' : Expr} (inst body : Expr) : Expr :=
  mkApp3 (.const ``Exists [u]) domain' inst (.lam name domain body .default)
@[match_pattern]
def regular_exists_pattern (name : Name) (u : Level) (domain : Expr) {domain' : Expr} (body : Expr) (bi : BinderInfo) : Expr :=
  mkApp2 (.const `Exists [u]) domain' (.lam name domain body bi)


structure Recursor (α : Type u) where
  all (name : Name) (u : Level) (domain inst : Expr) : Bool → Expr → (Expr → α) → α
  ex  (name : Name) (u : Level) (domain inst : Expr) : Bool → Expr → (Expr → α) → α

  imp_right (p : Expr) : Bool → Expr → α → α
  and_right (p : Expr) : Bool → Expr → α → α
  imp_left  (p : Expr) : Bool → Expr → α → α
  and_left  (p : Expr) : Bool → Expr → α → α

inductive TreeNodeKind where
  | imp_right
  | and_right
  | imp_left
  | and_left
  | all
  | ex
deriving BEq
instance : ToString TreeNodeKind where
  toString := fun 
    | .imp_right => ".. →"
    | .and_right => ".. ∧"
    | .imp_left => "→ .."
    | .and_left => "∧ .."
    | .all => "∀"
    | .ex => "∃"

partial def Recursor.recM [Inhabited α] [Monad m] [MonadError m] (r : Recursor (m α)) (pol : Bool := true) (tree : Expr) (pos : List TreeNodeKind) (k : Bool → Expr → m α) : m α :=
  let rec visit [Inhabited α] (pol : Bool) : List TreeNodeKind → Expr → m α  
    | .all::xs, forall_pattern n u α i b => r.all n u α i pol (.lam n α b .default) (fun a => visit pol xs (b.instantiate1 a))
    | .ex::xs, exists_pattern n u α i b => r.ex  n u α i pol (.lam n α b .default) (fun a => visit pol xs (b.instantiate1 a))
    | .imp_right::xs,    imp_pattern p tree => r.imp_right p pol tree (visit   pol  xs tree)
    | .and_right::xs,    and_pattern p tree => r.and_right p pol tree (visit   pol  xs tree)
    | .imp_left::xs, imp_pattern tree p => r.imp_left  p pol tree (visit (!pol) xs tree)
    | .and_left::xs, and_pattern tree p => r.and_left  p pol tree (visit   pol  xs tree)
    | [], e => k pol e
    | xs, e => throwError m!"could not tree-recurse to position {xs} in term {e}"
  visit pol pos tree



-- this is more efficient, as it doesn't require instantiation of the loose bound variables.
def positionToNodesAndPolarities : List Nat → Expr → List (TreeNodeKind × Bool) × List Nat :=
  let rec visit (pol : Bool) : List Nat → Expr → List (TreeNodeKind × Bool) × List Nat
    | 1::1::xs, forall_pattern (body := tree) .. => Bifunctor.fst (List.cons (.all      , pol)) <| visit   pol  xs tree
    | 1::1::xs, exists_pattern (body := tree) .. => Bifunctor.fst (List.cons (.ex       , pol)) <| visit   pol  xs tree
    | 1::xs,    imp_pattern _ tree               => Bifunctor.fst (List.cons (.imp_right, pol)) <| visit   pol  xs tree
    | 1::xs,    and_pattern _ tree               => Bifunctor.fst (List.cons (.and_right, pol)) <| visit   pol  xs tree
    | 0::1::xs, imp_pattern tree _               => Bifunctor.fst (List.cons (.imp_left , pol)) <| visit (!pol) xs tree
    | 0::1::xs, and_pattern tree _               => Bifunctor.fst (List.cons (.and_left , pol)) <| visit   pol  xs tree
    | xs, _ => ([], xs)
  visit true

def positionToNodes (pos : List Nat) (tree : Expr) : List (TreeNodeKind) × List Nat :=
  (Bifunctor.fst <| List.map Prod.fst) (positionToNodesAndPolarities pos tree)

def positionToNodes! [Monad m] [MonadError m] (pos : List Nat) (tree : Expr) : m (List (TreeNodeKind)) :=
  match positionToNodes pos tree with
  | (nodes, []) => return nodes
  | _ => throwError m!"could not tree-recurse to position {pos} in term {tree}"

def getNodes : Expr → List TreeNodeKind
  | forall_pattern (body := tree) .. => .all       :: getNodes tree
  | exists_pattern (body := tree) .. => .ex        :: getNodes tree
  | imp_pattern _ tree               => .imp_right :: getNodes tree
  | and_pattern _ tree               => .and_right :: getNodes tree
  | _ => []

def nodesToPosition (nodes : List TreeNodeKind) : List Nat :=
  (nodes.map fun | .imp_left | .and_left => [0,1] | _ => [1]).join


partial def makeTree : Expr → MetaM Expr
  | e@(.forallE name domain body _bi) =>
      withLocalDeclD name domain fun fvar => do
      let body' := body.instantiate1 fvar
      let u' ← getLevel domain
      match ← decLevel? u' with
      | none => 
        unless ← isProp body' do
          return e
        if body.hasLooseBVars
        then
          return mkApp2 (.const ``Imp' []) domain (.lam name domain ((← makeTree body').abstract #[fvar]) .default)
        else
          return mkApp2 (.const ``Imp []) (← makeTree domain) (← makeTree body)

      | some u =>
        if let some inst ← synthInstance? (mkApp (.const ``Nonempty [u']) domain)
        then
          return mkApp3 (.const ``Forall [u]) domain inst (.lam name domain ((← makeTree body').abstract #[fvar]) .default)
        else
          return e

  | regular_and_pattern p q =>
      return mkApp2 (.const ``And []) (← makeTree p) (← makeTree q)

  | e@(regular_exists_pattern name u' domain body _bi) =>
      withLocalDeclD name domain fun fvar => do
      let body' := body.instantiate1 fvar
      match ← decLevel? u' with
      | none =>
        unless ← isProp body' do
          return e
        return mkApp2 (.const ``And' []) domain (.lam name domain ((← makeTree body').abstract #[fvar]) .default)

      | some u =>
        if let some inst ← synthInstance? (mkApp (.const ``Nonempty [u']) domain)
        then
          return mkApp3 (.const ``Exists [u]) domain inst (.lam name domain ((← makeTree body').abstract #[fvar]) .default)
        else
          return e
  | e => return e

open Elab Tactic


elab "make_tree" : tactic => do
  replaceMainGoal [← (← getMainGoal).change (← makeTree (← getMainTarget))]

#eval 3/2
syntax treePos := "[" num,* "]"

def get_positions (stx : Syntax) : List Nat :=
  let stx := stx[1].getArgs.toList
  match stx with
  | [] => []
  | x :: xs =>
    let rec go : List Syntax → List Nat
      | [] => []
      | _ :: y :: ys => TSyntax.getNat ⟨y⟩ :: go ys
      | _ => panic! "even length nonempy list"
    TSyntax.getNat ⟨x⟩ :: go xs


def workOnTree (move : Expr → MetaM TreeProof) : TacticM Unit := do
  Term.withSynthesize <| withMainContext do
    let {newTree, proof} ← move (← getMainTarget)
    match newTree with
    | none =>
      unless ← isTypeCorrect proof do
        throwError m!"closing the goal does not type check{indentExpr proof}"
      (← getMainGoal).assign proof
      replaceMainGoal []

    | some newTree =>
      let mvarNew  ← mkFreshExprSyntheticOpaqueMVar newTree
      let proof  := .app proof mvarNew
      unless ← isTypeCorrect proof do 
        throwError m!"changing the goal does not type check{indentExpr proof}"
      (← getMainGoal).assign proof
      replaceMainGoal [mvarNew.mvarId!]




set_option pp.funBinderTypes true
example : ∀ n : Nat, ∃ m : Int, n = m → True ∧ ∀ n : Nat, ∃ m : Int, n = m → True ∧ False := by
  make_tree
  sorry

example {p : Nat → Nat → Nat → Prop }: (∀ a,∃ b,  ∀ c, p a b c ) → ∀ a, ∀ c, ∃ b, p a b c  := by
  make_tree
  sorry
