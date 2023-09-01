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
    proof := mkApp3 (.const (if pol then close_lemma else close_lemma') []) p tree proof }

  | some newTree => {
    newTree := match isImp with | none => newTree | some isImp => (if isRev then Function.swap else id) (mkApp2 (.const (if isImp then ``Imp else ``And) [])) p newTree,
    proof := mkApp4 (.const (if pol then imp_lemma else imp_lemma') []) p tree newTree proof }

variable {p : Prop} {old new : Prop}

lemma imp_right  (h : new → old) : Imp p new → Imp p old := (h ∘ ·)
lemma imp_right' (h : old → new) : Imp p old → Imp p new := (h ∘ ·)
lemma closed_imp_right  (h : old) : Imp p old     := imp_right (fun _ => h) (fun _ => trivial)

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
    proof := mkApp5 (.const (if pol then ``imp_make else ``and_make') []) p tree newTree definition proof }
  | none => {proof}


structure TreeHyp where
  hyp : Expr
  newTree : Option Expr
  proof : Expr
deriving Inhabited


private def bindPropBinderWithHyp (p : Expr) (isImp : Bool) (isRev : Bool) (lemma_ lemma' closed_lemma closed_lemma' : Name) (pol : Bool) (tree : Expr) : TreeHyp → TreeHyp :=
  fun {hyp, newTree, proof} =>
  match newTree with
  | none => { 
    hyp
    newTree := p
    proof := mkApp4 (.const (if pol then closed_lemma else closed_lemma') []) p hyp tree proof }

  | some newTree => {
    hyp
    newTree := (if isRev then Function.swap else id) (mkApp2 (.const (if isImp then ``Imp else ``And) [])) p newTree
    proof := mkApp5 (.const (if pol then lemma_ else lemma') []) p hyp tree newTree proof }


-- we need to manage a hypothesis that we want to use.
-- this is done by putting the hypothesis in the proof as either a hypothesis in the hypothesis or a conjuction in the conclustion.

variable {hyp old new : Prop}

lemma hyp_imp_right  (h : (hyp → new) → old) : (hyp → Imp p new) → Imp p old := fun h₁ hp => h (fun hh => h₁ hh hp)
lemma hyp_imp_right' (h : (hyp → old) → new) : (hyp → Imp p old) → Imp p new := fun h₁ hp => h (fun hh => h₁ hh hp)

def ImpRightWithHyp (p : Expr) : Bool → Expr → TreeHyp → TreeHyp :=
  bindPropBinderWithHyp p true false ``hyp_imp_right ``hyp_imp_right' .anonymous .anonymous


lemma hyp_imp_left   (h : old → (hyp ∧ new)) : (hyp → Imp new p) → Imp old p := fun h₁ h₂ => let ⟨hh, h₂⟩ := h h₂; h₁ hh h₂
lemma hyp_imp_left'  (h : new → (hyp ∧ old)) : (hyp → Imp old p) → Imp new p := fun h₁ h₂ => let ⟨hh, h₂⟩ := h h₂; h₁ hh h₂
lemma closed_hyp_imp_left   (h : old → hyp) : (hyp → p) → Imp old p := fun h₁ h₂ => h₁ (h h₂)
lemma closed_hyp_imp_left'  (h : hyp ∧ old) : (hyp → Imp old p) → p := let ⟨hh, h₂⟩ := h; fun h₁ => h₁ hh h₂

def ImpLeftWithHyp (p : Expr) : Bool → Expr → TreeHyp → TreeHyp :=
  bindPropBinderWithHyp p true true ``hyp_imp_left ``hyp_imp_left' ``closed_hyp_imp_left ``closed_hyp_imp_left'


lemma hyp_and_right  (h : new → (hyp ∧ old)) : And p new → (hyp ∧ And p old) := fun ⟨hp, h₂⟩ => let ⟨hh, h₂⟩ := h h₂; ⟨hh, hp, h₂⟩
lemma hyp_and_right' (h : old → (hyp ∧ new)) : And p old → (hyp ∧ And p new) := fun ⟨hp, h₂⟩ => let ⟨hh, h₂⟩ := h h₂; ⟨hh, hp, h₂⟩
lemma closed_hyp_and_right  (h : hyp ∧ old) : p → (hyp ∧ And p old) := fun hp => let ⟨hh, h₂⟩ := h; ⟨hh, hp, h₂⟩
lemma closed_hyp_and_right' (h : old → hyp) : And p old → (hyp ∧ p) := fun ⟨hp, h₂⟩ => ⟨h h₂, hp⟩

def AndRightWithHyp (p : Expr) : Bool → Expr → TreeHyp → TreeHyp :=
  bindPropBinderWithHyp p false false ``hyp_and_right ``hyp_and_right' ``closed_hyp_and_right ``closed_hyp_and_right'


lemma hyp_and_left   (h : new → (hyp ∧ old)) : And new p → (hyp ∧ And old p) := fun ⟨h₂, hp⟩ => let ⟨hh, h₂⟩ := h h₂; ⟨hh, h₂, hp⟩
lemma hyp_and_left'  (h : old → (hyp ∧ new)) : And old p → (hyp ∧ And new p) := fun ⟨h₂, hp⟩ => let ⟨hh, h₂⟩ := h h₂; ⟨hh, h₂, hp⟩
lemma closed_hyp_and_left   (h : hyp ∧ old) : p → (hyp ∧ And old p) := fun hp => let ⟨hh, h₂⟩ := h; ⟨hh, h₂, hp⟩
lemma closed_hyp_and_left'  (h : old → hyp) : And old p → (hyp ∧ p) := fun ⟨h₂, hp⟩ => ⟨h h₂, hp⟩

def AndLeftWithHyp (p : Expr) : Bool → Expr → TreeHyp → TreeHyp :=
  bindPropBinderWithHyp p false true ``hyp_and_left ``hyp_and_left' ``closed_hyp_and_left ``closed_hyp_and_left'


-- note that make_hyp is only applicable in the not primed case.
lemma make_hyp (hyp : Prop) : hyp → hyp := id
lemma make_hyp_keeping (hyp : Prop) : hyp → (hyp ∧ hyp) := fun h => ⟨h, h⟩

def MakeHyp (delete? pol : Bool) (tree : Expr) : TreeHyp :=
  if delete? && !pol
  then {
    hyp := tree
    newTree := none
    proof := mkApp (.const ``make_hyp []) tree
  }
  else {
    hyp := tree
    newTree := tree
    proof := mkApp (.const ``make_hyp_keeping []) tree
  }
  

def UseHyp (tree : Expr) (hyp : TreeHyp) (isImp isRev pol : Bool) (use use' use_closed use_closed' closed_use closed_use' closed_use_closed : Name) (tree' : Expr) (fvar : FVarId) : TreeProof → TreeProof :=
  let {hyp, newTree, proof} := hyp
  let (isClosed, application) := match newTree with
    | none         => (true, fun c => mkApp2 c hyp tree)
    | some newTree => (false, fun c => mkApp3 c hyp tree newTree)
  fun {newTree := newTree', proof := proof'} =>
  let (isClosed', application') := match newTree' with
    | none         => (true, fun c => mkApp  c tree')
    | some newTree' => (false, fun c => mkApp2 c tree' newTree')
  let proof' := .lam `h hyp (proof'.abstract #[.fvar fvar]) .default
  let lemma_ := if isClosed
    then if isClosed'
      then ite pol closed_use_closed .anonymous
      else ite pol use_closed use_closed'
    else if isClosed'
      then ite pol closed_use closed_use'
      else ite pol use use'
  {
    proof := mkApp2 (application' (application (.const lemma_ []))) proof proof'
    newTree := match newTree with
      | none     => match newTree' with
        | none      => none
        | some new' => new'
      | some new => match newTree' with
        | none      => if isImp == pol then none else new
        | some new' => (if isRev then Function.swap else id) (mkApp2 (.const (if isImp then ``Imp else ``And) [])) new new'
  }

variable {old' new' : Prop}

lemma use_hyp_imp_right  (h₁ : old → (hyp ∧ new)) (h₂ : hyp → (new' → old')) : Imp new new' → Imp old old' := fun g h₃ => let ⟨hh, h₃⟩ := h₁ h₃; h₂ hh (g h₃)
lemma use_hyp_imp_right' (h₁ : new → (hyp ∧ old)) (h₂ : hyp → (old' → new')) : Imp old old' → Imp new new' := fun g h₃ => let ⟨hh, h₃⟩ := h₁ h₃; h₂ hh (g h₃)
lemma use_closed_hyp_imp_right   (h₁ : old → hyp) (h₂ : hyp → (new' → old')) : new' → Imp old old' := fun g h₃ => h₂ (h₁ h₃) g
lemma use_closed_hyp_imp_right'  (h₁ : hyp ∧ old) (h₂ : hyp → (old' → new')) : Imp old old' → new' := fun g => let ⟨hh, h₃⟩ := h₁; h₂ hh (g h₃)
lemma closed_use_hyp_imp_right  (h₁ : old → (hyp ∧ new)) (h₂ : hyp →   old') : Imp old old'         := fun h₃ => let ⟨hh, _⟩ := h₁ h₃; h₂ hh
-- lemma closed_use_hyp_imp_right' (h₁ : new → (hyp ∧ old)) (h₂ : hyp → ¬ old') : Imp old old' → ¬ new := fun g h₃ => let ⟨hh, h₃⟩ := h₁ h₃; h₂ hh (g h₃)
lemma closed_use_closed_hyp_imp_right   (h₁ : old → hyp) (h₂ : hyp →   old') :   Imp old old' := fun h₃ => h₂ (h₁ h₃)
-- lemma closed_use_closed_hyp_imp_right'  (h₁ : hyp ∧ old) (h₂ : hyp → ¬ old') : ¬ Imp old old' := fun g => let ⟨hh, h₃⟩ := h₁; h₂ hh (g h₃)

def UseHypImpRight (tree : Expr) (hyp : TreeHyp) (pol : Bool) : Expr → FVarId → TreeProof → TreeProof :=
  UseHyp tree hyp true false pol 
  ``use_hyp_imp_right ``use_hyp_imp_right' ``use_closed_hyp_imp_right ``use_closed_hyp_imp_right' ``closed_use_hyp_imp_right .anonymous ``closed_use_closed_hyp_imp_right


lemma use_hyp_imp_left   (h₁ : (hyp → new) → old) (h₂ : hyp → (old' → new')) : Imp new' new → Imp old' old := fun g h₃ => h₁ (fun hh => g (h₂ hh h₃))
lemma use_hyp_imp_left'  (h₁ : (hyp → old) → new) (h₂ : hyp → (new' → old')) : Imp old' old → Imp new' new := fun g h₃ => h₁ (fun hh => g (h₂ hh h₃))
-- lemma closed_use_hyp_imp_left   (h₁ : (hyp → new) → old) (h₂ : hyp → ¬ old') : Imp old' old         := fun h₃ => h₁ (fun hh => (h₂ hh h₃).elim)
lemma closed_use_hyp_imp_left'  (h₁ : (hyp → old) → new) (h₂ : hyp →   old') : Imp old' old →   new := fun g  => h₁ (fun hh => g (h₂ hh))

def UseHypImpLeft (tree : Expr) (hyp : TreeHyp) (pol : Bool) : Expr → FVarId → TreeProof → TreeProof :=
  UseHyp tree hyp true false pol 
  ``use_hyp_imp_left ``use_hyp_imp_left' .anonymous .anonymous .anonymous ``closed_use_hyp_imp_left' .anonymous


lemma use_hyp_and_right  (h₁ : new → (hyp ∧ old)) (h₂ : hyp → (new' → old')) : And new new' → And old old' := fun ⟨h₃, h₄⟩ => let ⟨hh, h₃⟩ := h₁ h₃; ⟨h₃, h₂ hh h₄⟩
lemma use_hyp_and_right' (h₁ : old → (hyp ∧ new)) (h₂ : hyp → (old' → new')) : And old old' → And new new' := fun ⟨h₃, h₄⟩ => let ⟨hh, h₃⟩ := h₁ h₃; ⟨h₃, h₂ hh h₄⟩
lemma use_closed_hyp_and_right   (h₁ : hyp ∧ old) (h₂ : hyp → (new' → old')) : new' → And old old' := fun h₄ => let ⟨hh, h₃⟩ := h₁; ⟨h₃, h₂ hh h₄⟩
lemma use_closed_hyp_and_right'  (h₁ : old → hyp) (h₂ : hyp → (old' → new')) : And old old' → new' := fun ⟨h₃, h₄⟩ => h₂ (h₁ h₃) h₄
lemma closed_use_hyp_and_right  (h₁ : new → (hyp ∧ old)) (h₂ : hyp →   old') : new → And old old'   := fun h₃ => let ⟨hh, h₃⟩ := h₁ h₃; ⟨h₃, h₂ hh⟩
-- lemma closed_use_hyp_and_right' (h₁ : old → (hyp ∧ new)) (h₂ : hyp → ¬ old') : ¬ And old old'       := fun ⟨h₃, h₄⟩ => let ⟨hh, _⟩ := h₁ h₃; h₂ hh h₄
lemma closed_use_closed_hyp_and_right   (h₁ : hyp ∧ old) (h₂ : hyp →   old') :   And old old' := let ⟨hh, h₃⟩ := h₁; ⟨h₃, h₂ hh⟩
-- lemma closed_use_closed_hyp_and_right'  (h₁ : old → hyp) (h₂ : hyp → ¬ old') : ¬ And old old' := fun ⟨h₃, h₄⟩ => h₂ (h₁ h₃) h₄

def UseHypAndRight (tree : Expr) (hyp : TreeHyp) (pol : Bool) : Expr → FVarId → TreeProof → TreeProof :=
  UseHyp tree hyp true false pol 
  ``use_hyp_and_right ``use_hyp_and_right' ``use_closed_hyp_and_right ``use_closed_hyp_and_right' ``closed_use_hyp_and_right .anonymous ``closed_use_closed_hyp_and_right


lemma use_hyp_and_left   (h₁ : new → (hyp ∧ old)) (h₂ : hyp → (new' → old')) : And new' new → And old' old := fun ⟨h₄, h₃⟩ => let ⟨hh, h₃⟩ := h₁ h₃; ⟨h₂ hh h₄, h₃⟩
lemma use_hyp_and_left'  (h₁ : old → (hyp ∧ new)) (h₂ : hyp → (old' → new')) : And old' old → And new' new := fun ⟨h₄, h₃⟩ => let ⟨hh, h₃⟩ := h₁ h₃; ⟨h₂ hh h₄, h₃⟩
lemma use_closed_hyp_and_left    (h₁ : hyp ∧ old) (h₂ : hyp → (new' → old')) : new' → And old' old := fun h₄ => let ⟨hh, h₃⟩ := h₁; ⟨h₂ hh h₄, h₃⟩
lemma use_closed_hyp_and_left'   (h₁ : old → hyp) (h₂ : hyp → (old' → new')) : And old' old → new' := fun ⟨h₄, h₃⟩ => h₂ (h₁ h₃) h₄
lemma closed_use_hyp_and_left   (h₁ : new → (hyp ∧ old)) (h₂ : hyp →   old') : new → And old' old   := fun h₃ => let ⟨hh, h₃⟩ := h₁ h₃; ⟨h₂ hh, h₃⟩
-- lemma closed_use_hyp_and_left'  (h₁ : old → (hyp ∧ new)) (h₂ : hyp → ¬ old') : ¬ And old' old       := fun ⟨h₄, h₃⟩ => let ⟨hh, _⟩ := h₁ h₃; h₂ hh h₄
lemma closed_use_closed_hyp_and_left    (h₁ : hyp ∧ old) (h₂ : hyp →   old') :   And old' old := let ⟨hh, h₃⟩ := h₁; ⟨h₂ hh, h₃⟩
-- lemma closed_use_closed_hyp_and_left'   (h₁ : old → hyp) (h₂ : hyp → ¬ old') : ¬ And old' old := fun ⟨h₄, h₃⟩ => h₂ (h₁ h₃) h₄

def UseHypAndLeft (tree : Expr) (hyp : TreeHyp) (pol : Bool) : Expr → FVarId → TreeProof → TreeProof :=
  UseHyp tree hyp true false pol 
  ``use_hyp_and_left ``use_hyp_and_left' ``use_closed_hyp_and_left ``use_closed_hyp_and_left' ``closed_use_hyp_and_left .anonymous ``closed_use_closed_hyp_and_left




end nonDependent



-- section propDependent
-- variable {p : Prop} {old new : p → Prop}

-- lemma imp'_imp  (h : ∀ hp, old hp → new hp) : Imp' old → Imp' new := forall_imp h
-- lemma imp'_imp' (h : ∀ hp, new hp → old hp) : Imp' new → Imp' old := forall_imp h
-- lemma and'_imp  (h : ∀ hp, old hp → new hp) : And' old → And' new := Exists.imp h
-- lemma and'_imp' (h : ∀ hp, new hp → old hp) : And' new → And' old := Exists.imp h

-- def revertPropBinder (name : Name) (p tree var : Expr) (mkBinder proveImp : Name) : NewTreeProof → NewTreeProof :=
--   fun {newTree, proof} =>
--   let mkLam b := .lam name p (b.abstract #[var]) .default
--   let newTree := mkLam newTree
--   let proof := mkLam proof
--   {newTree := mkApp2 (.const mkBinder []) p newTree, proof := mkApp4 (.const proveImp []) p tree newTree proof}

-- def revertPropBinderWithDef (name : Name) (p tree var definition : Expr) (mkBinder proveImp : Name) : NewTreeProof → NewTreeProof :=
--   fun {newTree, proof} =>
--   let mkLam b := .lam name p (b.abstract #[var]) .default
--   let newTree := mkLam newTree
--   {newTree := mkApp2 (.const mkBinder []) p newTree,
--    proof   := mkApp5 (.const proveImp []) p tree newTree definition proof}
-- end propDependent



section typeBinders
variable {α : Type u} [inst : Nonempty α] {old new : α → Prop}

def bindTypeBinder (name : Name) (u : Level) (domain inst var : Expr) (isForall : Bool) (imp_lemma imp_lemma' non_dep_lemma non_dep_lemma' close_lemma close_lemma' : Name) (pol : Bool) (tree : Expr) : TreeProof → TreeProof :=
  fun {newTree, proof} =>
  let mkLam b := .lam name domain (b.abstract #[var]) .default
  let proof   := mkLam proof
  match newTree with
  | none => {proof := mkApp4 (.const (if pol then close_lemma else close_lemma') [u]) domain inst tree proof }
  | some newTree =>
    let newTree := newTree.abstract #[var]
    if newTree.hasLooseBVars
    then
      let newTree := .lam name domain newTree .default
      {
      newTree := mkApp3 (.const (if isForall then ``Forall else ``Exists) [u]) domain inst newTree,
      proof := mkApp5 (.const (if pol then imp_lemma else imp_lemma') [u]) domain inst tree newTree proof }
    else
      { newTree, proof := mkApp5 (.const (if pol then non_dep_lemma else non_dep_lemma') [u]) domain inst tree newTree proof }


lemma forall_imp  (h : ∀ a, new a → old a) : Forall new → Forall old := _root_.forall_imp h
lemma forall_imp' (h : ∀ a, old a → new a) : Forall old → Forall new := _root_.forall_imp h
variable {new : Prop}
lemma non_dep_forall_imp  (h : ∀ a, new → old a) : new → Forall old := fun g a => h a g
lemma non_dep_forall_imp' (h : ∀ a, old a → new) : Forall old → new := let ⟨a⟩ := inst; fun g => h a (g a)

lemma closed_forall_imp  (h : ∀ a,   old a) :   Forall old := h
lemma closed_forall_imp' (h : ∀ a, ¬ old a) : ¬ Forall old := let ⟨a⟩ := inst; fun g => h a (g a)

def bindForall (name : Name) (u : Level) (domain inst var : Expr) : Bool → Expr → TreeProof → TreeProof :=
  bindTypeBinder name u domain inst var true ``forall_imp ``forall_imp' ``non_dep_forall_imp ``non_dep_forall_imp' ``closed_forall_imp ``closed_forall_imp'

variable {new : α → Prop}
lemma exists_imp  (h : ∀ a, new a → old a) : Exists new → Exists old := Exists.imp h
lemma exists_imp' (h : ∀ a, old a → new a) : Exists old → Exists new := Exists.imp h
variable {new : Prop}
lemma non_dep_exists_imp  (h : ∀ a, new → old a) : new → Exists old := let ⟨a⟩ := inst; fun g => ⟨a, h a g⟩
lemma non_dep_exists_imp' (h : ∀ a, old a → new) : Exists old → new := fun ⟨a, g⟩ => h a g

lemma closed_exists_imp  (h : ∀ a,   old a) :   Exists old := let ⟨a⟩ := inst; ⟨a, h a⟩
lemma closed_exists_imp' (h : ∀ a, ¬ old a) : ¬ Exists old := fun ⟨a, ha⟩ => h a ha

def bindExists (name : Name) (u : Level) (domain inst var : Expr) : Bool → Expr → TreeProof → TreeProof :=
  bindTypeBinder name u domain inst var false ``exists_imp ``exists_imp' ``non_dep_exists_imp ``non_dep_exists_imp' ``closed_exists_imp ``closed_exists_imp'


variable {old : Prop} {new : α → Prop}

lemma forall_make  (a : α) (h : new a → old) : Forall new → old := fun g => h (g a)
lemma exists_make' (a : α) (h : old → new a) : old → Exists new := fun g => ⟨a, h g⟩

def bindFVar (fvar : FVarId) (name : Name) (u : Level) (domain inst definition : Expr) (pol : Bool) (tree : Expr) : TreeProof → TreeProof :=
  fun {newTree, proof} =>
    let mkLet b := .letE name domain definition (b.abstract #[.fvar fvar]) false
    let proof := mkLet proof
    match newTree with
    | none => {proof}
    | some newTree =>
      let mkLam b := .lam name domain (b.abstract #[.fvar fvar]) .default
      let newTree := mkLam newTree
      {
      newTree := mkApp3 (.const (if pol then ``Forall      else ``Exists      ) [u]) domain inst newTree,
      proof   := mkApp6 (.const (if pol then ``forall_make else ``exists_make') [u]) domain inst tree newTree definition proof}

lemma forall_make' (h : ∀ a, old → new a) : old → Forall new := fun g a => h a g
lemma exists_make  (h : ∀ a, new a → old) : Exists new → old := fun ⟨a, g⟩ => h a g
variable {new : Prop}
lemma non_dep_forall_make' (h : α → (old → new)) : old → new := let ⟨a⟩ := inst; h a
lemma non_dep_exists_make  (h : α → (new → old)) : new → old := let ⟨a⟩ := inst; h a

-- in the case where we close the goal, we need to use the instance to show that the metavariable can indeed be filled in.

def bindMVarWithInst (mvarId : MVarId) (type : Expr) (name : Name) (u : Level) (inst : Expr) (pol : Bool) (tree : Expr) : TreeProof → TreeProof := 
  fun treeProof@{newTree, proof} => match newTree with
  | none => {proof := .letE name type (mkApp2 (.const ``Classical.choice [.succ u]) type inst) (proof.abstract #[.mvar mvarId]) false}
  | some _ =>
  bindTypeBinder name u type inst (.mvar mvarId) (!pol) ``exists_make ``forall_make' ``non_dep_exists_make ``non_dep_forall_make' .anonymous .anonymous pol tree treeProof

variable {new : α → Prop}
lemma instance_forall_make' (h : ∀ a, old → new a) : old → Imp' (fun inst => @Forall α inst new) := fun g _ a => h a g
lemma instance_exists_make  (h : ∀ a, new a → old) : And' (fun inst => @Exists α inst new) → old := fun ⟨_, a, g⟩ => h a g

lemma instance_choose_mvar  (h : ∀ _ : α,   old) : Nonempty α → old   := fun   inst => h (Classical.choice inst)
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

lemma closed_destroy_exists (a : α) (h :   old a) :   Exists old := ⟨a, h⟩
lemma closed_destroy_forall (a : α) (h : ¬ old a) : ¬ Forall old := fun g => h (g a)

def introMVar (mvarId : MVarId) (name : Name) (u : Level) (type inst assignment : Expr) (pol : Bool) (tree : Expr) : TreeProof → TreeProof :=
  fun {newTree, proof} =>
  let mkLet e := .letE name type assignment (e.abstract #[.mvar mvarId]) false
  let proof := mkLet proof
  match newTree with
  | none => {proof := mkApp5 (.const (if pol then ``closed_destroy_exists else ``closed_destroy_forall) [u]) type inst tree assignment proof}
  | some newTree =>
    let newTree := newTree.replaceFVar (.mvar mvarId) assignment
    {newTree, proof := mkApp6 (.const (if pol then ``destroy_exists else ``destroy_forall) [u]) type inst tree newTree assignment proof}


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

structure OptionRecursor (α : Type u) where
  all (name : Name) (u : Level) (domain inst : Expr) : Bool → Expr → (Expr → α) → Option α
  ex  (name : Name) (u : Level) (domain inst : Expr) : Bool → Expr → (Expr → α) → Option α

  imp_right (p : Expr) : Bool → Expr → α → Option α
  and_right (p : Expr) : Bool → Expr → α → Option α
  imp_left  (p : Expr) : Bool → Expr → α → Option α
  and_left  (p : Expr) : Bool → Expr → α → Option α


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
    | .imp_right => "· →"
    | .and_right => "· ∧"
    | .imp_left => "→ ·"
    | .and_left => "∧ ·"
    | .all => "∀"
    | .ex => "∃"

partial def Recursor.recurseM [Inhabited α] [Monad m] [MonadError m] (r : Recursor (m α)) (pol : Bool := true) (tree : Expr) (pos : List TreeNodeKind) (k : Bool → Expr → m α) : m α :=
  let rec visit [Inhabited α] (pol : Bool) : List TreeNodeKind → Expr → m α  
    | .all      ::xs, forall_pattern n u α i b => r.all n u α i pol (.lam n α b .default) (fun a => visit pol xs (b.instantiate1 a))
    | .ex       ::xs, exists_pattern n u α i b => r.ex  n u α i pol (.lam n α b .default) (fun a => visit pol xs (b.instantiate1 a))
    | .imp_right::xs, imp_pattern p tree       => r.imp_right p pol tree (visit   pol  xs tree)
    | .and_right::xs, and_pattern p tree       => r.and_right p pol tree (visit   pol  xs tree)
    | .imp_left ::xs, imp_pattern tree p       => r.imp_left  p pol tree (visit (!pol) xs tree)
    | .and_left ::xs, and_pattern tree p       => r.and_left  p pol tree (visit   pol  xs tree)
    | [], e => k pol e
    | xs, e => throwError m!"could not tree-recurse to position {xs} in term {e}"
  visit pol pos tree


partial def OptionRecursor.recurse [Inhabited α] (r : OptionRecursor α) (pol : Bool := true) (tree : Expr) (pos : List TreeNodeKind)
  (k : Bool → Expr → List TreeNodeKind → α) : α :=
  let rec visit [Inhabited α] (pol : Bool) (ys : List TreeNodeKind) (e : Expr) : α :=
    let kOption := fun
      | some k => k
      | none => k pol e ys
    match ys, e with
    | .all      ::xs, forall_pattern n u α i b => kOption <| r.all n u α i pol (.lam n α b .default) (fun a => visit pol xs (b.instantiate1 a))
    | .ex       ::xs, exists_pattern n u α i b => kOption <| r.ex  n u α i pol (.lam n α b .default) (fun a => visit pol xs (b.instantiate1 a))
    | .imp_right::xs, imp_pattern p tree       => kOption <| r.imp_right p pol tree (visit   pol  xs tree)
    | .and_right::xs, and_pattern p tree       => kOption <| r.and_right p pol tree (visit   pol  xs tree)
    | .imp_left ::xs, imp_pattern tree p       => kOption <| r.imp_left  p pol tree (visit (!pol) xs tree)
    | .and_left ::xs, and_pattern tree p       => kOption <| r.and_left  p pol tree (visit   pol  xs tree)
    | _, _ => k pol e ys
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

syntax treePos := "[" num,* "]"

def get_positions (stx : Syntax) : List Nat :=
  let stx := stx[1].getArgs.toList
  match stx with
  | [] => []
  | x :: xs =>
    let rec go : List Syntax → List Nat
      | _ :: y :: ys => TSyntax.getNat ⟨y⟩ :: go ys
      | _ => []
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