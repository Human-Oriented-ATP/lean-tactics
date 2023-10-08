import Lean
import Mathlib.Logic.Basic
import Mathlib.Control.Bifunctor

namespace Tree

@[reducible] def Imp (p q : Prop) := p → q
@[reducible] def And (p q : Prop) := p ∧ q

@[reducible] def Forall (α : Sort u) (p : α → Prop) := ∀ a : α, p a
@[reducible] def Exists (α : Sort u) (p : α → Prop) := _root_.Exists p

@[reducible] def Instance (α : Sort u) (p : α → Prop) := (inst : α) → p inst

open Lean Meta

structure TreeProof where
  newTree : Option Expr := none
  proof : Expr
deriving Inhabited


section nonDependent

def bindPropBinderAux (saveClosed : Bool) (p : Expr) (isImp isRev keepsClosed : Bool) (imp_lemma close_lemma save_lemma : Name) (tree : Expr) : TreeProof → TreeProof :=
  fun {newTree, proof} =>
  match newTree with
  | none => if !keepsClosed && saveClosed
    then {
      newTree := if isImp then (if isRev then mkApp2 (.const ``And []) tree p else mkApp2 (.const ``And []) (mkNot tree) (mkNot p)) else mkApp2 (.const ``Imp []) tree p
      proof := mkApp3 (.const save_lemma  []) p tree proof }
    else { 
      newTree := if keepsClosed then none else (if isImp && !isRev then mkNot p else p)
      proof := mkApp3 (.const close_lemma []) p tree proof }

  | some newTree => {
    newTree := (if isRev then Function.swap else id) (mkApp2 (.const (if isImp then ``Imp else ``And) [])) p newTree
    proof := mkApp4 (.const imp_lemma []) p tree newTree proof }

def bindPropBinder (saveClosed : Bool) (p : Expr) (isImp isRev : Bool) (imp_lemma imp_lemma' close_lemma close_lemma' save_lemma : Name) (pol : Bool) (tree : Expr) : TreeProof → TreeProof :=
  bindPropBinderAux saveClosed p isImp isRev (isImp == pol) (ite pol imp_lemma imp_lemma') (ite pol close_lemma close_lemma') save_lemma tree

def bindDepPropBinderAux (delete? : Bool) (p fvar : Expr) (isImp isRev keepsClosed : Bool) (imp_lemma close_lemma forget_lemma : Name) (nonDep : Unit → TreeProof) (tree : Expr) : TreeProof → TreeProof :=
  fun {newTree, proof} =>
  let proof := proof.abstract #[fvar]
  if !proof.hasLooseBVars
  then nonDep ()
  else
    let proof := .lam `h p proof .default
    match newTree with
    | none => {
      newTree := if keepsClosed then none else (if isImp && !isRev then mkNot p else p),
      proof := mkApp3 (.const close_lemma []) p tree proof }

    | some newTree => if keepsClosed && delete?
      then {
        newTree
        proof := mkApp4 (.const forget_lemma []) p tree newTree proof }
      else {
      newTree := (if isRev then Function.swap else id) (mkApp2 (.const (if isImp then ``Imp else ``And) [])) p newTree
      proof := mkApp4 (.const imp_lemma []) p tree newTree proof }

def bindDepPropBinder (delete? : Bool) (p fvar : Expr) (isImp isRev : Bool) (imp_lemma imp_lemma' close_lemma close_lemma' forget_lemma : Name)
  (nonDep : Bool → Expr → Bool → Expr → TreeProof → TreeProof) (pol : Bool) (tree : Expr) (treeProof : TreeProof) : TreeProof :=
  bindDepPropBinderAux delete? p fvar isImp isRev (isImp == pol) (ite pol imp_lemma imp_lemma') (ite pol close_lemma close_lemma') forget_lemma
    (fun _ => nonDep false p pol tree treeProof) tree treeProof

variable {p : Prop} {old new : Prop}

lemma imp_right  (h : new → old) : Imp p new → Imp p old := (h ∘ ·)
lemma imp_right' (h : old → new) : Imp p old → Imp p new := (h ∘ ·)
lemma closed_imp_right       (h :   old) : Imp p old               := imp_right (fun _ => h) (fun _ => trivial)
lemma closed_imp_right'      (h : ¬ old) : Imp p old →         ¬ p := (h ∘ ·)
lemma closed_imp_right_save' (h : ¬ old) : Imp p old → ¬ old ∧ ¬ p := fun g => ⟨h, h ∘ g⟩

lemma imp_dep  (h : p → new → old) : Imp p new → Imp p old := fun g hp => h hp (g hp)
lemma imp_dep' (h : p → old → new) : Imp p old → Imp p new := fun g hp => h hp (g hp)
lemma closed_imp_dep  (h : p →   old) : Imp p old     := h
lemma closed_imp_dep' (h : p → ¬ old) : Imp p old → ¬ p := fun g hp => h hp (g hp)
lemma forget_imp_right (h : p → new → old) : new → Imp p old := Function.swap h

def bindImpRight (saveClosed : Bool) (p : Expr) : Bool → Expr → TreeProof → TreeProof :=
  bindPropBinder saveClosed p true false ``imp_right ``imp_right' ``closed_imp_right ``closed_imp_right' ``closed_imp_right_save'
def bindImpRightDep (delete? : Bool) (p fvar : Expr) : Bool → Expr → TreeProof → TreeProof :=
  bindDepPropBinder delete? p fvar true false ``imp_dep ``imp_dep' ``closed_imp_dep ``closed_imp_dep' ``forget_imp_right bindImpRight

lemma and_right  (h : new → old) : And p new → And p old := And.imp_right h
lemma and_right' (h : old → new) : And p old → And p new := And.imp_right h
lemma closed_and_right       (h :   old) :         p → And p old := fun hp => ⟨hp, h⟩
lemma closed_and_right_save  (h :   old) : Imp old p → And p old := fun hp => ⟨hp h, h⟩
lemma closed_and_right'      (h : ¬ old) :           ¬ And p old :=  fun ⟨_, g⟩ => h g

lemma and_dep  (h : p → new → old) : And p new → And p old := fun ⟨hp, g⟩ => ⟨hp, h hp g⟩
lemma and_dep' (h : p → old → new) : And p old → And p new := fun ⟨hp, g⟩ => ⟨hp, h hp g⟩
lemma closed_and_dep       (h : p →   old) : p → And p old   := fun hp => ⟨hp, h hp⟩
lemma closed_and_dep'      (h : p → ¬ old) :   ¬ And p old   := fun ⟨hp, g⟩ => h hp g
lemma forget_and_right (h : p → old → new) : And p old → new := fun ⟨hp, g⟩ => h hp g

def bindAndRight (saveClosed : Bool) (p : Expr) : Bool → Expr → TreeProof → TreeProof :=
  bindPropBinder saveClosed p false false ``and_right ``and_right' ``closed_and_right `closed_and_right' ``closed_and_right_save
def bindAndRightDep (delete? : Bool) (p fvar : Expr) : Bool → Expr → TreeProof → TreeProof :=
  bindDepPropBinder delete? p fvar false false ``and_dep ``and_dep' ``closed_and_dep `closed_and_dep' ``forget_and_right bindAndRight

lemma imp_left   (h : old → new) : Imp new p → Imp old p := (· ∘ h)
lemma imp_left'  (h : new → old) : Imp old p → Imp new p := (· ∘ h)
lemma closed_imp_left        (h : ¬ old) : Imp old p             := (absurd · h)
lemma closed_imp_left'       (h :   old) : Imp old p → p         := fun g => g h
lemma closed_imp_left_save'  (h :   old) : Imp old p → And old p := fun g => ⟨h, g h⟩

def bindImpLeft (saveClosed : Bool) (p : Expr) : Bool → Expr → TreeProof → TreeProof :=
  bindPropBinder saveClosed p true true ``imp_left ``imp_left' ``closed_imp_left ``closed_imp_left' ``closed_imp_left'

lemma and_left   (h : new → old) : And new p → And old p := And.imp_left h
lemma and_left'  (h : old → new) : And old p → And new p := And.imp_left h
lemma closed_and_left       (h :   old) :         p → And old p := fun hp => ⟨h, hp⟩
lemma closed_and_left_save  (h :   old) : Imp old p → And old p := fun hp => ⟨h, hp h⟩
lemma closed_and_left'      (h : ¬ old) :           ¬ And old p := fun ⟨g, _⟩ => absurd g h

def bindAndLeft (saveClosed : Bool) (p : Expr) : Bool → Expr → TreeProof → TreeProof :=
  bindPropBinder saveClosed p false true ``and_left ``and_left' ``closed_and_left ``closed_and_left' ``closed_and_left_save

lemma nonempty_make (h : new → old) : new → old := h

lemma and_make  (h : p → new → old) : And p new → old := fun ⟨g, f⟩ => h g f
lemma imp_make' (h : p → old → new) : old → Imp p new := fun g f => h f g
lemma closed_make  (h : p →   old) : p →   old := h
lemma closed_make' (h : p → ¬ old) : p → ¬ old := h

def bindUnknown (p fvar : Expr) (pol : Bool) : Expr → TreeProof → TreeProof :=
  bindDepPropBinder false p fvar (!pol) false ``and_make ``imp_make' ``closed_make ``closed_make' .anonymous (fun _ _ _ _ => id) pol


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


-- we need to manage the hypothesis that we want to use.
-- this is done by putting the hypothesis in the proof as either a hypothesis in the hypothesis or a conjuction in the conclusion.

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
  

def UseHypAux (tree : Expr) (hyp : TreeHyp) (isImp isRev pol : Bool) (use use_closed closed_use closed_use_closed : Name) (tree' : Expr) (fvar : FVarId) : TreeProof → TreeProof :=
  let {hyp, newTree, proof} := hyp
  let (keepsClosed, application) := match newTree with
    | none         => (true, fun c => mkApp2 c hyp tree)
    | some newTree => (false, fun c => mkApp3 c hyp tree newTree)

  fun {newTree := newTree', proof := proof'} =>
  let (keepsClosed', application') := match newTree' with
    | none         => (true, fun c => mkApp  c tree')
    | some newTree' => (false, fun c => mkApp2 c tree' newTree')
  let proof' := .lam `h hyp (proof'.abstract #[.fvar fvar]) .default
  let lemma_ := if keepsClosed
    then if keepsClosed' then closed_use_closed else use_closed
    else if keepsClosed' then closed_use        else use
  
  { proof := mkApp2 (application' (application (.const lemma_ []))) proof proof'
    newTree := match newTree with
      | none     => match newTree' with
        | none      => none
        | some new' => new'
      | some new => match newTree' with
        | none      => if isImp == pol then none else new
        | some new' => (if isRev then Function.swap else id) (mkApp2 (.const (if isImp then ``Imp else ``And) [])) new new'
  }

def UseHyp (tree : Expr) (hyp : TreeHyp) (isImp isRev pol : Bool) (use use' use_closed use_closed' closed_use closed_use' closed_use_closed : Name) (tree' : Expr) (fvar : FVarId) : TreeProof → TreeProof :=
  UseHypAux tree hyp isImp isRev pol (ite pol use use') (ite pol use_closed use_closed') (ite pol closed_use closed_use') (ite pol closed_use_closed .anonymous) tree' fvar

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
  UseHyp tree hyp true true pol 
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
  UseHyp tree hyp false false pol 
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
  UseHyp tree hyp false true pol 
  ``use_hyp_and_left ``use_hyp_and_left' ``use_closed_hyp_and_left ``use_closed_hyp_and_left' ``closed_use_hyp_and_left .anonymous ``closed_use_closed_hyp_and_left




end nonDependent


partial def _root_.Lean.Expr.replace1BetaAux [Monad m] [STWorld ω m] [MonadLiftT (ST ω) m] (e var subst : Expr) : MonadCacheT ExprStructEq Expr m Expr :=
  if !(e.hasFVar || e.hasMVar) then
    pure e
  else checkCache { val := e : ExprStructEq } fun _ => do match e with
    | .proj _ _ s      => return e.updateProj! (← s.replace1BetaAux var subst)
    | .forallE _ d b _ => return e.updateForallE! (← d.replace1BetaAux var subst) (← b.replace1BetaAux var subst)
    | .lam _ d b _     => return e.updateLambdaE! (← d.replace1BetaAux var subst) (← b.replace1BetaAux var subst)
    | .letE _ t v b _  => return e.updateLet! (← t.replace1BetaAux var subst) (← v.replace1BetaAux var subst) (← b.replace1BetaAux var subst)
    | .mdata _ b       => return e.updateMData! (← b.replace1BetaAux var subst)
    | .app ..          => e.withApp fun f args => do
      let wasVar := f.isFVar || f.isMVar
      let f ← f.replace1BetaAux var subst
      if wasVar && f.isLambda then
        (f.betaRev args.reverse).replace1BetaAux var subst
      else
        let args ← args.mapM (·.replace1BetaAux var subst)
        return mkAppN f args
    | e => return if e == var then subst else e

def _root_.Lean.Expr.replace1Beta (e var subst : Expr) : Expr :=
  let instantiate {ω} (e : Expr) : (MonadCacheT ExprStructEq Expr <| (ST ω)) Expr :=
    e.replace1BetaAux var subst
  runST fun _ => instantiate e |>.run


section typeBinders

inductive TypeBinderKind where
| all
| ex
| inst
deriving BEq

def TypeBinderKind.name : TypeBinderKind → Name
| all => ``Forall
| ex => ``Exists
| inst => ``Instance

register_option tree.rememberNonempty : Bool := {
  defValue := false
  group    := "tree"
  descr    := "when removing a binder, keep the nonemptyness of the type inside the tree"
}

def bindTypeBinderAux (name : Name) (u : Level) (domain var : Expr) (binderKind : TypeBinderKind) (keepsClosed : Bool)
  (imp_lemma nonempty_lemma empty_lemma prop_lemma close_nonempty_lemma close_empty_lemma close_prop_lemma : Name)
    (tree : Expr) : TreeProof → MetaM TreeProof :=
  fun {newTree, proof} => do
  let proof    := .lam name domain (proof.abstract #[var]) .default
  match newTree with
  | none => do
    if ← isProp domain then return {
        newTree := if keepsClosed
          then none
          else (if (binderKind == .ex) then id else mkNot) domain
        proof := mkApp3 (.const close_prop_lemma []) domain tree proof }

    let cls := mkApp (.const ``Nonempty [u]) domain
    if let some inst ← synthInstance? cls then return {
        proof := (if keepsClosed then id else (·.app inst)) $ mkApp3 (.const close_nonempty_lemma [u]) domain tree proof }
    
    return {
        newTree := if keepsClosed
          then none
          else (if (binderKind == .ex) then id else mkNot) cls
        proof := mkApp3 (.const close_empty_lemma [u]) domain tree proof }

  | some newTree => do
    let newTree ← instantiateMVars newTree
    let newTree := newTree.abstract #[var]
    if newTree.hasLooseBVars then
      let newTree := .lam name domain newTree .default
      return {
        newTree := mkApp2 (.const binderKind.name [u]) domain newTree,
        proof := mkApp4 (.const imp_lemma [u]) domain tree newTree proof }

    if ← isProp domain then return {
        newTree := mkApp2 (.const (if binderKind == .ex then ``And else ``Imp) []) domain newTree 
        proof := mkApp4 (.const prop_lemma []) domain tree newTree proof }

    let bindUnsafe : TreeProof := {
        newTree
        proof := mkApp4 (.const nonempty_lemma [u]) domain tree newTree proof }
    
    if keepsClosed then unless ← getBoolOption `tree.rememberNonempty do return bindUnsafe

    let cls := mkApp (.const ``Nonempty [u]) domain
    if let some inst ← synthInstance? cls then
      if keepsClosed then return bindUnsafe

      return {
        newTree
        proof := mkApp5 (.const nonempty_lemma [u]) domain tree newTree proof inst }
    
    return {
        newTree := mkApp2 (.const (if binderKind == .ex then ``And else ``Imp) []) cls newTree
        proof := mkApp4 (.const empty_lemma [u]) domain tree newTree proof }



def bindTypeBinder (name : Name) (u : Level) (domain var : Expr) (binderKind : TypeBinderKind) (imp_lemma imp_lemma' nonempty_lemma nonempty_lemma' empty_lemma empty_lemma' prop_lemma prop_lemma' 
  close_nonempty_lemma close_nonempty_lemma' close_empty_lemma close_empty_lemma' close_prop_lemma close_prop_lemma': Name) (pol : Bool) (tree : Expr) : TreeProof → MetaM TreeProof :=
  bindTypeBinderAux name u domain var binderKind (pol != (binderKind == .ex)) (ite pol imp_lemma imp_lemma') (ite pol nonempty_lemma nonempty_lemma') (ite pol empty_lemma empty_lemma') (ite pol prop_lemma prop_lemma')
    (ite pol close_nonempty_lemma close_nonempty_lemma') (ite pol close_empty_lemma close_empty_lemma') (ite pol close_prop_lemma close_prop_lemma') tree

variable {α : Sort u} {old new : α → Prop} {p : Prop} {pold : p → Prop}

lemma forall_imp  (h : ∀ a, new a → old a) : Forall α new → Forall α old := fun g a => h a (g a)
lemma forall_imp' (h : ∀ a, old a → new a) : Forall α old → Forall α new := fun g a => h a (g a)
variable {new : Prop}
lemma nonempty_forall_imp  (h : ∀ a, new → old a)                  : new → Forall α old := fun g a => h a g
lemma nonempty_forall_imp' (h : ∀ a, old a → new) (i : Nonempty α) : Forall α old → new := i.rec fun a g => h a (g a)

lemma empty_forall_imp  (h : ∀ a, new → old a) : Imp (Nonempty α) new → Forall α old := fun g a => h a (g ⟨a⟩)
lemma empty_forall_imp' (h : ∀ a, old a → new) : Forall α old → Imp (Nonempty α) new := fun g ⟨a⟩ => h a (g a)

lemma prop_forall_imp  (h : ∀ a, new → pold a) : (Imp p new) → Forall p pold := fun g a => h a (g a)
lemma prop_forall_imp' (h : ∀ a, pold a → new) : Forall p pold → Imp p new   := fun g a => h a (g a)

lemma empty_forall_close  (h : ∀ a,   old a) : Forall α old := h
lemma empty_forall_close' (h : ∀ a, ¬ old a) : Forall α old → ¬ Nonempty α := fun g ⟨a⟩ => h a (g a)

lemma nonempty_forall_close  (h : ∀ a,   old a)                  :   Forall α old := h
lemma nonempty_forall_close' (h : ∀ a, ¬ old a) (i : Nonempty α) : ¬ Forall α old := i.rec fun a g => h a (g a)

lemma prop_forall_close  (h : ∀ a,   pold a) : Forall p pold := h
lemma prop_forall_close' (h : ∀ a, ¬ pold a) : Forall p pold → ¬ p := fun g a => h a (g a)

def bindForall (name : Name) (u : Level) (domain var : Expr) : Bool → Expr → TreeProof → MetaM TreeProof :=
  bindTypeBinder name u domain var .all ``forall_imp ``forall_imp' ``nonempty_forall_imp ``nonempty_forall_imp' ``empty_forall_imp ``empty_forall_imp' 
  ``prop_forall_imp ``prop_forall_imp' ``nonempty_forall_close ``nonempty_forall_close' ``empty_forall_close ``empty_forall_close' ``prop_forall_close ``prop_forall_close'

variable {new : α → Prop}
lemma exists_imp  (h : ∀ a, new a → old a) : Exists α new → Exists α old := fun ⟨a, g⟩ => ⟨a, h a g⟩
lemma exists_imp' (h : ∀ a, old a → new a) : Exists α old → Exists α new := fun ⟨a, g⟩ => ⟨a, h a g⟩
variable {new : Prop}
lemma nonempty_exists_imp  (h : ∀ a, new → old a) (i : Nonempty α) : new → Exists α old := i.rec fun a g => ⟨a, h a g⟩
lemma nonempty_exists_imp' (h : ∀ a, old a → new)                  : Exists α old → new := fun ⟨a, g⟩ => h a g

lemma empty_exists_imp  (h : ∀ a, new → old a) : And (Nonempty α) new → Exists α old := fun ⟨⟨a⟩, g⟩ => ⟨a, h a g⟩
lemma empty_exists_imp' (h : ∀ a, old a → new) : Exists α old → And (Nonempty α) new := fun ⟨a, g⟩ => ⟨⟨a⟩, h a g⟩

lemma prop_exists_imp  (h : ∀ a, new → pold a) : And p new → Exists p pold := fun ⟨a, g⟩ => ⟨a, h a g⟩
lemma prop_exists_imp' (h : ∀ a, pold a → new) : Exists p pold → And p new := fun ⟨a, g⟩ => ⟨a, h a g⟩ 

lemma empty_exists_close  (h : ∀ a,   old a) : Nonempty α → Exists α old := fun ⟨a⟩ => ⟨a, h a⟩
lemma empty_exists_close' (h : ∀ a, ¬ old a) : ¬ Exists α old := fun ⟨a, ha⟩ => h a ha

lemma nonempty_exists_close  (h : ∀ a,   old a) (i : Nonempty α) :   Exists α old := i.rec fun a => ⟨a, h a⟩
lemma nonempty_exists_close' (h : ∀ a, ¬ old a)                  : ¬ Exists α old := fun ⟨a, ha⟩ => h a ha

lemma prop_exists_close  (h : ∀ a,   pold a) : p → Exists p pold := fun a => ⟨a, h a⟩
lemma prop_exists_close' (h : ∀ a, ¬ pold a) :   ¬ Exists p pold := fun ⟨a, ha⟩ => h a ha

def bindExists (name : Name) (u : Level) (domain var : Expr) : Bool → Expr → TreeProof → MetaM TreeProof :=
  bindTypeBinder name u domain var .ex ``exists_imp ``exists_imp' ``nonempty_exists_imp ``nonempty_exists_imp' ``empty_exists_imp ``empty_exists_imp' 
  ``prop_exists_imp ``prop_exists_imp' ``nonempty_exists_close ``nonempty_exists_close' ``empty_exists_close ``empty_exists_close' ``prop_exists_close ``prop_exists_close'


variable {new : α → Prop}

lemma instance_imp  (h : ∀ a, new a → old a) : Instance α new → Instance α old := fun g a => h a (g a)
lemma instance_imp' (h : ∀ a, old a → new a) : Instance α old → Instance α new := fun g a => h a (g a)
variable {new : Prop}
lemma nonempty_instance_imp  (h : ∀ a, new → old a)                  : new → Instance α old := fun g a => h a g
lemma nonempty_instance_imp' (h : ∀ a, old a → new) (i : Nonempty α) : Instance α old → new := i.rec fun a g => h a (g a)

lemma empty_instance_imp  (h : ∀ a, new → old a) : Imp (Nonempty α) new → Instance α old := fun g a => h a (g ⟨a⟩)
lemma empty_instance_imp' (h : ∀ a, old a → new) : Instance α old → Imp (Nonempty α) new := fun g ⟨a⟩ => h a (g a)

lemma prop_instance_imp  (h : ∀ a, new → pold a) : Imp p new → Instance p pold := fun g a => h a (g a)
lemma prop_instance_imp' (h : ∀ a, pold a → new) : Instance p pold → Imp p new := fun g a => h a (g a)

lemma empty_instance_close  (h : ∀ a,   old a) : Instance α old := h
lemma empty_instance_close' (h : ∀ a, ¬ old a) : Instance α old → ¬ Nonempty α := fun g ⟨a⟩ => h a (g a)

lemma nonempty_instance_close  (h : ∀ a,   old a)                  :   Instance α old := h
lemma nonempty_instance_close' (h : ∀ a, ¬ old a) (i : Nonempty α) : ¬ Instance α old := i.rec fun a g => h a (g a)

lemma prop_instance_close  (h : ∀ a,   pold a) : Instance p pold := h
lemma prop_instance_close' (h : ∀ a, ¬ pold a) : Instance p pold → ¬ p := fun g a => h a (g a)

def bindInstance (name : Name) (u : Level) (cls var : Expr) : Bool → Expr → TreeProof → MetaM TreeProof :=
  bindTypeBinder name u cls var .inst ``instance_imp ``instance_imp' ``nonempty_instance_imp ``nonempty_instance_imp' ``empty_instance_imp ``empty_instance_imp' 
  ``prop_instance_imp ``prop_instance_imp' ``nonempty_instance_close ``nonempty_instance_close' ``empty_instance_close ``empty_instance_close' ``prop_instance_close ``prop_instance_close'


variable {old : Prop} {new : α → Prop}

lemma forall_make  (a : α) (h : new a → old) : Forall α new → old := fun g => h (g a)
lemma exists_make' (a : α) (h : old → new a) : old → Exists α new := fun g => ⟨a, h g⟩
variable {new : Prop}
lemma empty_forall_make  (a : α) (h : new → old) : Imp (Nonempty α) new → old := fun g => h (g ⟨a⟩)
lemma empty_exists_make' (a : α) (h : old → new) : old → And (Nonempty α) new := fun g => ⟨⟨a⟩, h g⟩

lemma prop_forall_make  (a : p) (h : new → old) : Imp p new → old := fun g => h (g a)
lemma prop_exists_make' (a : p) (h : old → new) : old → And p new := fun g => ⟨a, h g⟩

def bindFVar (fvar : FVarId) (name : Name) (u : Level) (domain definition : Expr) (pol : Bool) (tree : Expr) : TreeProof → MetaM TreeProof :=
  fun {newTree, proof} =>
    let proof := .letE name domain definition (proof.abstract #[.fvar fvar]) false
    match newTree with
    | none => pure {proof}
    | some newTree => do
      let newTree ← instantiateMVars newTree
      let newTree := newTree.abstract #[.fvar fvar]
      if newTree.hasLooseBVars
      then
        let newTree := .lam name domain newTree .default
        return {
          newTree := mkApp2 (.const (if pol then ``Forall      else ``Exists      ) [u]) domain newTree,
          proof   := mkApp5 (.const (if pol then ``forall_make else ``exists_make') [u]) domain tree newTree definition proof}
      
      if ← isProp domain then return {
          newTree := mkApp2 (.const (if pol then ``Imp              else ``And              ) [] ) domain newTree
          proof   := mkApp5 (.const (if pol then ``prop_forall_make else ``prop_exists_make') [u]) domain tree newTree definition proof }
      
      let cls := mkApp (.const ``Nonempty [u]) domain
      if ← getBoolOption `tree.rememberNonempty <&&> (Option.isNone <$> synthInstance? cls) then return {
          newTree := mkApp2 (.const (if pol then ``Imp               else ``And               ) [] ) cls newTree
          proof   := mkApp5 (.const (if pol then ``empty_forall_make else ``empty_exists_make') [u]) domain tree newTree definition proof }
      
      return { newTree, proof }

variable {new : α → Prop}
lemma forall_make' (h : ∀ a, old → new a) : old → Forall α new := fun g a => h a g
lemma exists_make  (h : ∀ a, new a → old) : Exists α new → old := fun ⟨a, g⟩ => h a g
variable {new : Prop}
lemma nonempty_forall_make' (h : α → (old → new)) (i : Nonempty α) : old → new := i.rec h
lemma nonempty_exists_make  (h : α → (new → old)) (i : Nonempty α) : new → old := i.rec h

lemma empty_forall_make' (h : α → (old → new)) : old → Imp (Nonempty α) new := fun g ⟨a⟩ => h a g
lemma empty_exists_make  (h : α → (new → old)) : And (Nonempty α) new → old := fun ⟨⟨a⟩, g⟩ => h a g

lemma prop_forall_make' (h : p → (old → new)) : old → Imp p new := fun g a => h a g
lemma prop_exists_make  (h : p → (new → old)) : And p new → old := fun ⟨a, g⟩ => h a g

lemma empty_forall_close_make' (h : α → ¬ old) : old → ¬ Nonempty α := fun g ⟨a⟩ => h a g
lemma empty_exists_close_make  (h : α →   old) : Nonempty α → old   := fun ⟨a⟩ => h a

lemma nonempty_forall_close_make' (h : α → ¬ old) (i : Nonempty α) : ¬ old := i.rec fun a g => h a g
lemma nonempty_exists_close_make  (h : α →   old) (i : Nonempty α) :   old := i.rec h

lemma prop_forall_close_make' (h : p → ¬ old) : old → ¬ p := fun g a => h a g
lemma prop_exists_close_make  (h : p →   old) : p → old   := h


def bindMVar (mvarId : MVarId) (type : Expr) (name : Name) (u : Level) (pol : Bool) : Expr → TreeProof → MetaM TreeProof := 
  bindTypeBinder name u type (.mvar mvarId) (if pol then .ex else .all) ``exists_make ``forall_make' ``nonempty_exists_make ``nonempty_forall_make' ``empty_exists_make ``empty_forall_make' 
  ``prop_exists_make ``prop_forall_make' ``nonempty_exists_close_make ``nonempty_forall_close_make' ``empty_exists_close_make ``empty_forall_close_make' ``prop_exists_close_make ``prop_forall_close_make' pol



variable {old : α → Prop} {new : Prop}

-- this is for (assigned) metavariables that come from the target
lemma destroy_exists (a : α) (h : new → old a) : new → Exists α old := fun g => ⟨a, h g⟩
lemma destroy_forall (a : α) (h : old a → new) : Forall α old → new := fun g => h (g a)

lemma closed_destroy_exists (a : α) (h :   old a) :   Exists α old := ⟨a, h⟩
lemma closed_destroy_forall (a : α) (h : ¬ old a) : ¬ Forall α old := fun g => h (g a)

def introMVar (mvarId : MVarId) (name : Name) (u : Level) (type assignment : Expr) (pol : Bool) (tree : Expr) : TreeProof → TreeProof :=
  fun {newTree, proof} =>
  let proof := .letE name type assignment (proof.abstract #[.mvar mvarId]) false
  match newTree with
  | none => { proof := mkApp4 (.const (if pol then ``closed_destroy_exists else ``closed_destroy_forall) [u]) type tree assignment proof }
  | some newTree =>
    let newTree := newTree.replace1Beta (.mvar mvarId) assignment
    { newTree, proof := mkApp5 (.const (if pol then ``destroy_exists else ``destroy_forall) [u]) type tree newTree assignment proof }


end typeBinders
