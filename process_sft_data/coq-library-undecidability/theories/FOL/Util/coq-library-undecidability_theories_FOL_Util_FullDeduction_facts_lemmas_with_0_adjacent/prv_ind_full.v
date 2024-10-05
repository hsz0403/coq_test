From Undecidability Require Import FOL.Util.FullTarski_facts FOL.Util.Syntax_facts.
From Undecidability Require Import Shared.ListAutomation.
From Undecidability Require Export FOL.Util.FullDeduction.
Import ListAutomationNotations.
Local Set Implicit Arguments.
Require Import Lia.
Ltac comp := repeat (progress (cbn in *; autounfold in *)).
Section ND_def.
Context {Σ_funcs : funcs_signature}.
Context {Σ_preds : preds_signature}.
Context {ff : falsity_flag}.
Context {p : peirce}.
Hint Constructors prv : core.
Definition cycle_shift n x := if Dec (n = x) then $0 else $(S x).
End ND_def.
Hint Constructors prv : core.
Section Soundness.
Context {Σ_funcs : funcs_signature}.
Context {Σ_preds : preds_signature}.
End Soundness.
Ltac subsimpl_in H := rewrite ?up_term, ?subst_term_shift in H.
Ltac subsimpl := rewrite ?up_term, ?subst_term_shift.
Ltac assert1 H := match goal with |- (?phi :: ?T) ⊢ _ => assert (H : (phi :: T) ⊢ phi) by auto end.
Ltac assert2 H := match goal with |- (?phi :: ?psi :: ?T) ⊢ _ => assert (H : (phi :: psi :: T) ⊢ psi) by auto end.
Ltac assert3 H := match goal with |- (?phi :: ?psi :: ?theta :: ?T) ⊢ _ => assert (H : (phi :: psi :: theta :: T) ⊢ theta) by auto end.
Ltac assert4 H := match goal with |- (?f :: ?phi :: ?psi :: ?theta :: ?T) ⊢ _ => assert (H : (f :: phi :: psi :: theta :: T) ⊢ theta) by auto end.
Ltac prv_all x := apply AllI; edestruct nameless_equiv_all as [x ->]; cbn; subsimpl.
Ltac use_exists H x := apply (ExE _ H); edestruct nameless_equiv_ex as [x ->]; cbn; subsimpl.

Lemma prv_ind_full {Σ_funcs : funcs_signature} {Σ_preds : preds_signature} : forall P : peirce -> list (form falsity_on) -> (form falsity_on) -> Prop, (forall (p : peirce) (A : list form) (phi psi : form), (phi :: A) ⊢ psi -> P p (phi :: A) psi -> P p A (phi ~> psi)) -> (forall (p : peirce) (A : list form) (phi psi : form), A ⊢ phi ~> psi -> P p A (phi ~> psi) -> A ⊢ phi -> P p A phi -> P p A psi) -> (forall (p : peirce) (A : list form) (phi : form), (map (subst_form ↑) A) ⊢ phi -> P p (map (subst_form ↑) A) phi -> P p A (∀ phi)) -> (forall (p : peirce) (A : list form) (t : term) (phi : form), A ⊢ ∀ phi -> P p A (∀ phi) -> P p A phi[t..]) -> (forall (p : peirce) (A : list form) (t : term) (phi : form), A ⊢ phi[t..] -> P p A phi[t..] -> P p A (∃ phi)) -> (forall (p : peirce) (A : list form) (phi psi : form), A ⊢ ∃ phi -> P p A (∃ phi) -> (phi :: [p[↑] | p ∈ A]) ⊢ psi[↑] -> P p (phi :: [p[↑] | p ∈ A]) psi[↑] -> P p A psi) -> (forall (p : peirce) (A : list form) (phi : form), A ⊢ ⊥ -> P p A ⊥ -> P p A phi) -> (forall (p : peirce) (A : list form) (phi : form), phi el A -> P p A phi) -> (forall (p : peirce) (A : list form) (phi psi : form), A ⊢ phi -> P p A phi -> A ⊢ psi -> P p A psi -> P p A (phi ∧ psi)) -> (forall (p : peirce) (A : list form) (phi psi : form), A ⊢ phi ∧ psi -> P p A (phi ∧ psi) -> P p A phi) -> (forall (p : peirce) (A : list form) (phi psi : form), A ⊢ phi ∧ psi -> P p A (phi ∧ psi) -> P p A psi) -> (forall (p : peirce) (A : list form) (phi psi : form), A ⊢ phi -> P p A phi -> P p A (phi ∨ psi)) -> (forall (p : peirce) (A : list form) (phi psi : form), A ⊢ psi -> P p A psi -> P p A (phi ∨ psi)) -> (forall (p : peirce) (A : list form) (phi psi theta : form), A ⊢ phi ∨ psi -> P p A (phi ∨ psi) -> (phi :: A) ⊢ theta -> P p (phi :: A) theta -> (psi :: A) ⊢ theta -> P p (psi :: A) theta -> P p A theta) -> (forall (A : list form) (phi psi : form), P class A (((phi ~> psi) ~> phi) ~> phi)) -> forall (p : peirce) (l : list form) (f14 : form), l ⊢ f14 -> P p l f14.
Proof.
intros.
specialize (prv_ind (fun ff => match ff with falsity_on => P | _ => fun _ _ _ => True end)).
intros H'.
apply H' with (ff := falsity_on); clear H'.
all: intros; try destruct ff; trivial.
all: intuition eauto 2.
