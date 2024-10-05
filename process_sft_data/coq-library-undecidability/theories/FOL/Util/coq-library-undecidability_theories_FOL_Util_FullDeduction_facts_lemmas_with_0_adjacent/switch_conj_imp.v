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

Lemma switch_conj_imp alpha beta phi A : A ⊢ alpha ∧ beta ~> phi <-> A ⊢ alpha ~> beta ~> phi.
Proof.
split; intros H.
-
apply II, II.
eapply IE.
apply (@Weak A).
apply H.
firstorder.
apply CI; apply Ctx; firstorder.
-
apply II.
eapply IE.
eapply IE.
eapply Weak.
apply H.
firstorder.
eapply CE1, Ctx; firstorder.
eapply CE2, Ctx; firstorder.
