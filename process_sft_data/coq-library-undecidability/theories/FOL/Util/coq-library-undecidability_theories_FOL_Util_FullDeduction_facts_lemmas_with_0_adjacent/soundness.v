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

Lemma soundness {ff : falsity_flag} A phi : A ⊢I phi -> valid_ctx A phi.
Proof.
remember intu as p.
induction 1; intros D I rho HA; comp.
-
intros Hphi.
apply IHprv; trivial.
intros ? []; subst.
assumption.
now apply HA.
-
now apply IHprv1, IHprv2.
-
intros d.
apply IHprv; trivial.
intros psi [psi'[<- H' % HA]] % in_map_iff.
eapply sat_comp.
now comp.
-
eapply sat_comp, sat_ext.
2: apply (IHprv Heqp D I rho HA (eval rho t)).
now intros [].
-
exists (eval rho t).
cbn.
specialize (IHprv Heqp D I rho HA).
apply sat_comp in IHprv.
eapply sat_ext; try apply IHprv.
now intros [].
-
edestruct IHprv1 as [d HD]; eauto.
assert (H' : forall psi, phi = psi \/ psi el map (subst_form ↑) A -> (d.:rho) ⊨ psi).
+
intros P [<-|[psi'[<- H' % HA]] % in_map_iff]; trivial.
apply sat_comp.
apply H'.
+
specialize (IHprv2 Heqp D I (d.:rho) H').
apply sat_comp in IHprv2.
apply IHprv2.
-
apply (IHprv Heqp) in HA.
firstorder.
-
firstorder.
-
firstorder.
-
firstorder.
now apply H0.
-
firstorder.
now apply H0.
-
firstorder.
-
firstorder.
-
edestruct IHprv1; eauto.
+
apply IHprv2; trivial.
intros xi [<-|HX]; auto.
+
apply IHprv3; trivial.
intros xi [<-|HX]; auto.
-
discriminate.
