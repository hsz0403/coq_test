From Undecidability.FOL Require Import FOL Reductions.PCPb_to_FOL Util.Syntax_facts Util.Deduction Util.Tarski.
Require Import Undecidability.PCP.Reductions.PCPb_iff_dPCPb Undecidability.PCP.PCP.
From Undecidability.Synthetic Require Import Definitions DecidabilityFacts EnumerabilityFacts ReducibilityFacts.
Require Import List.
Import ListNotations.
Implicit Type b : falsity_flag.
Definition cprv := @prv _ _ falsity_on class.
Instance iUnit (P : Prop) : interp unit.
Proof.
split; intros [] v.
-
exact tt.
-
exact tt.
-
exact True.
-
exact P.
Defined.
Hint Constructors prv : core.
Fixpoint cast {b} (phi : form b) : form falsity_on := match phi with | atom P v => atom P v | falsity => falsity | bin Impl phi psi => bin (b := falsity_on) Impl (cast phi) (cast psi) | quant All phi => quant (b := falsity_on) All (cast phi) end.
Definition dnQ {b} (phi : form b) : form b := (phi --> Q) --> Q.
Fixpoint trans {b} (phi : form b) : form b := match phi with | bin Impl phi1 phi2 => bin Impl (trans phi1) (trans phi2) | quant All phi => quant All (trans phi) | atom sPr v => dnQ (atom sPr v) | atom _ _ => atom sQ (Vector.nil _) | falsity => @atom _ _ _ falsity_on sQ (Vector.nil _) end.
Goal (forall X, ~ ~ X -> X) -> (forall (X Y : Prop), ((X -> Y) -> X) -> X).
Proof.
intros H X Y.
apply H.
intros H'.
clear H.
apply H'.
intros f.
apply f.
intros x.
exfalso.
apply H'.
intros _.
exact x.
Section BPCP_CND.
Local Definition BSRS := list (card bool).
Variable R : BSRS.
Context {ff : falsity_flag}.
End BPCP_CND.

Lemma app3 b psi1 psi2 A phi phi2 : (phi :: phi2 :: psi1 --> psi2 :: A) ⊢I psi1 -> (phi :: phi2 :: psi1 --> psi2 :: A) ⊢I psi2.
Proof.
intros.
Admitted.

Lemma trans_trans' b (phi : form b) A sigma tau : (map (subst_form tau) A) ⊢I ((dnQ (trans phi[sigma])) --> trans phi[sigma]).
Proof.
revert A sigma tau.
induction phi; cbn; intros; try destruct P; try destruct b0; try destruct q.
-
cbn.
eapply II.
eapply app1.
eapply II.
eapply Ctx.
eauto.
-
eapply II.
eapply II.
eapply app2.
eapply II.
eapply app1.
eapply Ctx.
eauto.
-
eapply II.
eapply app1.
eapply II.
eapply Ctx.
eauto.
-
eapply II.
eapply II.
apply IE with (dnQ (trans phi2[sigma])).
specialize (IHphi2 A sigma tau).
apply (Weak IHphi2).
auto.
eapply II.
eapply app3.
eapply II.
eapply app2.
eapply app1.
eapply Ctx.
eauto.
-
apply II, AllI.
apply IE with (dnQ (trans phi[up sigma])).
+
apply IHphi.
+
apply II.
eapply IE.
{
apply Ctx.
right.
left.
cbn.
reflexivity.
}
apply II.
eapply IE.
{
apply Ctx.
right.
left.
reflexivity.
}
replace (trans phi[up sigma]) with (((trans (phi[up sigma]))[up ↑])[($0)..]) at 4.
*
apply AllE.
apply Ctx.
now left.
*
setoid_rewrite trans_subst.
cbn.
repeat setoid_rewrite subst_comp.
apply subst_ext.
intros n.
unfold funcomp.
cbn.
apply subst_term_id.
Admitted.

Lemma trans_trans b (phi : form b) A : A ⊢I ((dnQ (trans phi)) --> trans phi).
Proof.
specialize (trans_trans' phi A var var).
rewrite subst_var.
intros H.
apply (Weak H).
clear H.
induction A; cbn; trivial.
setoid_rewrite subst_var.
Admitted.

Goal (forall X, ~ ~ X -> X) -> (forall (X Y : Prop), ((X -> Y) -> X) -> X).
Proof.
intros H X Y.
apply H.
intros H'.
clear H.
apply H'.
intros f.
apply f.
intros x.
exfalso.
apply H'.
intros _.
Admitted.

Lemma Double' b A (phi : form b) : A ⊢C phi -> map trans A ⊢I trans phi.
Proof.
remember class as s; induction 1; subst.
-
cbn.
eapply II.
eauto.
-
eapply IE; eauto.
-
cbn.
apply AllI.
rewrite map_map.
rewrite map_map in IHprv.
erewrite map_ext; try now apply IHprv.
intros psi.
cbn.
now rewrite trans_subst.
-
setoid_rewrite trans_subst.
eapply AllE; eauto.
-
specialize (IHprv eq_refl).
eapply IE; try apply trans_trans.
apply II.
apply (Weak IHprv).
auto.
-
eapply Ctx.
now eapply in_map.
-
eapply IE; try apply trans_trans.
apply II.
eapply IE; try now apply Ctx.
cbn.
apply II.
eapply IE; try now apply Ctx.
apply II.
eapply IE; try apply trans_trans.
apply II.
eapply IE.
+
apply Ctx.
right.
right.
right.
now left.
+
apply II.
apply Ctx.
Admitted.

Lemma Double b (phi : form b) : [] ⊢C phi -> [] ⊢I (trans phi).
Proof.
Admitted.

Lemma BPCP_to_CND : PCPb R -> [] ⊢C (F R).
Proof.
intros H.
rewrite PCPb_iff_dPCPb in *.
Admitted.

Lemma impl_trans A phi : trans (A ==> phi) = (map trans A) ==> trans phi.
Proof.
Admitted.

Lemma CND_BPCP : [] ⊢C (F R) -> PCPb R.
Proof.
intros H % Double % soundness.
specialize (H _ (IB R) (fun _ => nil)).
unfold F, F1, F2 in H.
rewrite !impl_trans, !map_map, !impl_sat in H.
cbn in H.
eapply PCPb_iff_dPCPb.
eapply H; try tauto.
-
intros ? [(x,y) [<- ?] ] % in_map_iff ?.
cbn in *.
eapply H1.
left.
now rewrite !IB_enc.
-
intros ? [(x,y) [<- ?] ] % in_map_iff ? ? ? ?.
cbn in *.
eapply H1.
intros.
eapply H2.
rewrite !IB_prep.
cbn.
econstructor 2; trivial.
-
intros.
eapply H0.
intros.
unfold dPCPb, dPCP.
Admitted.

Lemma BPCP_CND : PCPb R <-> [] ⊢C (F R).
Proof.
split.
eapply BPCP_to_CND.
intros ? % CND_BPCP.
Admitted.

Corollary cprv_undec : UA -> ~ decidable (cprv nil).
Proof.
intros H.
Admitted.

Corollary cprv_unenum : UA -> ~ enumerable (complement (@cprv nil)).
Proof.
intros H.
Admitted.

Theorem cprv_red : PCPb ⪯ FOL_prv_class.
Proof.
exists (fun R => F R).
intros R.
apply (BPCP_CND R).
