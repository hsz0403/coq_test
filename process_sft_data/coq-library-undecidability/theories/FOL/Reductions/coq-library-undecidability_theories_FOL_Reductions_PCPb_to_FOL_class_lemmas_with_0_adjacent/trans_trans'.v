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
now intros [].
