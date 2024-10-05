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

Lemma MND_CND A (phi : form falsity_off) : A ⊢M phi -> map cast A ⊢C cast phi.
Proof.
revert A phi.
remember falsity_off as b.
intros.
induction H; cbn in *; subst; try congruence.
-
eapply II; eauto.
-
eapply IE; try now apply IHprv1.
now apply IHprv2.
-
eapply AllI.
rewrite map_map.
rewrite map_map in IHprv.
erewrite map_ext; try now apply IHprv.
intros psi.
cbn.
now rewrite subst_cast.
-
setoid_rewrite subst_cast.
eapply AllE; eauto.
-
eapply Ctx, in_map_iff; eauto.
-
apply Pc.
