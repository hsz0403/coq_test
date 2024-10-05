From Undecidability Require Import TMTac TM.Util.Prelim.
From Undecidability.TM Require Export Compound.Multi Combinators.Combinators.
From Undecidability.TM.Hoare Require Import HoareLogic HoareRegister.

Lemma Nop_Spec (sig : finType) (n : nat) (P : Assert sig n) : Triple P Nop (fun _ => P).
Proof.
eapply TripleI,Realise_monotone.
{
TM_Correct.
}
{
intros tin ([], tout) ->.
hnf.
auto.
Admitted.

Lemma Nop_SpecT_con (sig : finType) (n : nat) (P : Assert sig n) k : TripleT P k Nop (fun _ => P).
Proof.
eapply ConsequenceT_pre.
-
apply Nop_SpecT.
-
auto.
-
Admitted.

Lemma Relabel_Spec (sig : finType) (F1 F2 : finType) (n : nat) (P : Assert sig n) (Q : F1 -> Assert sig n) (pM : pTM sig F1 n) (f : F1->F2) : Triple P pM Q -> Triple P (Relabel pM f) (fun y' t => exists y'', y' = f y'' /\ Q y'' t).
Proof.
intros HT.
eapply TripleI, Realise_monotone.
{
TM_Correct.
apply HT.
}
{
intros tin (yout, tout) H.
TMSimp.
intros.
eauto.
Admitted.

Lemma Relabel_Spec_con (sig : finType) (F1 F2 : finType) (n : nat) (P : Assert sig n) (Q : F1 -> Assert sig n) (Q' : F2 -> Assert sig n) (pM : pTM sig F1 n) (f : F1->F2) : Triple P pM Q -> (forall yout, Entails (Q yout) (Q' (f yout))) -> Triple P (Relabel pM f) Q'.
Proof.
intros.
eapply Consequence_post.
-
apply Relabel_Spec; eauto.
-
setoid_rewrite Entails_iff in H0.
setoid_rewrite Entails_iff.
intros.
TMSimp.
Admitted.

Lemma Relabel_SpecT (sig : finType) (F1 F2 : finType) (n : nat) (P : Assert sig n) (k : nat) (Q : F1 -> Assert sig n) (pM : pTM sig F1 n) (f : F1->F2) : TripleT P k pM Q -> TripleT P k (Relabel pM f) (fun y' t => exists y'', y' = f y'' /\ Q y'' t).
Proof.
split.
-
apply Relabel_Spec; eauto.
-
eapply TerminatesIn_monotone.
+
TM_Correct.
apply H.
+
Admitted.

Lemma Relabel_SpecT_con (sig : finType) (F1 F2 : finType) (n : nat) (P : Assert sig n) (k : nat) (Q : F1 -> Assert sig n) (Q' : F2 -> Assert sig n) (pM : pTM sig F1 n) (f : F1->F2) : TripleT P k pM Q -> (forall yout, Entails (Q yout) (Q' (f yout))) -> TripleT P k (Relabel pM f) Q'.
Proof.
intros.
eapply ConsequenceT_post.
-
apply Relabel_SpecT; eauto.
-
setoid_rewrite Entails_iff in H0.
setoid_rewrite Entails_iff.
intros.
TMSimp.
Admitted.

Lemma Return_Spec (sig : finType) (F1 F2 : finType) (n : nat) (P : Assert sig n) (Q : F1 -> Assert sig n) (pM : pTM sig F1 n) (y : F2) : Triple P pM Q -> Triple P (Return pM y) (fun y' t => y' = y /\ exists y'', Q y'' t).
Proof.
intros HT.
eapply TripleI, Realise_monotone.
{
TM_Correct.
apply HT.
}
{
intros tin (yout, tout) H.
TMSimp.
intros.
eauto.
Admitted.

Lemma Return_Spec_con (sig : finType) (F1 F2 : finType) (n : nat) (P : Assert sig n) (Q : F1 -> Assert sig n) (Q' : F2 -> Assert sig n) (pM : pTM sig F1 n) (y : F2) : Triple P pM Q -> (forall yout, Entails (Q yout) (Q' y)) -> Triple P (Return pM y) Q'.
Proof.
intros.
eapply Consequence_post.
-
apply Return_Spec; eauto.
-
setoid_rewrite Entails_iff in H0.
setoid_rewrite Entails_iff.
intros ? ? (->&(?&?)).
Admitted.

Lemma Return_SpecT (sig : finType) (F1 F2 : finType) (n : nat) (P : Assert sig n) (k : nat) (Q : F1 -> Assert sig n) (pM : pTM sig F1 n) (y : F2) : TripleT P k pM Q -> TripleT P k (Return pM y) (fun y' t => y' = y /\ exists y'', Q y'' t).
Proof.
split.
-
apply Return_Spec; eauto.
-
eapply TerminatesIn_monotone.
+
TM_Correct.
apply H.
+
Admitted.

Lemma Return_SpecT_con (sig : finType) (F1 F2 : finType) (n : nat) (P : Assert sig n) (k : nat) (Q : F1 -> Assert sig n) (Q' : F2 -> Assert sig n) (pM : pTM sig F1 n) (y : F2) : TripleT P k pM Q -> (forall yout, Entails (Q yout) (Q' y)) -> TripleT P k (Return pM y) Q'.
Proof.
intros.
eapply ConsequenceT_post.
-
apply Return_SpecT; eauto.
-
setoid_rewrite Entails_iff in H0.
setoid_rewrite Entails_iff.
intros ? ? (->&(?&?)).
Admitted.

Lemma Seq_Spec (sig : finType) (n : nat) (F1 F2 : finType) (pM1 : pTM sig F1 n) (pM2 : pTM sig F2 n) (P : Assert sig n) (Q : F1 -> Assert sig n) (R : F2 -> Assert sig n) : Triple P pM1 Q -> (forall ymid, Triple (Q ymid) pM2 R) -> Triple P (pM1;;pM2) R.
Proof.
intros HT1 HT2.
eapply TripleI, Realise_monotone.
{
TM_Correct.
apply HT1.
instantiate (1 := fun tin '(yout, tout) => forall (ymid : F1), Q ymid tin -> R yout tout).
{
clear HT1 P pM1.
setoid_rewrite Triple_iff in HT2.
unfold Realise in *.
intros tin k outc HLoop.
intros ymid Hmid.
specialize HT2 with (1 := HLoop).
cbn in *.
eapply HT2; eauto.
}
}
{
intros tin (yout, tout) H.
TMSimp.
intros.
modpon H.
modpon H0.
eapply H0.
Admitted.

Lemma Nop_SpecT (sig : finType) (n : nat) (P : Assert sig n) : TripleT P 0 Nop (fun _ => P).
Proof.
split.
-
eapply Consequence_pre.
apply Nop_Spec.
firstorder.
-
eapply TerminatesIn_monotone.
+
TM_Correct.
+
firstorder.
