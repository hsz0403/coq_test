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

Lemma Seq_Spec' (sig : finType) (n : nat) (F1 F2 : finType) (pM1 : pTM sig F1 n) (pM2 : pTM sig F2 n) (P : Assert sig n) (Q : Assert sig n) (R : F2 -> Assert sig n) : Triple P pM1 (fun _ => Q) -> (Triple Q pM2 R) -> Triple P (pM1;;pM2) R.
Proof.
Admitted.

Lemma Seq_Spec_swapped (sig : finType) (n : nat) (F1 F2 : finType) (pM1 : pTM sig F1 n) (pM2 : pTM sig F2 n) (P : Assert sig n) (Q : F1 -> Assert sig n) (R : F2 -> Assert sig n) : (forall ymid, Triple (Q ymid) pM2 R) -> Triple P pM1 Q -> Triple P (pM1;;pM2) R.
Proof.
Admitted.

Lemma Seq_Spec_swapped' (sig : finType) (n : nat) (F1 F2 : finType) (pM1 : pTM sig F1 n) (pM2 : pTM sig F2 n) (P : Assert sig n) (Q : Assert sig n) (R : F2 -> Assert sig n) : (Triple Q pM2 R) -> Triple P pM1 (fun _ => Q) -> Triple P (pM1;; pM2) R.
Proof.
Admitted.

Lemma Seq_SpecT_strong (sig : finType) (n : nat) (F1 F2 : finType) (pM1 : pTM sig F1 n) (pM2 : pTM sig F2 n) (P : Assert sig n) (Q : F1 -> Assert sig n) (R : F2 -> Assert sig n) (k k1 k2 : nat) : TripleT P k1 pM1 Q -> (* Correctness of [pM1] *) (forall (ymid : F1), TripleT (Q ymid) k2 pM2 R) -> (* Correctness of [pM2] (for every output label of [pM1]) *) (forall tin ymid tmid, P tin -> Q ymid tmid -> 1 + k1 + k2 <= k) -> TripleT P k (pM1;; pM2) R.
Proof.
intros H1 H2 H3.
split.
-
eapply Seq_Spec.
+
apply H1.
+
cbn.
apply H2.
-
eapply TerminatesIn_monotone.
{
apply Seq_TerminatesIn'.
-
apply H1.
-
apply H1.
-
instantiate (1 := fun tmid k2' => exists ymid, Q ymid tmid /\ k2 <= k2').
{
clear H1 H3.
setoid_rewrite TripleT_iff in H2.
unfold TerminatesIn in *.
firstorder.
}
}
{
clear H1 H2.
intros tin k' (HP&Hk).
unfold Triple_TRel in *.
exists k1.
repeat split; eauto.
unfold Triple_Rel.
intros ymid tmid HQ.
modpon HQ.
specialize H3 with (1 := HP) (2 := HQ).
exists k2.
split; eauto.
lia.
Admitted.

Lemma Seq_SpecT (sig : finType) (n : nat) (F1 F2 : finType) (pM1 : pTM sig F1 n) (pM2 : pTM sig F2 n) (P : Assert sig n) (Q : F1 -> Assert sig n) (R : F2 -> Assert sig n) (k k1 k2 : nat) : TripleT P k1 pM1 Q -> (* Correctness of [pM1] *) (forall (ymid : F1), TripleT (Q ymid) k2 pM2 R) -> (* Correctness of [pM2] (for every output label of [pM1]) *) 1 + k1 + k2 <= k -> TripleT P k (pM1;; pM2) R.
Proof.
intros.
Admitted.

Lemma Seq_SpecT' (sig : finType) (n : nat) (F1 F2 : finType) (pM1 : pTM sig F1 n) (pM2 : pTM sig F2 n) (P : Assert sig n) (Q : Assert sig n) (R : F2 -> Assert sig n) (k k1 k2 : nat) : TripleT P k1 pM1 (fun _ => Q) -> (TripleT Q k2 pM2 R) -> 1 + k1 + k2 <= k -> TripleT P k (pM1;;pM2) R.
Proof.
Admitted.

Lemma If_Spec (sig : finType) (n : nat) (F : finType) (pM1 : pTM sig bool n) (pM2 pM3 : pTM sig F n) (P : Assert sig n) (Q : bool -> Assert sig n) (R : F -> Assert sig n) : Triple P pM1 Q -> Triple (Q true) pM2 R -> Triple (Q false) pM3 R -> Triple P (If pM1 pM2 pM3) R.
Proof.
rewrite !Triple_iff.
intros H1 H2 H3.
eapply Realise_monotone.
-
TM_Correct; eauto.
-
intros tin (yout, tout) H.
cbn in *.
Admitted.

Lemma If_SpecT (sig : finType) (n : nat) (F : finType) (pM1 : pTM sig bool n) (pM2 pM3 : pTM sig F n) (P : Assert sig n) (Q : bool -> Assert sig n) (R : F -> Assert sig n) (k k1 k2 k3 : nat) : TripleT P k1 pM1 Q -> TripleT (Q true) k2 pM2 R -> TripleT (Q false) k3 pM3 R -> (forall tin yout tout, P tin -> Q yout tout -> (1 + k1 + if yout then k2 else k3) <= k) -> TripleT P k (If pM1 pM2 pM3) R.
Proof.
intros H1 H2 H3 H4.
split.
-
eapply If_Spec.
+
apply H1.
+
apply H2.
+
apply H3.
-
eapply TerminatesIn_monotone.
{
apply If_TerminatesIn'.
-
apply H1.
-
apply H1.
-
apply H2.
-
apply H3.
}
{
unfold Triple_Rel, Triple_TRel.
intros tin k' (H&Hk).
specialize H4 with (1 := H).
exists k1.
repeat split.
-
assumption.
-
reflexivity.
-
intros tmid ymid Hmid.
modpon Hmid.
modpon H4.
destruct ymid; cbn in *.
+
exists k2.
repeat split; auto.
lia.
+
exists k3.
repeat split; auto.
lia.
Admitted.

Lemma If_SpecTReg (sig : finType) (n : nat) (F : finType) (pM1 : pTM _ bool n) (pM2 pM3 : pTM _ F n) (P : Spec sig n) (Q : bool -> Spec sig n) (R : F -> Spec sig n) (k k1 k2 k3 : nat) : TripleT ≃≃( P) k1 pM1 (fun y => ≃≃( Q y)) -> TripleT ≃≃( Q true) k2 pM2 (fun y => ≃≃( R y)) -> TripleT ≃≃( Q false) k3 pM3 (fun y => ≃≃( R y)) -> (implList (fst P) (forall b, implList (fst (Q b)) (1 + k1 + (if b then k2 else k3) <= k))) -> TripleT ≃≃( P) k (If pM1 pM2 pM3) (fun y => ≃≃( R y)).
Proof.
intros H1 H2 H3 H4.
eapply If_SpecT.
1-3:eassumption.
cbn.
intros.
do 2 setoid_rewrite implList_iff in H4.
specialize H4 with (b:=yout).
destruct P,(Q yout).
eapply H4;cbn.
Admitted.

Lemma If_SpecT_weak (sig : finType) (n : nat) (F : finType) (pM1 : pTM sig bool n) (pM2 pM3 : pTM sig F n) (P : Assert sig n) (Q : bool -> Assert sig n) (R : F -> Assert sig n) (k k1 k2 k3 : nat) : TripleT P k1 pM1 Q -> TripleT (Q true) k2 pM2 R -> TripleT (Q false) k3 pM3 R -> (1 + k1 + max k2 k3 <= k) -> TripleT P k (If pM1 pM2 pM3) R.
Proof.
intros.
eapply If_SpecT; eauto.
intros.
destruct yout.
+
assert (k2 <= max k2 k3) by apply Nat.le_max_l.
lia.
+
assert (k3 <= max k2 k3) by apply Nat.le_max_r.
Admitted.

Lemma If_SpecT_weak' (sig : finType) (n : nat) (F : finType) (pM1 : pTM sig bool n) (pM2 pM3 : pTM sig F n) (P : Assert sig n) (Q : bool -> Assert sig n) (R : F -> Assert sig n) (k k1 k2 : nat) : TripleT P k1 pM1 Q -> TripleT (Q true) k2 pM2 R -> TripleT (Q false) k2 pM3 R -> (1 + k1 + k2 <= k) -> TripleT P k (If pM1 pM2 pM3) R.
Proof.
intros H1 H2 H3 H4.
eapply ConsequenceT_pre.
-
eapply If_SpecT_weak with (k2 := k2) (k3 := k2); eauto.
-
auto.
-
Admitted.

Lemma Switch_Spec (sig : finType) (n : nat) (F1 F2 : finType) (pM1 : pTM sig F1 n) (pM2 : F1 -> pTM sig F2 n) (P : Assert sig n) (Q : F1 -> Assert sig n) (R : F2 -> Assert sig n) : Triple P pM1 Q -> (forall (y : F1), Triple (Q y) (pM2 y) R) -> Triple P (Switch pM1 pM2) R.
Proof.
intros H1 H2.
eapply TripleI, Realise_monotone.
-
apply Switch_Realise.
+
apply H1.
+
apply H2.
-
intros tin (yout, tout) H.
cbn in *.
Admitted.

Lemma Switch_SpecT (sig : finType) (n : nat) (F1 F2 : finType) (pM1 : pTM sig F1 n) (pM2 : F1 -> pTM sig F2 n) (P : Assert sig n) (Q : F1 -> Assert sig n) (R : F2 -> Assert sig n) (k k1 k2 : nat) : TripleT P k1 pM1 Q -> (forall (y : F1), TripleT (Q y) k2 (pM2 y) R) -> (1 + k1 + k2 <= k) -> TripleT P k (Switch pM1 pM2) R.
Proof.
intros H1 H2 H3.
split.
-
eapply Switch_Spec.
+
apply H1.
+
apply H2.
-
eapply TerminatesIn_monotone.
+
apply Switch_TerminatesIn.
*
apply H1.
*
apply H1.
*
apply H2.
+
unfold Triple_TRel.
intros tin k' (H&Hk).
exists k1, k2.
repeat split; eauto.
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
eauto.
