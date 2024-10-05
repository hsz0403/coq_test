From Undecidability Require Import TMTac TM.Util.Prelim.
From Undecidability.TM Require Export Compound.Multi Combinators.Combinators.
From Undecidability.TM.Hoare Require Import HoareLogic HoareRegister.

Lemma Switch_SpecT_strong (sig : finType) (n : nat) (F1 F2 : finType) (pM1 : pTM sig F1 n) (pM2 : F1 -> pTM sig F2 n) (P : Assert sig n) (Q : F1 -> Assert sig n) (R : F2 -> Assert sig n) (k k1 : nat) (k2 : F1 -> nat) : TripleT P k1 pM1 Q -> (forall (y : F1), TripleT (Q y) (k2 y) (pM2 y) R) -> (forall tin yout tout, P tin -> Q yout tout -> 1 + k1 + k2 yout <= k) -> TripleT P k (Switch pM1 pM2) R.
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
apply Switch_TerminatesIn'.
*
apply H1.
*
apply H1.
*
apply H2.
+
unfold Triple_TRel.
intros tin k' (H&Hk).
exists k1.
repeat split.
*
assumption.
*
reflexivity.
*
unfold Triple_Rel.
intros tmid ymid Hmid.
modpon Hmid.
specialize H3 with (1 := H) (2 := Hmid).
exists (k2 ymid).
repeat split; eauto.
lia.
