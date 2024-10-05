From Undecidability Require Import TMTac TM.Util.Prelim.
From Undecidability.TM Require Export Compound.Multi Combinators.Combinators.
From Undecidability.TM.Hoare Require Import HoareLogic HoareRegister.

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
firstorder.
