From Undecidability Require Import TMTac TM.Util.Prelim.
From Undecidability.TM Require Export Compound.Multi Combinators.Combinators.
From Undecidability.TM.Hoare Require Import HoareLogic HoareRegister.

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
firstorder.
