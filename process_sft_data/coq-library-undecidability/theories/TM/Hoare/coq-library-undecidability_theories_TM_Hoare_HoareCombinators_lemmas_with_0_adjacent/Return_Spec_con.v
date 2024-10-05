From Undecidability Require Import TMTac TM.Util.Prelim.
From Undecidability.TM Require Export Compound.Multi Combinators.Combinators.
From Undecidability.TM.Hoare Require Import HoareLogic HoareRegister.

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
eauto.
