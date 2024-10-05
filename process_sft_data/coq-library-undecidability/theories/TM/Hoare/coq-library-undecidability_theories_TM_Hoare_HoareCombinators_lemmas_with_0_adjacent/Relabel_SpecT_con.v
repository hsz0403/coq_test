From Undecidability Require Import TMTac TM.Util.Prelim.
From Undecidability.TM Require Export Compound.Multi Combinators.Combinators.
From Undecidability.TM.Hoare Require Import HoareLogic HoareRegister.

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
firstorder.
