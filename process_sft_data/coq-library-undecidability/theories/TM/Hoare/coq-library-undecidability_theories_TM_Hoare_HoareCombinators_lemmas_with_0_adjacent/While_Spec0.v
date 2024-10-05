From Undecidability Require Import TMTac TM.Util.Prelim.
From Undecidability.TM Require Export Compound.Multi Combinators.Combinators.
From Undecidability.TM.Hoare Require Import HoareLogic HoareRegister.

Lemma While_Spec0 (sig : finType) (n : nat) (F : finType) {inF : inhabitedC F} (pM : pTM sig (option F) n) (P : Assert sig n) (Q : option F -> Assert sig n) (R : F -> Assert sig n) : Triple P pM Q -> (forall yout tout, Q (Some yout) tout -> R yout tout) -> (forall tmid, Q None tmid -> P tmid) -> Triple P (While pM) R.
Proof.
intros H1 H3 H2.
eapply TripleI, Realise_monotone.
{
TM_Correct.
apply H1.
}
{
clear H1.
unfold Triple_Rel in *.
apply WhileInduction; firstorder.
}
