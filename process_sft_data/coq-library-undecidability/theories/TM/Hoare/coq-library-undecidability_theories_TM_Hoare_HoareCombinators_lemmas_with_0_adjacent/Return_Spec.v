From Undecidability Require Import TMTac TM.Util.Prelim.
From Undecidability.TM Require Export Compound.Multi Combinators.Combinators.
From Undecidability.TM.Hoare Require Import HoareLogic HoareRegister.

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
}
