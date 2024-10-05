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
}
