From Undecidability Require Import TMTac TM.Util.Prelim.
From Undecidability.TM Require Export Compound.Multi Combinators.Combinators.
From Undecidability.TM.Hoare Require Import HoareLogic HoareRegister.

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
}
