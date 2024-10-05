From Undecidability Require Import TMTac TM.Util.Prelim.
From Undecidability.TM Require Export Compound.Multi Combinators.Combinators.
From Undecidability.TM.Hoare Require Import HoareLogic HoareRegister.

Lemma Switch_SpecTReg (sig : finType) (n : nat) (F1 F2 : finType) (pM1 : pTM _ F1 n) (pM2 : F1 -> pTM _ F2 n) (P : Spec sig n) Q R (k k1 : nat) (f : F1 -> nat) : TripleT ≃≃(P) k pM1 (fun y => ≃≃(Q y)) -> (forall (y : F1), TripleT ≃≃(Q y) (f y) (pM2 y) (fun y => ≃≃(R y))) -> (implList (fst P) (forall y, implList (fst (Q y)) (1 + k + f y <= k1))) -> TripleT ≃≃(P) k1 (Switch pM1 pM2) (fun y => ≃≃(R y)).
Proof.
intros H1 H2 H3.
eapply Switch_SpecT_strong.
1-2:eassumption.
intros.
destruct P.
eapply tspecE in H as [].
eapply implListE in H3.
2:easy.
setoid_rewrite implList_iff in H3.
apply H3.
cbn in H0.
destruct Q.
eapply tspecE;eassumption.
