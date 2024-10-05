From Undecidability Require Import TMTac TM.Util.Prelim.
From Undecidability.TM Require Export Compound.Multi Combinators.Combinators.
From Undecidability.TM.Hoare Require Import HoareLogic HoareRegister.

Lemma If_SpecTReg (sig : finType) (n : nat) (F : finType) (pM1 : pTM _ bool n) (pM2 pM3 : pTM _ F n) (P : Spec sig n) (Q : bool -> Spec sig n) (R : F -> Spec sig n) (k k1 k2 k3 : nat) : TripleT ≃≃( P) k1 pM1 (fun y => ≃≃( Q y)) -> TripleT ≃≃( Q true) k2 pM2 (fun y => ≃≃( R y)) -> TripleT ≃≃( Q false) k3 pM3 (fun y => ≃≃( R y)) -> (implList (fst P) (forall b, implList (fst (Q b)) (1 + k1 + (if b then k2 else k3) <= k))) -> TripleT ≃≃( P) k (If pM1 pM2 pM3) (fun y => ≃≃( R y)).
Proof.
intros H1 H2 H3 H4.
eapply If_SpecT.
1-3:eassumption.
cbn.
intros.
do 2 setoid_rewrite implList_iff in H4.
specialize H4 with (b:=yout).
destruct P,(Q yout).
eapply H4;cbn.
all:eapply tspecE;eauto.
