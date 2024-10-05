From Undecidability Require Import TMTac TM.Util.Prelim.
From Undecidability.TM Require Export Compound.Multi Combinators.Combinators.
From Undecidability.TM.Hoare Require Import HoareLogic HoareRegister.

Lemma While_SpecTReg (sig : finType) (n : nat) (F : finType) {inF : inhabitedC F} (pM : pTM _ (option F) n) (X : Type) (f__loop f__step : X -> nat) (PRE : X -> Spec sig n) (INV : X -> option F -> Spec sig n) (POST : X -> F -> Spec sig n) : (forall x, TripleT ≃≃( PRE x) (f__step x) pM (fun y => ≃≃( INV x y))) -> (forall x , implList (fst (PRE x)) (forall yout, implList (fst (INV x (Some yout))) (Entails ≃≃( [],snd (INV x (Some yout))) ≃≃( POST x yout) /\ f__step x <= f__loop x)) /\ (implList (fst (INV x None)) (exists x', Entails ≃≃( [],snd (INV x None)) ≃≃( PRE x') /\ 1 + f__step x + f__loop x' <= f__loop x /\ (forall yout, Entails ≃≃( POST x' yout) ≃≃( POST x yout))))) -> forall (x : X), TripleT ≃≃( PRE x) (f__loop x) (While pM) (fun y => ≃≃( POST x y)).
Proof.
intros H1 H2.
eapply While_SpecT with (1:=H1).
-
intros x y ? ? ? H'.
specialize (H2 x) as [H2 ?].
setoid_rewrite implList_iff in H2.
destruct (PRE _).
apply tspecE in H as [H _].
specialize (H2 H y).
destruct (POST x y).
destruct (INV x (Some _)).
specialize (tspecE H') as [H'1 ?].
setoid_rewrite implList_iff in H2.
specialize (H2 H'1) as [].
split.
2:easy.
eapply H2.
eapply tspecI.
all:easy.
-
intros **.
specialize (H2 x) as [? H2].
destruct (PRE _).
destruct (INV _ _).
apply tspecE in H as [H _].
setoid_rewrite implList_iff in H2.
eapply tspecE in H0 as (H0&?).
specialize (H2 H0) as (x'&H2&?&H').
eexists x'.
split.
{
eapply (EntailsE H2).
eapply tspecI.
now hnf.
easy.
}
split.
easy.
intros ? .
now eapply EntailsE.
