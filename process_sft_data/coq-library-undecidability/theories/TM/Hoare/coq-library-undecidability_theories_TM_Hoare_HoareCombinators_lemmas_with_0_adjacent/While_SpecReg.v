From Undecidability Require Import TMTac TM.Util.Prelim.
From Undecidability.TM Require Export Compound.Multi Combinators.Combinators.
From Undecidability.TM.Hoare Require Import HoareLogic HoareRegister.

Lemma While_SpecReg (sig : finType) (n : nat) (F : finType) {inF : inhabitedC F} (pM : pTM _ (option F) n) (X : Type) (P : X -> Spec sig n) (Q : X -> option F -> Spec sig n) (R : X -> F -> Spec sig n) : (forall x, Triple ≃≃( P x) pM (fun y => ≃≃( Q x y))) -> (forall x , implList (fst (P x)) (forall yout, implList (fst (Q x (Some yout))) (Entails ≃≃( [],snd (Q x (Some yout))) ≃≃( R x yout))) /\ (implList (fst (Q x None)) (exists x', Entails ≃≃( [],snd (Q x None)) ≃≃( P x') /\ (forall yout, Entails ≃≃( R x' yout) ≃≃( R x yout))))) -> forall (x : X), Triple ≃≃( P x) (While pM) (fun y => ≃≃( R x y)).
Proof.
intros H1 H2.
eapply While_Spec with (1:=H1).
-
intros ? ? ? ? ?.
revert tout.
apply EntailsE.
specialize (H2 x) as [H2 ?].
destruct (P x);cbn in *.
apply tspecE in H as [H _].
do 2 setoid_rewrite implList_iff in H2.
specialize (H2 H yout).
destruct (Q x (Some yout));cbn in *.
eapply tspec_introPure.
rewrite implList_iff.
eauto.
-
intros **.
specialize (H2 x) as [? H2].
destruct (P x);cbn in *.
apply tspecE in H as [H _].
setoid_rewrite implList_iff in H2.
destruct (Q x None);cbn in *.
eapply tspecE in H0 as (H0&?).
specialize (H2 H0) as (x'&H2&H').
eexists x'.
split.
{
eapply (EntailsE H2).
eapply tspecI.
now hnf.
easy.
}
intros ? .
now eapply EntailsE.
