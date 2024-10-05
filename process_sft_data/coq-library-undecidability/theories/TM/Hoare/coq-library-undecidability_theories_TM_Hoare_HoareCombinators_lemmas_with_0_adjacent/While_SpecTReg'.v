From Undecidability Require Import TMTac TM.Util.Prelim.
From Undecidability.TM Require Export Compound.Multi Combinators.Combinators.
From Undecidability.TM.Hoare Require Import HoareLogic HoareRegister.

Lemma While_SpecTReg' (sig : finType) (n : nat) (F : finType) {inF : inhabitedC F} (pM : pTM _ (option F) n) (X : Type) (f g : X -> nat) P' Q' R' (P : X -> SpecV sig n) (Q : X -> option F -> SpecV sig n) (R : X -> F -> SpecV sig n) : (forall x, TripleT ≃≃( P' x, P x) (g x) pM (fun y => ≃≃( Q' x y, Q x y))) -> (forall x , implList (P' x) (forall yout, implList (Q' x (Some yout)) (Entails ≃≃( [],Q x (Some yout)) ≃≃( R' x yout,R x yout) /\ g x <= f x)) /\ (implList (Q' x None) (exists x', Entails ≃≃( [],Q x None) ≃≃( P' x', P x') /\ 1 + g x + f x' <= f x /\ (forall yout, Entails ≃≃( R' x' yout,R x' yout) ≃≃( R' x yout,R x yout))))) -> forall (x : X), TripleT ≃≃( P' x,P x) (f x) (While pM) (fun y => ≃≃( R' x y,R x y)).
Proof.
intros H1 H2.
eapply While_SpecTReg with (INV := fun _ _ => (_,_)).
all:easy.
