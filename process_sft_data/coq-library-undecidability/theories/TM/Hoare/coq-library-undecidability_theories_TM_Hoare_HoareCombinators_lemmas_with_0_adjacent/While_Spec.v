From Undecidability Require Import TMTac TM.Util.Prelim.
From Undecidability.TM Require Export Compound.Multi Combinators.Combinators.
From Undecidability.TM.Hoare Require Import HoareLogic HoareRegister.

Lemma While_Spec (sig : finType) (n : nat) (F : finType) {inF : inhabitedC F} (pM : pTM sig (option F) n) (X : Type) (P : X -> Assert sig n) (Q : X -> option F -> Assert sig n) (R : X -> F -> Assert sig n) : (forall x, Triple (P x) pM (Q x)) -> (forall x yout tmid tout, P x tmid -> Q x (Some yout) tout -> R x yout tout) -> (forall x tin tmid, P x tin -> Q x None tmid -> exists x', P x' tmid /\ forall yout tout, R x' yout tout -> R x yout tout) -> forall (x : X), Triple (P x) (While pM) (R x).
Proof.
intros H1 H2 H3.
enough (While pM ⊨ fun tin '(yout, tout) => forall (x : X), P x tin -> R x yout tout) as H.
{
clear H1 H2 H3.
intros.
rewrite Triple_iff.
unfold Triple_Rel, Realise in *.
eauto.
}
{
eapply Realise_monotone.
{
clear H2 H3.
apply While_Realise with (R := fun tin '(yout, tout) => forall (x : X), P x tin -> Q x yout tout).
hnf.
setoid_rewrite Triple_iff in H1.
unfold Triple_Rel in *.
firstorder.
}
{
clear H1.
apply WhileInduction; intros.
-
eapply H2; eauto.
-
specialize HStar with (1 := H).
specialize H3 with (1 := H) (2 := HStar) as (x'&H3&H3').
eapply H3'; eauto.
}
}
