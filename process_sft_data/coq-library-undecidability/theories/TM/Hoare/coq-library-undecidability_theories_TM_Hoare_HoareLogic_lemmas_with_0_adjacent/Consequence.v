From Undecidability.TM Require Import TM Util.TM_facts.
Definition Assert (sig : Type) (n : nat) : Type := tapes sig n -> Prop.
Definition Triple_Rel {sig : finType} {n : nat} {F : Type} (P : Assert sig n) (Q : F -> Assert sig n) : pRel sig F n := fun tin '(yout, tout) => P tin -> Q yout tout.
Inductive Triple {sig : finType} {n : nat} {F : Type} P (pM : pTM sig F n) Q := TripleI : pM ⊨ Triple_Rel P Q -> Triple P pM Q.
Definition Triple_TRel {sig : finType} {n : nat} (P : Assert sig n) (k : nat) : tRel sig n := fun tin k' => P tin /\ k <= k'.
Inductive TripleT {sig : finType} {n : nat} {F : Type} (P : Assert sig n) (k : nat) (pM : pTM sig F n) (Q : F -> Assert sig n) := TripleTI : Triple P pM Q -> projT1 pM ↓ Triple_TRel P k -> TripleT P k pM Q.
Hint Resolve TripleT_Triple : core.
Hint Resolve Triple_False : core.
Hint Resolve TripleT_False : core.
Hint Resolve Triple_True : core.
Inductive Entails (sig : Type) (n : nat) (P1 P2 : Assert sig n) := EntailsI : (forall tin, P1 tin -> P2 tin) -> Entails P1 P2.
Arguments Entails {_ _} _ _.
Hint Resolve EntailsI : core.
Instance Entails_PO (sig : Type) (n : nat): PreOrder (@Entails sig n).
Proof.
split;hnf.
all:setoid_rewrite Entails_iff.
all:eauto.
Instance Triple_Entails_Proper sig n F: Proper (Entails --> eq ==> pointwise_relation F Entails ==> Basics.impl) (@Triple sig n F).
Proof.
repeat intro.
subst.
eapply Consequence;eauto.
Instance TripleT_Entails_Proper sig n F: Proper (Entails --> le ==> eq ==> pointwise_relation F Entails ==> Basics.impl) (@TripleT sig n F).
Proof.
repeat intro.
subst.
eapply ConsequenceT;eauto.

Lemma Consequence (sig : finType) (n : nat) (F : Type) (P1 P2 : Assert sig n) (Q1 Q2 : F -> Assert sig n) (pM : pTM sig F n) : Triple P2 pM Q2 -> Entails P1 P2 -> (forall y, Entails (Q2 y) (Q1 y)) -> Triple P1 pM Q1.
Proof.
intros H1%TripleE H2 H3.
apply TripleI.
setoid_rewrite Entails_iff in H2.
setoid_rewrite Entails_iff in H3.
eapply Realise_monotone.
{
apply H1.
}
{
intros tin (yout, tout) H4.
cbn in H4.
cbn.
intros H5.
auto.
}
