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

Lemma TripleE {sig : finType} {n : nat} {F : Type} P (pM : pTM sig F n) Q: Triple P pM Q -> pM ⊨ Triple_Rel P Q.
Proof.
Admitted.

Lemma TripleTE {sig : finType} {n : nat} {F : Type} P k (pM : pTM sig F n) Q: TripleT P k pM Q -> Triple P pM Q /\ projT1 pM ↓ Triple_TRel P k.
Proof.
Admitted.

Lemma TripleT_iff {sig : finType} {n : nat} {F : Type} P k (pM : pTM sig F n) Q: TripleT P k pM Q <-> (Triple P pM Q /\ projT1 pM ↓ Triple_TRel P k).
Proof.
Admitted.

Lemma TripleT_Triple {sig : finType} {n : nat} {F : Type} P k (pM : pTM sig F n) Q : TripleT P k pM Q -> Triple P pM Q.
Proof.
Admitted.

Lemma Triple_False {sig : finType} {n : nat} {F : Type} (pM : pTM sig F n) Q : Triple (fun _ => False) pM Q.
Proof.
hnf.
Admitted.

Lemma TripleT_False {sig : finType} {n : nat} {F : Type} k (pM : pTM sig F n) Q : TripleT (fun _ => False) k pM Q.
Proof.
hnf.
Admitted.

Lemma Triple_True {sig : finType} {n : nat} {F : Type} (pM : pTM sig F n) P : Triple P pM (fun _ _ => True).
Proof.
hnf.
Admitted.

Lemma Realise_Triple {sig : finType} {n : nat} {F : Type} (P : Assert sig n) (pM : pTM sig F n) (Q : F -> Assert sig n) (R : pRel sig F n) : pM ⊨ R -> (forall tin yout tout, R tin (yout, tout) -> P tin -> Q yout tout) -> Triple P pM Q.
Proof.
intros H1 H2.
apply TripleI.
unfold Triple_Rel.
eapply Realise_monotone.
+
eapply H1.
+
intros tin (yout, tout).
Admitted.

Lemma Realise_TripleT {sig : finType} {n : nat} {F : Type} (P : Assert sig n) (k : nat) (pM : pTM sig F n) (Q : F -> Assert sig n) (R : pRel sig F n) (T : tRel sig n) : pM ⊨ R -> projT1 pM ↓ T -> (forall tin yout tout, R tin (yout, tout) -> P tin -> Q yout tout) -> (forall tin k', P tin -> k <= k' -> T tin k') -> TripleT P k pM Q.
Proof.
intros H1 H2.
split.
-
eapply Realise_Triple; eauto.
-
unfold Triple_TRel.
eapply TerminatesIn_monotone; eauto.
intros tin k' (?&Hk).
Admitted.

Lemma Triple_Realise {sig : finType} {n : nat} {F : Type} (P : Assert sig n) (pM : pTM sig F n) (Q : F -> Assert sig n) : Triple P pM Q -> pM ⊨ (fun tin '(yout,tout) => P tin -> Q yout tout).
Proof.
intros ?%TripleE.
Admitted.

Lemma TripleT_Realise {sig : finType} {n : nat} {F : Type} (P : Assert sig n) k (pM : pTM sig F n) (Q : F -> Assert sig n) : TripleT P k pM Q -> pM ⊨ (fun tin '(yout,tout) => P tin -> Q yout tout).
Proof.
intros ?%TripleTE.
Admitted.

Lemma Triple_iff {sig : finType} {n : nat} {F : Type} P (pM : pTM sig F n) Q: Triple P pM Q <-> pM ⊨ Triple_Rel P Q.
Proof.
split;eauto using TripleE,TripleI.
