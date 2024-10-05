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

Instance TripleT_Entails_Proper sig n F: Proper (Entails --> le ==> eq ==> pointwise_relation F Entails ==> Basics.impl) (@TripleT sig n F).
Proof.
repeat intro.
subst.
Admitted.

Lemma ConsequenceT_post (sig : finType) (n : nat) (F : Type) (P : Assert sig n) (k : nat) (Q1 Q2 : F -> Assert sig n) (pM : pTM sig F n) : TripleT P k pM Q2 -> (forall y, Entails (Q2 y) (Q1 y)) -> TripleT P k pM Q1.
Proof.
intros.
Admitted.

Lemma ConsequenceT_pre (sig : finType) (n : nat) (F : Type) (P1 P2 : Assert sig n) (k1 k2 : nat) (Q : F -> Assert sig n) (pM : pTM sig F n) : TripleT P2 k2 pM Q -> Entails P1 P2 -> k2 <= k1 -> TripleT P1 k1 pM Q.
Proof.
intros.
Admitted.

Lemma Triple_exists_pre {sig : finType} {n : nat} {F : Type} (pM : pTM sig F n) (X : Type) (P : X -> Assert sig n) (Q : F -> Assert sig n) : (forall (x : X), Triple (P x) pM Q) -> Triple (fun tin => exists x : X, P x tin) pM (Q).
Proof.
setoid_rewrite Triple_iff.
unfold Triple_Rel.
Admitted.

Lemma Triple_exists_con {sig : finType} {n : nat} {F : Type} (pM : pTM sig F n) (X : Type) (P : Assert sig n) (Q : X -> F -> Assert sig n) : (exists (x : X), Triple P pM (Q x)) -> Triple P pM (fun yout tout => exists x : X, Q x yout tout).
Proof.
setoid_rewrite Triple_iff.
unfold Triple_Rel.
Admitted.

Lemma Triple_forall_pre {sig : finType} {n : nat} {F : Type} (pM : pTM sig F n) (X : Type) (P : X -> Assert sig n) (Q : F -> Assert sig n) : (exists (x : X), Triple (P x) pM Q) -> Triple (fun tin => forall x : X, P x tin) pM (Q).
Proof.
setoid_rewrite Triple_iff.
unfold Triple_Rel.
Admitted.

Lemma Triple_forall_con {sig : finType} {n : nat} {F : Type} (pM : pTM sig F n) (X : Type) (P : Assert sig n) (Q : X -> F -> Assert sig n) : (forall (x : X), Triple P pM (Q x)) -> Triple P pM (fun yout tout => forall x : X, Q x yout tout).
Proof.
setoid_rewrite Triple_iff.
unfold Triple_Rel.
Admitted.

Lemma Triple_eta_pre {sig : finType} {n : nat} {F : Type} (pM : pTM sig F n) (P : Assert sig n) (Q : F -> Assert sig n) : Triple P pM Q -> Triple (fun tin => P tin) pM Q.
Proof.
Admitted.

Lemma Triple_eta_con {sig : finType} {n : nat} {F : Type} (pM : pTM sig F n) (P : Assert sig n) (Q : F -> Assert sig n) : Triple P pM Q -> Triple P pM (fun yout => Q yout).
Proof.
Admitted.

Lemma Triple_eta_con2 {sig : finType} {n : nat} {F : Type} (pM : pTM sig F n) (P : Assert sig n) (Q : F -> Assert sig n) : Triple P pM Q -> Triple P pM (fun yout tout => Q yout tout).
Proof.
Admitted.

Lemma Triple_and_con {sig : finType} {n : nat} {F : Type} (pM : pTM sig F n) (P : Assert sig n) (Q1 : F -> Assert sig n) (Q2 : Prop) : Triple P pM Q1 -> Q2 -> Triple P pM (fun yout tout => Q2 /\ Q1 yout tout).
Proof.
setoid_rewrite Triple_iff.
unfold Triple_Rel.
Admitted.

Lemma TripleT_exists_pre {sig : finType} {n : nat} {F : Type} (pM : pTM sig F n) (X : Type) (P : X -> Assert sig n) (Q : F -> Assert sig n) k : (forall (x : X), TripleT (P x) k pM Q) -> TripleT (fun tin => exists x : X, P x tin) k pM (Q).
Proof.
setoid_rewrite TripleT_iff;setoid_rewrite Triple_iff.
unfold Triple_Rel,Triple_TRel.
Admitted.

Lemma TripleT_exists_con {sig : finType} {n : nat} {F : Type} (pM : pTM sig F n) (X : Type) (P : Assert sig n) (Q : X -> F -> Assert sig n) k : (exists (x : X), TripleT P k pM (Q x)) -> TripleT P k pM (fun yout tout => exists x : X, Q x yout tout).
Proof.
setoid_rewrite TripleT_iff;setoid_rewrite Triple_iff.
unfold Triple_Rel,Triple_TRel.
Admitted.

Lemma TripleT_forall_pre {sig : finType} {n : nat} {F : Type} (pM : pTM sig F n) (X : Type) (P : X -> Assert sig n) (Q : F -> Assert sig n) k : (exists (x : X), TripleT (P x) k pM Q) -> TripleT (fun tin => forall x : X, P x tin) k pM (Q).
Proof.
setoid_rewrite TripleT_iff;setoid_rewrite Triple_iff.
unfold Triple_Rel,Triple_TRel.
Admitted.

Lemma TripleT_forall_con {sig : finType} {n : nat} {F : Type} (pM : pTM sig F n) (X : Type) (P : Assert sig n) (Q : X -> F -> Assert sig n) k {inhX: inhabitedC X} : (forall (x : X), TripleT P k pM (Q x)) -> TripleT P k pM (fun yout tout => forall x : X, Q x yout tout).
Proof.
intros H; split.
-
apply Triple_forall_con.
apply H.
-
apply H.
Admitted.

Lemma TripleT_eta_pre {sig : finType} {n : nat} {F : Type} (pM : pTM sig F n) (P : Assert sig n) (Q : F -> Assert sig n) k : TripleT P k pM Q -> TripleT (fun tin => P tin) k pM Q.
Proof.
Admitted.

Lemma TripleT_eta_con {sig : finType} {n : nat} {F : Type} (pM : pTM sig F n) (P : Assert sig n) (Q : F -> Assert sig n) k : TripleT P k pM Q -> TripleT P k pM (fun yout => Q yout).
Proof.
Admitted.

Lemma TripleT_eta_con2 {sig : finType} {n : nat} {F : Type} (pM : pTM sig F n) (P : Assert sig n) (Q : F -> Assert sig n) k : TripleT P k pM Q -> TripleT P k pM (fun yout tout => Q yout tout).
Proof.
Admitted.

Lemma TripleT_and_pre {sig : finType} {n : nat} {F : Type} (pM : pTM sig F n) (P1 : Assert sig n) (P2 : Prop) (Q : F -> Assert sig n) k : (P2 -> TripleT P1 k pM Q) -> TripleT (fun tin => P2 /\ P1 tin) k pM Q.
Proof.
setoid_rewrite TripleT_iff;setoid_rewrite Triple_iff.
unfold Triple_Rel,Triple_TRel.
Admitted.

Lemma TripleT_and_con {sig : finType} {n : nat} {F : Type} (pM : pTM sig F n) (P : Assert sig n) (Q1 : F -> Assert sig n) (Q2 : Prop) k : TripleT P k pM Q1 -> Q2 -> TripleT P k pM (fun yout tout => Q2 /\ Q1 yout tout).
Proof.
setoid_rewrite TripleT_iff;setoid_rewrite Triple_iff.
unfold Triple_Rel,Triple_TRel.
Admitted.

Lemma Triple_and_pre {sig : finType} {n : nat} {F : Type} (pM : pTM sig F n) (P1 : Assert sig n) (P2 : Prop) (Q : F -> Assert sig n) : (P2 -> Triple P1 pM Q) -> Triple (fun tin => P2 /\ P1 tin) pM Q.
Proof.
setoid_rewrite Triple_iff.
unfold Triple_Rel.
firstorder.
