From Undecidability Require Import TMTac TM.Util.Prelim.
From Undecidability.TM Require Export Compound.Multi Combinators.Combinators.
From Undecidability.TM.Hoare Require Import HoareLogic HoareRegister.

Lemma Return_SpecT (sig : finType) (F1 F2 : finType) (n : nat) (P : Assert sig n) (k : nat) (Q : F1 -> Assert sig n) (pM : pTM sig F1 n) (y : F2) : TripleT P k pM Q -> TripleT P k (Return pM y) (fun y' t => y' = y /\ exists y'', Q y'' t).
Proof.
split.
-
apply Return_Spec; eauto.
-
eapply TerminatesIn_monotone.
+
TM_Correct.
apply H.
+
firstorder.
