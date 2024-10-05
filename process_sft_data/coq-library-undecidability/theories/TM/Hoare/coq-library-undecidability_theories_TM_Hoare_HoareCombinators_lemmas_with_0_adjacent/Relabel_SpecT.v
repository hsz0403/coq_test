From Undecidability Require Import TMTac TM.Util.Prelim.
From Undecidability.TM Require Export Compound.Multi Combinators.Combinators.
From Undecidability.TM.Hoare Require Import HoareLogic HoareRegister.

Lemma Relabel_SpecT (sig : finType) (F1 F2 : finType) (n : nat) (P : Assert sig n) (k : nat) (Q : F1 -> Assert sig n) (pM : pTM sig F1 n) (f : F1->F2) : TripleT P k pM Q -> TripleT P k (Relabel pM f) (fun y' t => exists y'', y' = f y'' /\ Q y'' t).
Proof.
split.
-
apply Relabel_Spec; eauto.
-
eapply TerminatesIn_monotone.
+
TM_Correct.
apply H.
+
firstorder.
