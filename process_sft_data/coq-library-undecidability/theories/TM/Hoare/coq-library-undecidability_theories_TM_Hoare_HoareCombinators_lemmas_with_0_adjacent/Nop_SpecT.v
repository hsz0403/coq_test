From Undecidability Require Import TMTac TM.Util.Prelim.
From Undecidability.TM Require Export Compound.Multi Combinators.Combinators.
From Undecidability.TM.Hoare Require Import HoareLogic HoareRegister.

Lemma Nop_SpecT (sig : finType) (n : nat) (P : Assert sig n) : TripleT P 0 Nop (fun _ => P).
Proof.
split.
-
eapply Consequence_pre.
apply Nop_Spec.
firstorder.
-
eapply TerminatesIn_monotone.
+
TM_Correct.
+
firstorder.
