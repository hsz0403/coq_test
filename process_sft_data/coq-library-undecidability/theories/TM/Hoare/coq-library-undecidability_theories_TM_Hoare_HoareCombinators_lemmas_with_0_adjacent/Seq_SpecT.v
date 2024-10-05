From Undecidability Require Import TMTac TM.Util.Prelim.
From Undecidability.TM Require Export Compound.Multi Combinators.Combinators.
From Undecidability.TM.Hoare Require Import HoareLogic HoareRegister.

Lemma Seq_SpecT (sig : finType) (n : nat) (F1 F2 : finType) (pM1 : pTM sig F1 n) (pM2 : pTM sig F2 n) (P : Assert sig n) (Q : F1 -> Assert sig n) (R : F2 -> Assert sig n) (k k1 k2 : nat) : TripleT P k1 pM1 Q -> (* Correctness of [pM1] *) (forall (ymid : F1), TripleT (Q ymid) k2 pM2 R) -> (* Correctness of [pM2] (for every output label of [pM1]) *) 1 + k1 + k2 <= k -> TripleT P k (pM1;; pM2) R.
Proof.
intros.
eapply Seq_SpecT_strong; eauto.
