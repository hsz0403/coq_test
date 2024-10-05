From Undecidability Require Import TMTac TM.Util.Prelim.
From Undecidability.TM Require Export Compound.Multi Combinators.Combinators.
From Undecidability.TM.Hoare Require Import HoareLogic HoareRegister.

Lemma Seq_Spec_swapped (sig : finType) (n : nat) (F1 F2 : finType) (pM1 : pTM sig F1 n) (pM2 : pTM sig F2 n) (P : Assert sig n) (Q : F1 -> Assert sig n) (R : F2 -> Assert sig n) : (forall ymid, Triple (Q ymid) pM2 R) -> Triple P pM1 Q -> Triple P (pM1;;pM2) R.
Proof.
eauto using Seq_Spec.
