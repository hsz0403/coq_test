From Undecidability Require Import TMTac TM.Util.Prelim.
From Undecidability.TM Require Export Compound.Multi Combinators.Combinators.
From Undecidability.TM.Hoare Require Import HoareLogic HoareRegister.

Lemma If_SpecT_weak' (sig : finType) (n : nat) (F : finType) (pM1 : pTM sig bool n) (pM2 pM3 : pTM sig F n) (P : Assert sig n) (Q : bool -> Assert sig n) (R : F -> Assert sig n) (k k1 k2 : nat) : TripleT P k1 pM1 Q -> TripleT (Q true) k2 pM2 R -> TripleT (Q false) k2 pM3 R -> (1 + k1 + k2 <= k) -> TripleT P k (If pM1 pM2 pM3) R.
Proof.
intros H1 H2 H3 H4.
eapply ConsequenceT_pre.
-
eapply If_SpecT_weak with (k2 := k2) (k3 := k2); eauto.
-
auto.
-
now rewrite Nat.max_id.
