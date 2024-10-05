From Undecidability Require Import TMTac TM.Util.Prelim.
From Undecidability.TM Require Export Compound.Multi Combinators.Combinators.
From Undecidability.TM.Hoare Require Import HoareLogic HoareRegister.

Lemma If_SpecT_weak (sig : finType) (n : nat) (F : finType) (pM1 : pTM sig bool n) (pM2 pM3 : pTM sig F n) (P : Assert sig n) (Q : bool -> Assert sig n) (R : F -> Assert sig n) (k k1 k2 k3 : nat) : TripleT P k1 pM1 Q -> TripleT (Q true) k2 pM2 R -> TripleT (Q false) k3 pM3 R -> (1 + k1 + max k2 k3 <= k) -> TripleT P k (If pM1 pM2 pM3) R.
Proof.
intros.
eapply If_SpecT; eauto.
intros.
destruct yout.
+
assert (k2 <= max k2 k3) by apply Nat.le_max_l.
lia.
+
assert (k3 <= max k2 k3) by apply Nat.le_max_r.
lia.
