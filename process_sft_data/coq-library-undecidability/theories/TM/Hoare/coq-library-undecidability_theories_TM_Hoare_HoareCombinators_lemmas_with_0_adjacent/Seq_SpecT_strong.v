From Undecidability Require Import TMTac TM.Util.Prelim.
From Undecidability.TM Require Export Compound.Multi Combinators.Combinators.
From Undecidability.TM.Hoare Require Import HoareLogic HoareRegister.

Lemma Seq_SpecT_strong (sig : finType) (n : nat) (F1 F2 : finType) (pM1 : pTM sig F1 n) (pM2 : pTM sig F2 n) (P : Assert sig n) (Q : F1 -> Assert sig n) (R : F2 -> Assert sig n) (k k1 k2 : nat) : TripleT P k1 pM1 Q -> (* Correctness of [pM1] *) (forall (ymid : F1), TripleT (Q ymid) k2 pM2 R) -> (* Correctness of [pM2] (for every output label of [pM1]) *) (forall tin ymid tmid, P tin -> Q ymid tmid -> 1 + k1 + k2 <= k) -> TripleT P k (pM1;; pM2) R.
Proof.
intros H1 H2 H3.
split.
-
eapply Seq_Spec.
+
apply H1.
+
cbn.
apply H2.
-
eapply TerminatesIn_monotone.
{
apply Seq_TerminatesIn'.
-
apply H1.
-
apply H1.
-
instantiate (1 := fun tmid k2' => exists ymid, Q ymid tmid /\ k2 <= k2').
{
clear H1 H3.
setoid_rewrite TripleT_iff in H2.
unfold TerminatesIn in *.
firstorder.
}
}
{
clear H1 H2.
intros tin k' (HP&Hk).
unfold Triple_TRel in *.
exists k1.
repeat split; eauto.
unfold Triple_Rel.
intros ymid tmid HQ.
modpon HQ.
specialize H3 with (1 := HP) (2 := HQ).
exists k2.
split; eauto.
lia.
}
