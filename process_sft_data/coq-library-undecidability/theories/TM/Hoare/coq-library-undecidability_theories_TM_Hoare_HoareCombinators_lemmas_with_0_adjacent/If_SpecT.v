From Undecidability Require Import TMTac TM.Util.Prelim.
From Undecidability.TM Require Export Compound.Multi Combinators.Combinators.
From Undecidability.TM.Hoare Require Import HoareLogic HoareRegister.

Lemma If_SpecT (sig : finType) (n : nat) (F : finType) (pM1 : pTM sig bool n) (pM2 pM3 : pTM sig F n) (P : Assert sig n) (Q : bool -> Assert sig n) (R : F -> Assert sig n) (k k1 k2 k3 : nat) : TripleT P k1 pM1 Q -> TripleT (Q true) k2 pM2 R -> TripleT (Q false) k3 pM3 R -> (forall tin yout tout, P tin -> Q yout tout -> (1 + k1 + if yout then k2 else k3) <= k) -> TripleT P k (If pM1 pM2 pM3) R.
Proof.
intros H1 H2 H3 H4.
split.
-
eapply If_Spec.
+
apply H1.
+
apply H2.
+
apply H3.
-
eapply TerminatesIn_monotone.
{
apply If_TerminatesIn'.
-
apply H1.
-
apply H1.
-
apply H2.
-
apply H3.
}
{
unfold Triple_Rel, Triple_TRel.
intros tin k' (H&Hk).
specialize H4 with (1 := H).
exists k1.
repeat split.
-
assumption.
-
reflexivity.
-
intros tmid ymid Hmid.
modpon Hmid.
modpon H4.
destruct ymid; cbn in *.
+
exists k2.
repeat split; auto.
lia.
+
exists k3.
repeat split; auto.
lia.
}
