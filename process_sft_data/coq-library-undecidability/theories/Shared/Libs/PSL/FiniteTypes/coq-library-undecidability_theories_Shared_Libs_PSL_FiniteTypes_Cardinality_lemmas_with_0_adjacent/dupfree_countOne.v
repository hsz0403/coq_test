From Undecidability.Shared.Libs.PSL Require Import FinTypes.
Definition Cardinality (F: finType) := | elem F |.

Lemma dupfree_countOne (X: eqType) (A: list X) : (forall x, count A x <= 1) -> dupfree A.
Proof.
induction A.
-
constructor.
-
intro H.
constructor.
+
cbn in H.
specialize (H a).
deq a.
assert (count A a = 0) by lia.
now apply countZero.
+
apply IHA.
intro x.
specialize (H x).
cbn in H.
dec; lia.
