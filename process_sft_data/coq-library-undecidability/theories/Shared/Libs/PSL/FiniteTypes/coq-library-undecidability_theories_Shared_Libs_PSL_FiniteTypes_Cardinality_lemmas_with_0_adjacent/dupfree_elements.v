From Undecidability.Shared.Libs.PSL Require Import FinTypes.
Definition Cardinality (F: finType) := | elem F |.

Lemma dupfree_elements (X: finType) : dupfree (elem X).
Proof.
destruct X as [X [A AI]].
assert (forall x, count A x <= 1) as H'.
{
intro x.
specialize (AI x).
lia.
}
now apply dupfree_countOne.
