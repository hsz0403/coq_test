From Undecidability.Shared.Libs.PSL Require Import FinTypes.
Definition Cardinality (F: finType) := | elem F |.

Lemma dupfree_length (X: finType) (A: list X) : dupfree A -> |A| <= Cardinality X.
Proof.
unfold Cardinality.
intros D.
rewrite <- (dupfree_card D).
rewrite <- (dupfree_card (dupfree_elements X)).
apply card_le.
apply allSub.
