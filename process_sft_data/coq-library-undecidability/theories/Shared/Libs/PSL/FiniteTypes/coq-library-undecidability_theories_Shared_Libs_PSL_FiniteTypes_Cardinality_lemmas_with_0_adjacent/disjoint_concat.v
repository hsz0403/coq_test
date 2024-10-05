From Undecidability.Shared.Libs.PSL Require Import FinTypes.
Definition Cardinality (F: finType) := | elem F |.

Lemma disjoint_concat X (A: list (list X)) (B: list X) : (forall C, C el A -> disjoint B C) -> disjoint B (concat A).
Proof.
intros H.
induction A.
-
cbn.
auto.
-
cbn.
apply disjoint_symm.
apply disjoint_app.
split; auto using disjoint_symm.
