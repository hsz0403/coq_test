From Undecidability.Shared.Libs.PSL Require Export BaseLists Removal.
Section Cardinality.
Variable X : eqType.
Implicit Types A B : list X.
Fixpoint card A := match A with | nil => 0 | x::A => if Dec (x el A) then card A else 1 + card A end.
End Cardinality.
Instance card_equi_proper (X: eqType) : Proper (@equi X ==> eq) (@card X).
Proof.
hnf.
apply card_eq.

Lemma card_or A B : A <<= B -> A === B \/ card A < card B.
Proof.
intros D.
decide (card A = card B) as [F|F].
-
left.
apply card_equi; auto.
-
right.
apply card_le in D.
lia.
