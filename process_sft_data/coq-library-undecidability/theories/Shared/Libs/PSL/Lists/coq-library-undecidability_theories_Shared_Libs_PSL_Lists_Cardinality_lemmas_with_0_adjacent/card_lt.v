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

Lemma card_lt A B x : A <<= B -> x el B -> ~ x el A -> card A < card B.
Proof.
intros D E F.
decide (card A = card B) as [G|G].
+
exfalso.
apply F.
apply (card_equi D); auto.
+
apply card_le in D.
lia.
