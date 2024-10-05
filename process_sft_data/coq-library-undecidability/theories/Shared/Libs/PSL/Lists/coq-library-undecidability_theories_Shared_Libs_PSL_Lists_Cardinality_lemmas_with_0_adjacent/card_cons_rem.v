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

Lemma card_cons_rem x A : card (x::A) = 1 + card (rem A x).
Proof.
rewrite (card_eq (rem_equi x A)).
cbn.
decide (x el rem A x) as [D|D].
-
exfalso.
apply in_rem_iff in D; tauto.
-
reflexivity.
