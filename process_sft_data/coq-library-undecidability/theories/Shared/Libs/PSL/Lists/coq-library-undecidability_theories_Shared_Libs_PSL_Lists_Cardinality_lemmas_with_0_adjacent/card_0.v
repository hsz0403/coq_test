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

Lemma card_0 A : card A = 0 -> A = nil.
Proof.
destruct A as [|x A]; intros D.
-
reflexivity.
-
exfalso.
rewrite card_cons_rem in D.
lia.
