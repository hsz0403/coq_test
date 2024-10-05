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

Lemma card_le A B : A <<= B -> card A <= card B.
Proof.
revert B.
induction A as [|x A]; intros B D; cbn.
-
lia.
-
apply incl_lcons in D as [D D1].
decide (x el A) as [E|E].
+
auto.
+
rewrite (card_in_rem D).
enough (card A <= card (rem B x)) by lia.
apply IHA.
auto.
