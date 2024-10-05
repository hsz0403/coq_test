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

Lemma card_equi A B : A <<= B -> card A = card B -> A === B.
Proof.
revert B.
induction A as [|x A]; cbn; intros B D E.
-
symmetry in E.
apply card_0 in E.
now rewrite E.
-
apply incl_lcons in D as [D D1].
decide (x el A) as [F|F].
+
rewrite (IHA B); auto.
+
rewrite (IHA (rem B x)).
*
symmetry.
apply rem_reorder, D.
*
auto.
*
apply card_in_rem in D.
lia.
