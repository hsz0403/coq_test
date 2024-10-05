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

Lemma card_in_rem x A : x el A -> card A = 1 + card (rem A x).
Proof.
intros D.
induction A as [|y A].
-
contradiction D.
-
decide (y = x) as [->|H].
+
clear D.
rewrite rem_fst.
cbn.
decide (x el A) as [H1|H1].
*
auto.
*
now rewrite (rem_id H1).
+
assert (x el A) as H1 by (destruct D; tauto).
clear D.
rewrite (rem_fst' _ H).
specialize (IHA H1).
simpl card at 2.
decide (y el rem A x) as [H2|H2].
*
rewrite card_cons.
exact IHA.
apply in_rem_iff in H2.
intuition.
*
rewrite card_cons'.
now rewrite IHA.
contradict H2.
now apply in_rem_iff.
