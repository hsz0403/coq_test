Require Export Arith.
Require Export ArithRing.
Require Export Omega.
Unset Standard Proposition Elimination Names.

Lemma minus_lt_lemma1 : forall (b a:nat),(a<b)->(0<b-a).
intros.
omega.
