Require Export Arith.
Require Export ArithRing.
Require Export Omega.
Unset Standard Proposition Elimination Names.

Lemma minus_lemma1 : forall (a b:nat),(S a-S b)<S a.
intros.
omega.
