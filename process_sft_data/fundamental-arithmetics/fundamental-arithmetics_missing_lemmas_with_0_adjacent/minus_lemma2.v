Require Export Arith.
Require Export ArithRing.
Require Export Omega.
Unset Standard Proposition Elimination Names.

Lemma minus_lemma2 : forall (n m:nat),(n<=m)->(n-m=O).
intros.
omega.
