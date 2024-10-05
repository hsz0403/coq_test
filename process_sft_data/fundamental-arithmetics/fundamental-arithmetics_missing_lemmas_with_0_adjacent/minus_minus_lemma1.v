Require Export Arith.
Require Export ArithRing.
Require Export Omega.
Unset Standard Proposition Elimination Names.

Lemma minus_minus_lemma1 : forall (x y z:nat),(z<=y)->(x-(y-z))=(x+z-y).
intros.
rewrite (le_plus_minus z y);trivial.
rewrite minus_plus;rewrite plus_comm;rewrite <- minus_plus_simpl_l_reverse;trivial.
