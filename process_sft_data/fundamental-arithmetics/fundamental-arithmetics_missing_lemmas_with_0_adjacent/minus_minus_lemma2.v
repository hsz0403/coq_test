Require Export Arith.
Require Export ArithRing.
Require Export Omega.
Unset Standard Proposition Elimination Names.

Lemma minus_minus_lemma2 : forall (x y z:nat),(x-y-z)=(x-(y+z)).
induction x;simpl;trivial.
intros.
case y;simpl;trivial.
