Require Export Arith.
Require Export ArithRing.
Require Export Omega.
Unset Standard Proposition Elimination Names.

Lemma plus_minus_lemma2 : forall (x y z:nat),(y<=x)->(x-y+z)=(x+z-y).
intros.
rewrite (le_plus_minus y x);try (auto with arith).
rewrite minus_plus;rewrite <- plus_assoc;rewrite minus_plus;trivial.
