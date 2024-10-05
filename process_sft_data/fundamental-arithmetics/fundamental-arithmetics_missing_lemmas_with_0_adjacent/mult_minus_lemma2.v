Require Export Arith.
Require Export ArithRing.
Require Export Omega.
Unset Standard Proposition Elimination Names.

Lemma mult_minus_lemma2 : forall (x y z:nat),(x*(y-z))=(x*y-x*z).
intros.
case (le_lt_dec y z);intro.
rewrite (minus_lemma2 y z l);rewrite mult_comm;simpl;rewrite minus_lemma2;trivial;auto with arith.
assert (y=z+(y-z)).
rewrite <- (le_plus_minus z y);try (auto with arith).
replace (x*y) with (x*(z+(y-z))).
rewrite mult_plus_distr_l;rewrite minus_plus;trivial.
rewrite <- H;trivial.
