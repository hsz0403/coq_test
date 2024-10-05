Require Export Arith.
Require Export ArithRing.
Require Export Omega.
Unset Standard Proposition Elimination Names.

Lemma mult_minus_lemma1 : forall (a n:nat),a*n-n = (a-1)*n.
intros.
induction a.
simpl.
trivial.
replace (S a*n) with (n+a*n);try (auto with arith).
rewrite plus_comm.
rewrite plus_minus_lemma1.
simpl.
rewrite <- minus_n_O;trivial.
