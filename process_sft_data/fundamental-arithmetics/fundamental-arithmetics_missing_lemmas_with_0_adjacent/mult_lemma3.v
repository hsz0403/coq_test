Require Export Arith.
Require Export ArithRing.
Require Export Omega.
Unset Standard Proposition Elimination Names.

Lemma mult_lemma3 : forall (n m:nat),(n <> O)->(m > 1)->(n < n*m).
intros.
rewrite mult_comm.
induction m.
inversion H0.
simpl.
assert (O < m*n);try omega.
inversion H0;try omega.
assert (1 <= n);try omega.
assert (m > 1);try omega.
generalize (IHm H4);omega.
