Require Export Arith.
Require Export ArithRing.
Require Export Omega.
Unset Standard Proposition Elimination Names.

Lemma mult_lemma1 : forall (n m:nat),(n <> O)->(m <> 0)->(n <= n*m).
intros.
rewrite mult_comm.
induction m;simpl;auto with arith.
elim H0;trivial.
