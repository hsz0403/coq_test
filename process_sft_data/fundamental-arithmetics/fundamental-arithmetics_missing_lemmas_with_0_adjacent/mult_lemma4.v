Require Export Arith.
Require Export ArithRing.
Require Export Omega.
Unset Standard Proposition Elimination Names.

Lemma mult_lemma4 : forall (n m:nat),n=n*m -> n=O \/ m=1.
intros n m.
case n.
left;trivial.
intros.
right.
destruct m.
rewrite mult_comm in H.
discriminate.
destruct m;trivial.
assert ((S n0)<(S n0)*(S (S m))).
apply mult_lemma3;intros;auto with arith.
rewrite <- H in H0.
elim (lt_irrefl (S n0) H0).
