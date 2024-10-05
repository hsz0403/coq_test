Require Export Arith.
Require Export ArithRing.
Require Export Omega.
Unset Standard Proposition Elimination Names.

Lemma mult_lemma2 : forall (n m:nat),(n*m = O)->(n=O)\/(m=O).
intros.
induction n.
tauto.
simpl in H.
right.
assert (m <= O);try omega.
rewrite <- H.
auto with arith.
