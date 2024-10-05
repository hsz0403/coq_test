Require Export Arith.
Require Export ArithRing.
Require Export Omega.
Unset Standard Proposition Elimination Names.

Lemma mult_lemma5 : forall (n m:nat),((n * m) =1)->(n=1)/\(m=1).
induction n;simpl;intros;try discriminate.
induction m.
rewrite mult_comm in H.
simpl in H;discriminate.
assert ((S n)<=((S n)*(S m))).
apply mult_lemma1;discriminate.
assert (((S n)*(S m))=((S m)+n*(S m))).
reflexivity.
rewrite H1 in H0.
rewrite H in H0.
assert ((S n)=1).
omega.
split;trivial.
inversion H2.
rewrite H4 in H.
simpl in H.
omega.
