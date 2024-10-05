Require Export Arith.
Require Export ArithRing.
Require Export Omega.
Unset Standard Proposition Elimination Names.

Lemma mult_lemma6 : forall (a b n:nat),(n <> O)->(n*a=n*b)->(a=b).
induction a.
intros;rewrite <- mult_n_O in H0; generalize (mult_lemma2 n b); intros Hl2; elim Hl2; intros; (auto || elim H ; auto).
intros b n H.
rewrite mult_comm;simpl;rewrite mult_comm;intro.
assert (n*a = n*b-n).
apply plus_minus;auto.
assert (a*n=(b-1)*n).
rewrite <- mult_minus_lemma1;rewrite mult_comm;rewrite (mult_comm b n);trivial.
assert (a=(b-1)).
apply (IHa (b-1) n);trivial.
rewrite mult_comm;rewrite (mult_comm n (b-1));trivial.
destruct b;simpl in H3.
rewrite H3 in H0;rewrite (mult_comm n 0) in H0;rewrite plus_comm in H0;simpl in H0;elim H;trivial.
rewrite <- minus_n_O in H3;auto.
