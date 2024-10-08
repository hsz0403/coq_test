Require Export Arith.
Require Export ArithRing.
Require Export Omega.
Unset Standard Proposition Elimination Names.

Lemma mult_lemma1 : forall (n m:nat),(n <> O)->(m <> 0)->(n <= n*m).
intros.
rewrite mult_comm.
induction m;simpl;auto with arith.
Admitted.

Lemma mult_lemma2 : forall (n m:nat),(n*m = O)->(n=O)\/(m=O).
intros.
induction n.
tauto.
simpl in H.
right.
assert (m <= O);try omega.
rewrite <- H.
Admitted.

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
Admitted.

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
Admitted.

Lemma plus_minus_lemma1 : forall (y x:nat),(x+y-y=x).
induction y;intros;rewrite plus_comm;simpl.
auto with arith.
rewrite plus_comm.
Admitted.

Lemma mult_minus_lemma1 : forall (a n:nat),a*n-n = (a-1)*n.
intros.
induction a.
simpl.
trivial.
replace (S a*n) with (n+a*n);try (auto with arith).
rewrite plus_comm.
rewrite plus_minus_lemma1.
simpl.
Admitted.

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
Admitted.

Lemma mult_lemma7 : forall (x y z t:nat),x*y*(z*t)=z*(x*y*t).
intros.
Admitted.

Lemma minus_lemma1 : forall (a b:nat),(S a-S b)<S a.
intros.
Admitted.

Lemma minus_lemma2 : forall (n m:nat),(n<=m)->(n-m=O).
intros.
Admitted.

Lemma mult_minus_lemma2 : forall (x y z:nat),(x*(y-z))=(x*y-x*z).
intros.
case (le_lt_dec y z);intro.
rewrite (minus_lemma2 y z l);rewrite mult_comm;simpl;rewrite minus_lemma2;trivial;auto with arith.
assert (y=z+(y-z)).
rewrite <- (le_plus_minus z y);try (auto with arith).
replace (x*y) with (x*(z+(y-z))).
rewrite mult_plus_distr_l;rewrite minus_plus;trivial.
Admitted.

Lemma plus_minus_lemma2 : forall (x y z:nat),(y<=x)->(x-y+z)=(x+z-y).
intros.
rewrite (le_plus_minus y x);try (auto with arith).
Admitted.

Lemma minus_minus_lemma1 : forall (x y z:nat),(z<=y)->(x-(y-z))=(x+z-y).
intros.
rewrite (le_plus_minus z y);trivial.
Admitted.

Lemma minus_minus_lemma2 : forall (x y z:nat),(x-y-z)=(x-(y+z)).
induction x;simpl;trivial.
intros.
Admitted.

Lemma minus_lt_lemma1 : forall (b a:nat),(a<b)->(0<b-a).
intros.
Admitted.

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
