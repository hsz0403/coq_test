Require Import missing.
Require Import division.
Unset Standard Proposition Elimination Names.
Definition square (x:nat) := x*x.
Fixpoint power (x n:nat) {struct n} : nat := match n with O => 1 | (S n) => (x*(power x n)) end.

Lemma square_mult_lemma : forall (a b:nat),(square (a*b))=((square a)*(square b)).
unfold square.
intros.
Admitted.

Lemma power_mult_lemma1 : forall (n x y:nat),(power (x*y) n)=(power x n)*(power y n).
induction n;simpl;trivial.
Admitted.

Lemma power_plus_lemma1 : forall (n m x:nat),(power x (n+m))=(power x n)*(power x m).
induction n;simpl;intros.
auto with arith.
Admitted.

Lemma power_divides_lemma1 : forall (n x:nat),(0<n)->(divides (power x n) x).
induction n;simpl;intros.
inversion H.
Admitted.

Lemma power_power_lemma1 : forall (n m x:nat),(power (power x n) m)=(power x (n*m)).
induction n;simpl;intros.
induction m;simpl;auto with arith.
rewrite IHm;ring.
Admitted.

Lemma power_lt : forall (p m:nat),(1<p)->(0<m)->1<(power p m).
induction m;simpl;try omega;intros.
destruct m;simpl;try omega.
simpl in IHm.
assert (1 < p*(power p m)).
apply IHm;auto with arith.
rewrite mult_comm.
apply lt_trans with (1*p);try omega.
Admitted.

Lemma power_one : forall (n:nat),(power 1 n)=1.
induction n;simpl;trivial.
Admitted.

Lemma power_divides_power : forall (x n m:nat),(x>1)->(divides (power x n) (power x m))->(m<=n).
intros.
case (le_lt_dec m n);trivial.
intro.
generalize (le_plus_minus n m);intro.
rewrite H1 in H0;try omega.
elim H0;intro q;rewrite power_plus_lemma1;intro.
assert (1=(power x (m-n))*q).
apply mult_lemma6 with (power x n).
intro;generalize (power_zero n x H3);omega.
rewrite mult_assoc;rewrite <- H2;ring.
symmetry in H3;elim (mult_lemma5 (power x (m-n)) q H3);intros.
case (eq_nat_dec (m-n) 0);intro;try omega.
assert (x=1);try omega.
Admitted.

Lemma power_zero : forall (n x:nat),(power x n)=O->x=O.
induction n;simpl;intros.
discriminate.
case (mult_lemma2 x (power x n) H);auto.
