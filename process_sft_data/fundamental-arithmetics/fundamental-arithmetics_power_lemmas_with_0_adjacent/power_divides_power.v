Require Import missing.
Require Import division.
Unset Standard Proposition Elimination Names.
Definition square (x:nat) := x*x.
Fixpoint power (x n:nat) {struct n} : nat := match n with O => 1 | (S n) => (x*(power x n)) end.

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
apply divides_antisym;[apply one_min_div | rewrite <- H4;apply power_divides_lemma1;omega].
