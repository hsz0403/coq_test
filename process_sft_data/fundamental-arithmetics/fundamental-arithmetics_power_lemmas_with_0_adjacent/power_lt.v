Require Import missing.
Require Import division.
Unset Standard Proposition Elimination Names.
Definition square (x:nat) := x*x.
Fixpoint power (x n:nat) {struct n} : nat := match n with O => 1 | (S n) => (x*(power x n)) end.

Lemma power_lt : forall (p m:nat),(1<p)->(0<m)->1<(power p m).
induction m;simpl;try omega;intros.
destruct m;simpl;try omega.
simpl in IHm.
assert (1 < p*(power p m)).
apply IHm;auto with arith.
rewrite mult_comm.
apply lt_trans with (1*p);try omega.
apply mult_lt_compat_r;try omega.
