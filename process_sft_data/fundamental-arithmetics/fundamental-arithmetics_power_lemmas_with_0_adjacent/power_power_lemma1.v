Require Import missing.
Require Import division.
Unset Standard Proposition Elimination Names.
Definition square (x:nat) := x*x.
Fixpoint power (x n:nat) {struct n} : nat := match n with O => 1 | (S n) => (x*(power x n)) end.

Lemma power_power_lemma1 : forall (n m x:nat),(power (power x n) m)=(power x (n*m)).
induction n;simpl;intros.
induction m;simpl;auto with arith.
rewrite IHm;ring.
rewrite power_mult_lemma1;rewrite IHn;rewrite <- power_plus_lemma1;trivial.
