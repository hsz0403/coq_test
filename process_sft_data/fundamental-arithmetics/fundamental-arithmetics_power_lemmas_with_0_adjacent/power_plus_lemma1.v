Require Import missing.
Require Import division.
Unset Standard Proposition Elimination Names.
Definition square (x:nat) := x*x.
Fixpoint power (x n:nat) {struct n} : nat := match n with O => 1 | (S n) => (x*(power x n)) end.

Lemma power_plus_lemma1 : forall (n m x:nat),(power x (n+m))=(power x n)*(power x m).
induction n;simpl;intros.
auto with arith.
rewrite IHn;ring.
