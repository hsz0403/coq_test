Require Import missing.
Require Import division.
Unset Standard Proposition Elimination Names.
Definition square (x:nat) := x*x.
Fixpoint power (x n:nat) {struct n} : nat := match n with O => 1 | (S n) => (x*(power x n)) end.

Lemma power_one : forall (n:nat),(power 1 n)=1.
induction n;simpl;trivial.
rewrite IHn;ring.
