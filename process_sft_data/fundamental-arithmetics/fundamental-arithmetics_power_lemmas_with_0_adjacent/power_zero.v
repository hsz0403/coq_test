Require Import missing.
Require Import division.
Unset Standard Proposition Elimination Names.
Definition square (x:nat) := x*x.
Fixpoint power (x n:nat) {struct n} : nat := match n with O => 1 | (S n) => (x*(power x n)) end.

Lemma power_zero : forall (n x:nat),(power x n)=O->x=O.
induction n;simpl;intros.
discriminate.
case (mult_lemma2 x (power x n) H);auto.
