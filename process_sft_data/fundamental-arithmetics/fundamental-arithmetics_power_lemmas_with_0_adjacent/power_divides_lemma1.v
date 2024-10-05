Require Import missing.
Require Import division.
Unset Standard Proposition Elimination Names.
Definition square (x:nat) := x*x.
Fixpoint power (x n:nat) {struct n} : nat := match n with O => 1 | (S n) => (x*(power x n)) end.

Lemma power_divides_lemma1 : forall (n x:nat),(0<n)->(divides (power x n) x).
induction n;simpl;intros.
inversion H.
exists (power x n);trivial.
