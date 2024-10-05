Require Import missing.
Require Import division.
Unset Standard Proposition Elimination Names.
Definition square (x:nat) := x*x.
Fixpoint power (x n:nat) {struct n} : nat := match n with O => 1 | (S n) => (x*(power x n)) end.

Lemma power_mult_lemma1 : forall (n x y:nat),(power (x*y) n)=(power x n)*(power y n).
induction n;simpl;trivial.
intros;rewrite (IHn x y);ring.
