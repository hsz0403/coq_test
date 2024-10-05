Require Import missing.
Require Import division.
Unset Standard Proposition Elimination Names.
Definition square (x:nat) := x*x.
Fixpoint power (x n:nat) {struct n} : nat := match n with O => 1 | (S n) => (x*(power x n)) end.

Lemma square_mult_lemma : forall (a b:nat),(square (a*b))=((square a)*(square b)).
unfold square.
intros.
ring.
