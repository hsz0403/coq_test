Require Import Arith.
Require Import Compare_dec.

Lemma mult_commut : forall n m : nat, n * m = m * n.
intros; elim n; simpl in |- *.
auto with arith.
intros; rewrite H; elim mult_n_Sm; auto with arith.
