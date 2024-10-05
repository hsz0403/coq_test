Require Import Arith.
Require Import Compare_dec.

Lemma minus_n_Sm : forall n m : nat, m < n -> pred (n - m) = n - S m.
simple induction 1; intros; elim minus_Sn_m; auto with arith.
