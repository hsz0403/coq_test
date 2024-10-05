Require Import Arith.
Require Import Compare_dec.

Lemma lt_minus2 : forall n m : nat, n < m -> 0 < m - n.
simple induction 1; intros; elim minus_Sn_m; auto with arith.
