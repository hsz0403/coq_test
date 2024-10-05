Require Import Arith.
Require Import Compare_dec.

Lemma lt_succ : forall n m : nat, n <= S m -> {n <= m} + {n = S m}.
intros; elim (le_lt_eq_dec n (S m) H); auto with arith.
