Require Import Arith.
Require Import Compare_dec.

Lemma eq_gt_O_dec : forall n : nat, {n = 0} + {n > 0}.
simple destruct n; auto with arith.
