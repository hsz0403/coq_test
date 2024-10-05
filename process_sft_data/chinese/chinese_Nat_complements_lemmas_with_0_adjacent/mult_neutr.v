Require Import Arith.
Require Import Compare_dec.

Lemma mult_neutr : forall n : nat, 1 * n = n.
unfold mult in |- *; auto with arith.
