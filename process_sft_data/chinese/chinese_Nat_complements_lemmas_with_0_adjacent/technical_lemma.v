Require Import Arith.
Require Import Compare_dec.

Lemma technical_lemma : forall y m : nat, S (y * m + (y + m) + m) = S y * m + (S y + m).
intros; simpl in |- *; elim (plus_comm m (y * m + (y + m))).
rewrite (plus_assoc m (y * m) (y + m)); auto with arith.
