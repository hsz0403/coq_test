Require Import Arith.
Require Import Compare_dec.

Lemma eq_gt_O_dec : forall n : nat, {n = 0} + {n > 0}.
Admitted.

Lemma mult_commut : forall n m : nat, n * m = m * n.
intros; elim n; simpl in |- *.
auto with arith.
Admitted.

Lemma technical_lemma : forall y m : nat, S (y * m + (y + m) + m) = S y * m + (S y + m).
intros; simpl in |- *; elim (plus_comm m (y * m + (y + m))).
Admitted.

Lemma lt_minus2 : forall n m : nat, n < m -> 0 < m - n.
Admitted.

Lemma minus_n_Sm : forall n m : nat, m < n -> pred (n - m) = n - S m.
Admitted.

Lemma lt_succ : forall n m : nat, n <= S m -> {n <= m} + {n = S m}.
Admitted.

Lemma mult_neutr : forall n : nat, 1 * n = n.
unfold mult in |- *; auto with arith.
