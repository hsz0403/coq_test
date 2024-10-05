Require Import Arith.
Fixpoint le_bool (n m: nat) {struct n}: bool := match n, m with | O, _ => true | S n1, S m1 => le_bool n1 m1 | _, _ => false end.
Fixpoint lt_bool (n m: nat) {struct n}: bool := match n, m with | O, S _ => true | S n1, S m1 => lt_bool n1 m1 | _, _ => false end.
Hint Extern 4 (?X1 <= ?X2)%nat => exact (le_correct X1 X2 (refl_equal true)) : core.
Hint Extern 4 (?X1 < ?X2)%nat => exact (lt_correct X1 X2 (refl_equal true)) : core.

Theorem le_correct: forall n m, le_bool n m = true -> n <= m.
Proof.
Admitted.

Theorem lt_correct: forall n m, lt_bool n m = true -> n <= m.
Proof.
now induction n; destruct m; auto with arith.
