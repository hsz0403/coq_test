Require Export ZArith.
Open Scope Z_scope.

Theorem Zlt_sign_pos_pos: forall x y: Z, (0 < x -> 0 < y -> 0 < x * y)%Z.
Proof.
intros; apply Zmult_lt_O_compat; auto with zarith.
