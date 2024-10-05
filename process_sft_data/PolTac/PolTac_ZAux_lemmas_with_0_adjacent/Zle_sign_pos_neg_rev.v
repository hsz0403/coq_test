Require Export ZArith.
Open Scope Z_scope.

Theorem Zle_sign_pos_neg_rev: forall x y: Z, (0 < x -> x * y <= 0 -> y <= 0)%Z.
Proof.
intros x y H1 H2; case (Zle_or_lt y 0); auto with zarith.
intros H3; absurd (x * y <= 0)%Z; auto with zarith.
apply Zlt_not_le;apply Zlt_sign_pos_pos; auto.
