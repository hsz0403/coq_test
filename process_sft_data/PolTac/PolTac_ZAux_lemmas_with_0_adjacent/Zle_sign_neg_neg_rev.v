Require Export ZArith.
Open Scope Z_scope.

Theorem Zle_sign_neg_neg_rev: forall x y: Z, (x < 0 -> 0 <= x * y -> y <= 0)%Z.
Proof.
intros x y H1 H2; case (Zle_or_lt y 0); auto with zarith.
intros H3; absurd (0 <= x * y)%Z; auto with zarith.
apply Zlt_not_le;apply Zlt_sign_neg_pos; auto.
