Require Export ZArith.
Open Scope Z_scope.

Theorem Zle_sign_pos_pos_rev: forall x y: Z, (0 < x -> 0 <= x * y -> 0 <= y)%Z.
Proof.
intros x y H1 H2; case (Zle_or_lt 0 y); auto with zarith.
intros H3; absurd (0 <= x * y)%Z; auto with zarith.
apply Zlt_not_le;apply Zlt_sign_pos_neg; auto.
