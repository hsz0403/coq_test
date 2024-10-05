Require Export ZArith.
Open Scope Z_scope.

Theorem Zle_sign_pos_neg: forall x y: Z, (0 <= x -> y <= 0 -> x * y <= 0)%Z.
Proof.
intros x y H1 H2; apply Zle_pos_neg; replace (- (x * y))%Z with (x * (- y))%Z; auto with zarith; ring.
