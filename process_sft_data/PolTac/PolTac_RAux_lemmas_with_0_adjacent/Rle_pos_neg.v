Require Export Reals.
Open Scope R_scope.

Theorem Rle_pos_neg x : 0 <= -x -> x <= 0.
Proof.
intros; rewrite <- (Ropp_involutive 0), <- (Ropp_involutive x).
now apply Ropp_le_contravar; rewrite Ropp_0.
