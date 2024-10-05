Require Export Reals.
Open Scope R_scope.

Theorem Rge_neg_pos x : 0 >= -x -> x >= 0.
Proof.
intros; rewrite <- (Ropp_involutive 0), <- (Ropp_involutive x).
now apply Rle_ge; apply Ropp_le_contravar; rewrite Ropp_0; auto with real.
