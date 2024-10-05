Require Export Jordan8.
Open Scope nat_scope.
Open Scope nat_scope.
Open Scope Z_scope.

Lemma B_L_ter:forall(m:fmap)(k j:dim)(x y z:dart), j <> k -> B (L m k x y) j z = L (B m j z) k x y.
Proof.
intros.
simpl in |- *.
elim (eq_dim_dec k j).
intro.
symmetry in a.
tauto.
tauto.
