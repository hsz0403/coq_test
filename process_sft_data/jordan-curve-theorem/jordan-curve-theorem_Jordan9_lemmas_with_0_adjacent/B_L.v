Require Export Jordan8.
Open Scope nat_scope.
Open Scope nat_scope.
Open Scope Z_scope.

Lemma B_L:forall(m:fmap)(k j:dim)(x y z:dart), x <> z -> B (L m k x y) j z = L (B m j z) k x y.
Proof.
intros.
simpl in |- *.
elim (eq_dart_dec x z).
tauto.
elim (eq_dim_dec k j).
tauto.
tauto.
