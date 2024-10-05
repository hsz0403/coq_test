Require Export ZArith.
Open Scope Z_scope.

Theorem Zplus_neg_reg_l: forall a b c: Z, (a + b <> a + c -> b <> c)%Z.
Proof.
intros a b c H H1; case H; subst; auto.
