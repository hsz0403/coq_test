Require Export ZArith.
Open Scope Z_scope.

Theorem Zplus_neg_compat_l: forall a b c: Z, (b <> c -> a + b <> a + c)%Z.
Proof.
intros a b c H H1; case H.
apply Zplus_reg_l with a; auto.
