Require Export ZArith.
Open Scope Z_scope.

Theorem Zplus_eq_compat_l: forall a b c:Z, (b = c -> a + b = a + c)%Z.
Proof.
intros; apply f_equal2 with (f := Zplus); auto.
