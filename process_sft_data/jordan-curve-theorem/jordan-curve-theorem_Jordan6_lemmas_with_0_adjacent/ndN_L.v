Require Export Jordan5.
Open Scope nat_scope.
Definition dec (A:Prop):Set:= {A}+{~A}.
Open Scope nat_scope.

Lemma ndN_L: forall(m:fmap)(k:dim)(x y:dart), ndN (L m k x y) = ndN m.
Proof.
simpl in |- *.
tauto.
