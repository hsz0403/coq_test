Require Export Jordan5.
Open Scope nat_scope.
Definition dec (A:Prop):Set:= {A}+{~A}.
Open Scope nat_scope.

Lemma expf_impl_expf_L1:forall(m:fmap)(x y z t:dart), let m1:= L m one x y in let y0:= cA m zero y in inv_hmap m1 -> ~expf m x y0 -> ~expf m x z -> ~expf m y0 t -> expf m z t -> expf m1 z t.
Proof.
intros.
assert (~ expf m y0 z).
intro.
elim H2.
apply expf_trans with z.
tauto.
tauto.
generalize (expf_L1_eq m x y z t H H0 H1 H4).
tauto.
