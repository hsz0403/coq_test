Require Export Jordan8.
Open Scope nat_scope.
Open Scope nat_scope.
Open Scope Z_scope.

Theorem nf_B0:forall (m:fmap)(x:dart), inv_hmap m -> succ m zero x -> let y := A m zero x in let x0 := bottom m zero x in nf (B m zero x) = nf m + if expf_dec m y x0 then 1 else -1.
Proof.
simpl in |- *.
intros.
assert (nf (L (B m zero x) zero x (A m zero x)) = nf m).
apply nf_L_B0.
tauto.
tauto.
simpl in H1.
generalize H1.
clear H1.
assert (cA m zero x = A m zero x).
rewrite cA_eq.
elim (succ_dec m zero x).
tauto.
tauto.
tauto.
assert (cA_1 (B m zero x) one x = cA_1 m one x).
rewrite cA_1_B_ter.
tauto.
tauto.
intro.
inversion H2.
rewrite H2.
rewrite <- H1.
generalize (expf_not_expf_B0 m x H H0).
simpl in |- *.
intro.
elim (expf_dec (B m zero x) (cA_1 m one x) (cA m zero x)).
elim (expf_dec m (cA m zero x) (bottom m zero x)).
intros.
tauto.
intros.
clear a.
clear H3 b.
omega.
elim (expf_dec m (cA m zero x) (bottom m zero x)).
intros.
clear H3 a b.
omega.
tauto.
