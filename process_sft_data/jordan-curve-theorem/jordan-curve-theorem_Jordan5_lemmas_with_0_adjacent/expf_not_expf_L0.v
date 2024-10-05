Require Export Jordan4.
Definition betweenf:= MF.between.

Theorem expf_not_expf_L0: forall (m:fmap)(x y:dart), inv_hmap (L m zero x y) -> let x_1:= cA_1 m one x in let x0 := cA m zero x in (expf m x_1 y <-> ~expf (L m zero x y) y x0).
Proof.
intros.
generalize (expf_not_expf_L0_CV m x y H).
simpl in |- *.
fold x0 in |- *.
fold x_1 in |- *.
intros.
generalize (not_expf_expf_L0_CN m x y H).
simpl in |- *.
fold x0 in |- *.
fold x_1 in |- *.
intro.
generalize (expf_dec m x_1 y).
tauto.
