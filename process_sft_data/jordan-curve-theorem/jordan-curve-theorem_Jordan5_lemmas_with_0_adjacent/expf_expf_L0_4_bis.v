Require Export Jordan4.
Definition betweenf:= MF.between.

Lemma expf_expf_L0_4_bis:forall(m:fmap)(x y z:dart), inv_hmap (L m zero x y) -> let x_1 := cA_1 m one x in ~ expf m x_1 y -> expf m y z -> expf (L m zero x y) y z.
Proof.
intros.
set (y_0 := cA_1 m zero y) in |- *.
set (y_0_1 := cA_1 m one y_0) in |- *.
apply expf_trans with y_0_1.
apply expf_symm.
unfold y_0_1 in |- *.
unfold y_0 in |- *.
apply expf_expf_L0_4_bis_prel.
tauto.
fold x_1 in |- *.
tauto.
fold (cF m y) in |- *.
apply expf_symm.
unfold expf in |- *.
split.
simpl in H.
tauto.
unfold MF.expo in |- *.
split.
simpl in H.
unfold prec_L in H.
tauto.
split with 1%nat.
simpl in |- *.
tauto.
unfold y_0_1 in |- *.
unfold y_0 in |- *.
apply expf_expf_L0_4_bis_prel.
tauto.
fold x_1 in |- *; tauto.
fold (cF m y) in |- *.
apply expf_trans with y.
apply expf_symm.
unfold expf in |- *.
split.
simpl in H.
tauto.
unfold MF.expo in |- *.
split.
simpl in H.
unfold prec_L in H.
tauto.
split with 1%nat.
simpl in |- *.
tauto.
tauto.
