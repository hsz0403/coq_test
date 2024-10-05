Require Export Jordan4.
Definition betweenf:= MF.between.

Lemma expf_L0_CN:forall (m:fmap)(x y z t:dart), inv_hmap (L m zero x y) -> exd m z -> expf (L m zero x y) z t -> let x0 := cA m zero x in let x_1 := cA_1 m one x in let y_0:= cA_1 m zero y in let y_0_1 := cA_1 m one y_0 in (if expf_dec m x_1 y then betweenf m x_1 z y /\ betweenf m x_1 t y \/ betweenf m y_0_1 z x0 /\ betweenf m y_0_1 t x0 \/ ~ expf m x_1 z /\ expf m z t else expf m z t \/ expf m z y /\ expf m t x0 \/ expf m t y /\ expf m z x0).
Proof.
intros.
unfold expf in H1.
unfold MF.expo in H1.
decompose [and] H1.
clear H1.
elim H5.
clear H5.
intros i Hi.
assert (MF.f = cF).
tauto.
rewrite H1 in Hi.
rewrite <- Hi.
elim (expf_dec m x_1 y).
unfold y_0_1 in |- *.
unfold y_0 in |- *.
unfold x0 in |- *.
unfold x_1 in |- *.
apply expf_L0_CN_1.
tauto.
tauto.
intro.
unfold x0 in |- *.
apply expf_L0_CN_2.
tauto.
tauto.
tauto.
