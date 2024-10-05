Require Export Jordan4.
Definition betweenf:= MF.between.

Theorem expf_L0_CNS:forall (m:fmap)(x y z t:dart), inv_hmap (L m zero x y) -> exd m z -> (expf (L m zero x y) z t <-> let x0 := cA m zero x in let x_1 := cA_1 m one x in let y_0:= cA_1 m zero y in let y_0_1 := cA_1 m one y_0 in (if expf_dec m x_1 y then betweenf m x_1 z y /\ betweenf m x_1 t y \/ betweenf m y_0_1 z x0 /\ betweenf m y_0_1 t x0 \/ ~ expf m x_1 z /\ expf m z t else expf m z t \/ expf m z y /\ expf m t x0 \/ expf m t y /\ expf m z x0)).
Proof.
intros.
split.
intro.
apply expf_L0_CN.
tauto.
tauto.
tauto.
intro.
apply expf_L0_CS.
tauto.
tauto.
simpl in H1.
generalize H1.
elim (expf_dec m (cA_1 m one x) y).
tauto.
clear H1.
intros.
elim H1.
tauto.
clear H1.
intro.
elim H1.
clear H1.
intro.
right.
left.
split.
unfold expf in |- *.
split.
simpl in H.
tauto.
apply MF.expo_symm.
simpl in H.
tauto.
unfold expf in H1.
decompose [and] H1.
clear H1.
set (x0 := cA m zero x) in |- *.
assert (x = cA_1 m zero x0).
unfold x0 in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
simpl in H.
unfold prec_L in H.
tauto.
rewrite H1 in |- *.
fold x0 in H6.
fold (cF m x0) in |- *.
assert (cF = MF.f).
tauto.
rewrite H3 in |- *.
unfold MF.expo in |- *.
unfold MF.expo in H6.
decompose [and] H6.
split.
tauto.
elim H8.
intros i Hi.
split with (S i).
simpl in |- *.
rewrite Hi in |- *.
tauto.
unfold expf in |- *.
unfold expf in H1.
split.
tauto.
apply MF.expo_symm.
tauto.
tauto.
clear H1.
left.
generalize H1.
unfold expf in |- *.
intros.
decompose [and] H2.
simpl in H.
unfold prec_L in H.
clear H2.
split.
split.
tauto.
apply MF.expo_symm.
tauto.
generalize H7.
clear H7.
unfold MF.expo in |- *.
intros.
split.
tauto.
decompose [and] H7.
elim H4.
intros i Hi.
split with (S i).
simpl in |- *.
set (x0 := cA m zero x) in |- *.
fold x0 in Hi.
assert (x = cA_1 m zero x0).
unfold x0 in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
tauto.
rewrite Hi in |- *.
rewrite H8 in |- *.
fold (cF m x0) in |- *.
assert (cF = MF.f).
tauto.
rewrite H9 in |- *.
tauto.
split.
tauto.
apply MF.expo_symm.
tauto.
tauto.
