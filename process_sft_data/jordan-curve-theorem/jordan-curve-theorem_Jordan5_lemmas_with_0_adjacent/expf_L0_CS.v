Require Export Jordan4.
Definition betweenf:= MF.between.

Lemma expf_L0_CS:forall (m:fmap)(x y z t:dart), inv_hmap (L m zero x y) -> exd m z -> let x0 := cA m zero x in let x_1 := cA_1 m one x in let y_0:= cA_1 m zero y in let y_0_1 := cA_1 m one y_0 in (if expf_dec m x_1 y then betweenf m x_1 z y /\ betweenf m x_1 t y \/ betweenf m y_0_1 z x0 /\ betweenf m y_0_1 t x0 \/ ~ expf m x_1 z /\ expf m z t else expf m x_1 z /\ expf m y t \/ expf m x_1 t /\ expf m y z \/ expf m z t) -> expf (L m zero x y) z t.
Proof.
intros.
rename H0 into Ez.
rename H1 into H0.
generalize H0; clear H0.
assert (inv_hmap (L m zero x y)).
tauto.
simpl in H0.
unfold prec_L in H0.
decompose [and] H0.
clear H0.
elim (expf_dec m x_1 y).
intros.
generalize (between_expf_L0 m x y z t H).
simpl in |- *.
intros.
unfold y_0_1 in H0.
unfold y_0 in H0.
unfold x_1 in H0.
unfold x0 in H0.
elim H0.
tauto.
intro.
elim H8.
tauto.
clear H0.
clear H6 H8.
intro.
elim H0.
intros.
unfold expf in H8.
elim H8.
intros.
unfold MF.expo in H10.
elim H10.
intros.
elim H12.
intros i Hi.
assert (MF.f = cF).
tauto.
rewrite H13 in Hi.
rewrite <- Hi.
apply expf_expf_L0_1.
tauto.
tauto.
fold x_1 in |- *.
tauto.
tauto.
intros.
assert (expf m z t \/ expf m x_1 z /\ expf m y t \/ expf m x_1 t /\ expf m y z).
tauto.
clear H0.
assert ((expf m x_1 z /\ expf m y t \/ expf m x_1 t /\ expf m y z) \/ ~ (expf m x_1 z /\ expf m y t \/ expf m x_1 t /\ expf m y z)).
generalize (expf_dec m x_1 z).
generalize (expf_dec m y t).
generalize (expf_dec m x_1 t).
generalize (expf_dec m y z).
tauto.
elim H0.
intro.
apply expf_L0_5.
tauto.
tauto.
fold x_1 in |- *.
tauto.
tauto.
intro.
clear H0.
assert ((expf m x_1 z /\ expf m x_1 t \/ expf m y z /\ expf m y t) \/ ~ (expf m x_1 z /\ expf m x_1 t \/ expf m y z /\ expf m y t)).
generalize (expf_dec m x_1 z).
generalize (expf_dec m y t).
generalize (expf_dec m x_1 t).
generalize (expf_dec m y z).
tauto.
elim H0.
clear H0.
intro.
apply expf_L0_5bis.
tauto.
tauto.
fold x_1 in |- *.
tauto.
tauto.
clear H0.
intro.
elim H6.
clear H6.
intro.
assert (~ expf m x_1 z /\ ~ expf m y z).
assert (expf m y z -> expf m y t).
unfold expf in |- *.
intros.
split.
tauto.
apply MF.expo_trans with z.
tauto.
unfold expf in H6.
tauto.
assert (expf m y t -> expf m y z).
unfold expf in |- *.
intros.
split.
tauto.
apply MF.expo_trans with t.
tauto.
unfold expf in H6.
apply MF.expo_symm.
tauto.
tauto.
assert (expf m x_1 z -> expf m x_1 t).
intro.
unfold expf in |- *.
split.
tauto.
apply MF.expo_trans with z.
unfold expf in H11.
tauto.
unfold expf in H6.
tauto.
assert (expf m x_1 t -> expf m x_1 z).
intro.
unfold expf in |- *.
split.
tauto.
apply MF.expo_trans with t.
unfold expf in H12.
tauto.
unfold expf in H6.
apply MF.expo_symm.
tauto.
tauto.
tauto.
apply expf_expf_L0_2_bis.
tauto.
tauto.
fold x_1 in |- *.
tauto.
fold x_1 in |- *.
tauto.
tauto.
tauto.
tauto.
