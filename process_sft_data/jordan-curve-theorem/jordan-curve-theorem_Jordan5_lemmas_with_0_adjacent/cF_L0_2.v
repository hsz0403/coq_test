Require Export Jordan4.
Definition betweenf:= MF.between.

Lemma cF_L0_2:forall (m:fmap)(x y z:dart), inv_hmap (L m zero x y) -> let y_0_1 := cF m y in let x0 := cA m zero x in betweenf m y_0_1 z x0 -> cF (L m zero x y) z = if eq_dart_dec x0 z then y_0_1 else cF m z.
Proof.
unfold betweenf in |- *.
unfold MF.between in |- *.
simpl in |- *.
unfold prec_L in |- *.
intros.
decompose [and] H.
clear H.
assert (exd m (cF m y)).
generalize (exd_cF m y).
tauto.
generalize (H0 H1 H).
clear H0.
intro.
elim H0.
intros i Hi.
clear H0.
elim Hi.
intros j Hj.
clear Hi.
decompose [and] Hj.
clear Hj.
assert (MF.f = cF).
tauto.
rewrite H9 in H0.
rewrite H9 in H8.
rewrite cF_L in |- *.
elim (eq_dim_dec zero zero).
intro.
elim (eq_dart_dec y z).
intro.
elim (eq_dart_dec (cA m zero x) z).
rewrite a0 in H7.
tauto.
intro.
set (p := MF.Iter_upb m (cF m y)) in |- *.
fold p in H10.
assert (cF m y = Iter (cF m) p (cF m y)).
rewrite <- H9 in |- *.
unfold p in |- *.
rewrite MF.Iter_upb_period in |- *.
tauto.
tauto.
rewrite H9 in |- *.
tauto.
assert (z = Iter (cF m) (p - 1) (cF m y)).
rewrite <- a0 in |- *.
assert (p = S (p - 1)).
omega.
rewrite H12 in H11.
simpl in H11.
assert (inj_dart (exd m) (cF m)).
apply inj_cF.
tauto.
unfold inj_dart in H13.
apply H13.
tauto.
generalize (MF.exd_Iter_f m (p - 1) (cF m y)).
tauto.
tauto.
assert (j = (j - i + i)%nat).
omega.
generalize H8.
rewrite H13 in |- *.
rewrite <- H9 in |- *.
rewrite MF.Iter_comp in |- *.
rewrite H9 in |- *.
rewrite H0 in |- *.
intro.
assert ((p - 1)%nat = (p - 1 - j + j)%nat).
omega.
generalize H12.
rewrite H15 in |- *.
rewrite <- H9 in |- *.
rewrite MF.Iter_comp in |- *.
rewrite H9 in |- *.
rewrite H8 in |- *.
rewrite <- H14 in |- *.
rewrite <- H9 in |- *.
rewrite <- MF.Iter_comp in |- *.
intro.
assert (p = MF.Iter_upb m z).
rewrite <- H0 in |- *.
unfold p in |- *.
apply MF.period_uniform.
tauto.
tauto.
clear H13.
clear a.
clear H15.
assert ((p - 1 - j + (j - i))%nat = (p - 1 - i)%nat).
omega.
rewrite H13 in H16.
clear H13.
assert (0%nat = (p - 1 - i)%nat).
apply (MF.unicity_mod_p m z 0 (p - 1 - i)).
tauto.
rewrite <- a0 in |- *.
tauto.
rewrite <- H17 in |- *.
omega.
rewrite <- H17 in |- *.
omega.
rewrite <- H16 in |- *.
simpl in |- *.
tauto.
assert (i = j).
omega.
rewrite H15 in H0.
rewrite <- a0 in H0.
rewrite H8 in H0.
tauto.
elim (eq_dart_dec (cA m zero x) z).
unfold cF in |- *.
tauto.
unfold cF in |- *.
tauto.
tauto.
tauto.
unfold prec_L in |- *.
tauto.
