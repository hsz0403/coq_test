Require Export Jordan4.
Definition betweenf:= MF.between.

Lemma cF_L0_1:forall (m:fmap)(x y z:dart), inv_hmap (L m zero x y) -> let x_1 := cA_1 m one x in betweenf m x_1 z y -> cF (L m zero x y) z = if eq_dart_dec y z then x_1 else cF m z.
Proof.
unfold betweenf in |- *.
unfold MF.between in |- *.
simpl in |- *.
unfold prec_L in |- *.
intros.
decompose [and] H.
clear H.
assert (exd m (cA_1 m one x)).
generalize (exd_cA_1 m one x).
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
rewrite cF_L.
elim (eq_dim_dec zero zero).
intro.
elim (eq_dart_dec y z).
tauto.
elim (eq_dart_dec (cA m zero x) z).
intros.
set (p := MF.Iter_upb m (cA_1 m one x)) in |- *.
fold p in H10.
assert (z = Iter (cF m) (p - 1) (cA_1 m one x)).
assert (cF m z = cA_1 m one x).
unfold cF in |- *.
rewrite <- a0.
rewrite cA_1_cA.
tauto.
tauto.
tauto.
assert (z = cF_1 m (cA_1 m one x)).
rewrite <- H11.
rewrite cF_1_cF.
tauto.
tauto.
rewrite <- a0.
generalize (exd_cA m zero x).
tauto.
rewrite H12.
assert (cA_1 m one x = cF m (Iter (cF m) (p - 1) (cA_1 m one x))).
rewrite <- H9.
assert (MF.f m (Iter (MF.f m) (p - 1) (cA_1 m one x)) = Iter (MF.f m) p (cA_1 m one x)).
assert (p = S (p - 1)).
omega.
rewrite H13.
simpl in |- *.
assert ((p - 1 - 0)%nat = (p - 1)%nat).
omega.
rewrite H14.
tauto.
rewrite H13.
unfold p in |- *.
set (x_1 := cA_1 m one x) in |- *.
generalize (MF.Iter_upb_period m x_1).
simpl in |- *.
intros.
rewrite H14.
tauto.
tauto.
unfold x_1 in |- *.
tauto.
rewrite H13.
rewrite cF_1_cF.
rewrite <- H13.
tauto.
tauto.
generalize (MF.exd_Iter_f m (p - 1) (cA_1 m one x)).
tauto.
assert (i = (p - 1)%nat).
eapply (MF.unicity_mod_p m (cA_1 m one x)).
tauto.
tauto.
fold p in |- *.
omega.
fold p in |- *.
omega.
rewrite H9.
rewrite <- H11.
tauto.
assert (i = j).
omega.
rewrite H13 in H0.
rewrite H8 in H0.
tauto.
unfold cF in |- *.
tauto.
tauto.
tauto.
unfold prec_L in |- *.
tauto.
