Require Export Jordan4.
Definition betweenf:= MF.between.

Lemma ne_B:forall (m:fmap)(k:dim)(x:dart), inv_hmap m -> succ m k x -> ne (B m k x) = ne m + if (eq_dim_dec k zero) then 1 else 0.
Proof.
intros.
induction m.
unfold succ in H0.
simpl in H0.
tauto.
unfold succ in H0.
simpl in H0.
simpl in |- *.
simpl in H.
assert (ne (B m k x) = ne m + (if eq_dim_dec k zero then 1 else 0)).
apply IHm.
tauto.
unfold succ in |- *.
tauto.
omega.
simpl in H.
unfold succ in H0.
simpl in H0.
generalize H0.
clear H0.
induction k.
simpl in |- *.
elim (eq_dim_dec d zero).
elim (eq_dart_dec d0 x).
intros.
induction d.
omega.
inversion a0.
simpl in |- *.
intros.
induction d.
unfold succ in IHm.
assert (ne (B m zero x) = ne m + (if eq_dim_dec zero zero then 1 else 0)).
apply IHm.
tauto.
tauto.
generalize H1.
clear H1.
elim (eq_dim_dec zero zero).
intros.
omega.
tauto.
inversion a.
simpl in |- *.
induction d.
tauto.
intros.
assert (ne (B m zero x) = ne m + (if eq_dim_dec zero zero then 1 else 0)).
apply IHm.
tauto.
unfold succ in |- *.
tauto.
generalize H1.
clear H1.
elim (eq_dim_dec zero zero).
tauto.
tauto.
simpl in |- *.
elim (eq_dim_dec d one).
elim (eq_dart_dec d0 x).
elim d.
intros.
inversion a0.
intros.
omega.
simpl in |- *.
intros.
elim d.
assert (ne (B m one x) = ne m + (if eq_dim_dec one zero then 1 else 0)).
apply IHm.
tauto.
unfold succ in |- *.
tauto.
generalize H1.
elim (eq_dim_dec one zero).
intro.
inversion a0.
intros.
omega.
assert (ne (B m one x) = ne m + (if eq_dim_dec one zero then 1 else 0)).
apply IHm.
tauto.
unfold succ in |- *.
tauto.
generalize H1.
elim (eq_dim_dec one zero).
intro.
inversion a0.
tauto.
simpl in |- *.
intros.
elim d.
assert (ne (B m one x) = ne m + (if eq_dim_dec one zero then 1 else 0)).
apply IHm.
tauto.
unfold succ in |- *.
tauto.
generalize H1.
elim (eq_dim_dec one zero).
intro.
inversion a.
intros.
omega.
assert (ne (B m one x) = ne m + (if eq_dim_dec one zero then 1 else 0)).
apply IHm.
tauto.
unfold succ in |- *.
tauto.
generalize H1.
elim (eq_dim_dec one zero).
intro.
inversion a.
intros.
omega.
