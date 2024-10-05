Require Export Jordan3.
Definition expfo(m:fmap)(x:dart)(z t:dart):= expf (L (B m zero x) zero x (A m zero x)) z t.
Definition eqco(m:fmap)(k:dim)(x z t:dart):= eqc (L (B m k x) k x (A m k x)) z t.

Lemma A_1_L_B:forall (m:fmap)(k j:dim)(x z:dart), inv_hmap m -> succ m k x -> let y:= A m k x in A_1 (L (B m k x) k x y) j z = A_1 m j z.
Proof.
induction m.
simpl in |- *.
intros.
unfold succ in H0.
simpl in H0.
tauto.
simpl in |- *.
unfold prec_I in |- *.
unfold succ in |- *.
intros.
elim (eq_dim_dec k j).
elim (eq_dart_dec (A m k x) z).
intro.
rewrite <- a in |- *.
intro.
rewrite <- a0 in |- *.
rewrite A_1_A in |- *.
auto.
tauto.
simpl in H0; unfold succ in |- *.
tauto.
intros.
simpl in H0.
rewrite <- a in |- *.
rewrite A_1_B_bis in |- *.
auto.
auto.
tauto.
intro.
symmetry in H1.
tauto.
simpl in H0.
intro.
rewrite A_1_B_ter in |- *.
tauto.
tauto.
simpl in |- *.
unfold prec_L in |- *.
unfold succ in |- *.
unfold pred in |- *.
intros.
simpl in H0.
generalize H0.
clear H0.
elim (eq_dim_dec k j).
elim (eq_dim_dec d k).
intros a b.
rewrite a in |- *.
rewrite <- b in |- *.
rewrite a in H.
elim (eq_dart_dec d0 x).
elim (eq_dart_dec d1 z).
elim (eq_dim_dec k k).
symmetry in |- *.
tauto.
tauto.
elim (eq_dim_dec k k).
tauto.
tauto.
elim (eq_dart_dec (A m k x) z).
elim (eq_dim_dec k k).
elim (eq_dart_dec d1 z).
intros.
rewrite <- a0 in a2.
rewrite <- a2 in H.
rewrite A_1_A in H.
absurd (x <> nil).
tauto.
apply exd_not_nil with m.
tauto.
apply succ_exd with k.
tauto.
unfold succ in |- *.
tauto.
tauto.
unfold succ in |- *.
tauto.
intros.
rewrite <- a1 in |- *.
rewrite A_1_A in |- *.
tauto.
tauto.
unfold succ in |- *.
tauto.
tauto.
simpl in |- *.
elim (eq_dim_dec k k).
elim (eq_dart_dec d1 z).
tauto.
intros.
rewrite A_1_B_bis in |- *.
tauto.
tauto.
intro.
symmetry in H1.
tauto.
tauto.
elim (eq_dart_dec (A m k x) z).
elim (eq_dim_dec d j).
elim (eq_dart_dec d1 z).
intros.
rewrite <- a2 in a0.
tauto.
intros.
rewrite <- a1 in |- *.
rewrite <- a0 in |- *.
rewrite A_1_A in |- *.
tauto.
tauto.
unfold succ in |- *.
tauto.
intros.
rewrite <- a0 in |- *.
rewrite <- a in |- *.
rewrite A_1_A in |- *.
tauto.
tauto.
unfold succ in |- *.
tauto.
simpl in |- *.
intros.
elim (eq_dim_dec d j).
intro.
rewrite <- a in a0.
tauto.
intro.
rewrite <- a in |- *.
rewrite A_1_B_bis in |- *.
tauto.
tauto.
intro.
symmetry in H1.
tauto.
elim (eq_dim_dec d k).
elim (eq_dart_dec d0 x).
elim (eq_dim_dec d j).
intros.
rewrite a1 in a.
tauto.
tauto.
simpl in |- *.
elim (eq_dim_dec d j).
intros.
rewrite a0 in a.
tauto.
intros.
rewrite A_1_B_ter in |- *.
tauto.
tauto.
simpl in |- *.
elim (eq_dim_dec d j).
elim (eq_dart_dec d1 z).
tauto.
intros.
rewrite A_1_B_ter in |- *.
tauto.
tauto.
intros.
rewrite A_1_B_ter in |- *.
tauto.
tauto.
