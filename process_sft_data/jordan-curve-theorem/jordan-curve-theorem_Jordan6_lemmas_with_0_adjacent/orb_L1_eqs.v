Require Export Jordan5.
Open Scope nat_scope.
Definition dec (A:Prop):Set:= {A}+{~A}.
Open Scope nat_scope.

Theorem orb_L1_eqs: forall(m:fmap)(x y z:dart), let m1:= L m one x y in let y0:= cA m zero y in inv_hmap m1 -> exd m z -> ~expf m x y0 -> ~expf m x z -> ~expf m y0 z -> eqs (MF.Iter_orb m1 z) (MF.Iter_orb m z).
Proof.
intros.
unfold eqs in |- *.
intro t.
generalize (expf_L1_eq m x y z t H H1 H2 H3).
fold m1 in |- *.
intro.
generalize (MF.expo_eq_exds_orb m z t).
intros.
generalize (MF.expo_eq_exds_orb m1 z t).
intros.
assert (inv_hmap m1).
tauto.
unfold m1 in H7.
simpl in H7.
unfold prec_L in H7.
decompose [and] H7.
clear H7.
assert (exd m z <-> exd m1 z).
unfold m1 in |- *.
simpl in |- *.
tauto.
split.
intro.
assert (exd m1 z).
unfold m1 in |- *.
simpl in |- *.
tauto.
generalize (MF.incls_orbit m1 z H H15).
intros.
assert (fmap_to_set m1 = fmap_to_set m).
unfold m1 in |- *.
simpl in |- *.
tauto.
rewrite H17 in H16.
inversion H16.
generalize (H18 t H13).
intro.
generalize (exd_exds m t).
intro.
clear H18.
assert (exd m t).
tauto.
assert (exd m1 t).
unfold m1 in |- *.
simpl in |- *.
tauto.
unfold expf in H4.
tauto.
intro.
assert (exd m1 z).
unfold m1 in |- *.
simpl in |- *.
tauto.
generalize (MF.incls_orbit m1 z H H15).
intros.
assert (fmap_to_set m1 = fmap_to_set m).
unfold m1 in |- *.
simpl in |- *.
tauto.
generalize (MF.incls_orbit m z H8 H0).
intros.
inversion H18.
generalize (H19 t H13).
intro.
unfold expf in H4.
generalize (exd_exds m t).
intro.
clear H19.
assert (exd m1 t).
unfold m1 in |- *.
simpl in |- *.
tauto.
assert (exd m t).
tauto.
tauto.
