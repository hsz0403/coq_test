Require Export Jordan5.
Open Scope nat_scope.
Definition dec (A:Prop):Set:= {A}+{~A}.
Open Scope nat_scope.

Lemma expf_L1_x: forall (m:fmap)(x y z:dart), let y0 := cA m zero y in let m1 := L m one x y in inv_hmap m1 -> ~expf m x y0 -> expf m x z -> expf m1 x z.
Proof.
intros.
unfold expf in |- *.
split.
tauto.
unfold expf in H1.
decompose [and] H1.
clear H1.
generalize (MF.expo_expo1 m x z).
intros.
assert (MF.expo1 m x z).
tauto.
unfold MF.expo1 in H4.
set (dx := MF.Iter_upb m x) in |- *.
fold dx in H4.
assert (exists j : nat, j < dx /\ Iter (MF.f m) j x = z).
tauto.
elim H5.
intros i Hi.
decompose [and] Hi.
assert (MF.f = cF).
tauto.
rewrite H8 in H7.
unfold MF.expo in |- *.
split.
unfold m1 in |- *.
simpl in |- *.
tauto.
split with i.
rewrite H8 in |- *.
unfold m1 in |- *.
rewrite <- H7 in |- *.
apply cF_L1_x_x10.
tauto.
unfold m1 in H.
simpl in H.
tauto.
fold y0 in |- *.
tauto.
fold dx in |- *.
rewrite <- MF.upb_eq_degree in |- *.
fold dx in |- *.
omega.
tauto.
tauto.
