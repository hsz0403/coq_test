Require Export Jordan5.
Open Scope nat_scope.
Definition dec (A:Prop):Set:= {A}+{~A}.
Open Scope nat_scope.

Lemma expf_L1_I_CS:forall (m:fmap)(x y z t:dart), inv_hmap (L m one x y) -> exd m z -> let x1 := cA m one x in let x10 := cA m zero x1 in let y0 := cA m zero y in let y_1 := cA_1 m one y in ~ expf m x y0 -> ( expf m z t \/ expf m z x /\ expf m t y0 \/ expf m t x /\ expf m z y0 ) -> expf (L m one x y) z t.
Proof.
intros.
generalize (expf_dec m z x).
intro AA.
generalize (expf_dec m t y0).
intro BB.
generalize (expf_dec m t x).
intro CC.
generalize (expf_dec m z y0).
intro DD.
generalize (or_and_dec (expf m z x) (expf m t y0) (expf m t x) (expf m z y0)).
unfold dec in |- *.
intros.
generalize (H3 AA BB CC DD).
clear H3.
intro.
elim H3.
clear H3.
intro.
elim a.
clear a.
intro.
set (m1 := L m one x y) in |- *.
assert (expf m1 z x).
unfold m1 in |- *.
apply expf_symm.
apply expf_L1_x.
tauto.
fold y0 in |- *.
tauto.
apply expf_symm.
tauto.
assert (expf m1 t y0).
apply expf_symm.
unfold m1 in |- *.
unfold y0 in |- *.
apply expf_L1_y0.
tauto.
fold y0 in |- *.
tauto.
fold y0 in |- *.
apply expf_symm.
tauto.
apply expf_trans with y0.
apply expf_trans with x.
tauto.
unfold y0 in |- *.
unfold m1 in |- *.
apply expf_L1_x_y0.
tauto.
fold y0 in |- *.
tauto.
apply expf_symm.
tauto.
clear a.
intro.
set (m1 := L m one x y) in |- *.
clear H2.
assert (expf m1 t x).
unfold m1 in |- *.
apply expf_symm.
apply expf_L1_x.
tauto.
fold y0 in |- *.
tauto.
apply expf_symm.
tauto.
assert (expf m1 z y0).
apply expf_symm.
unfold m1 in |- *.
unfold y0 in |- *.
apply expf_L1_y0.
tauto.
fold y0 in |- *.
tauto.
fold y0 in |- *.
apply expf_symm.
tauto.
apply expf_trans with y0.
tauto.
apply expf_trans with x.
apply expf_symm.
unfold m1 in |- *.
unfold y0 in |- *.
apply expf_L1_x_y0.
tauto.
fold y0 in |- *.
tauto.
unfold m1 in |- *.
apply expf_L1_x.
tauto.
fold y0 in |- *.
tauto.
apply expf_symm.
tauto.
intros.
clear H3.
assert (expf m z t).
tauto.
clear H2.
set (m1 := L m one x y) in |- *.
assert (expf m1 x y0).
unfold m1 in |- *; unfold y0 in |- *.
apply expf_L1_x_y0.
tauto.
fold y0 in |- *.
tauto.
elim b.
clear b.
intro.
decompose [and] H4.
clear H4.
elim BB.
intro.
assert (expf m y0 z).
apply expf_trans with t.
apply expf_symm.
tauto.
apply expf_symm.
tauto.
assert (expf m1 y0 z).
unfold m1 in |- *.
unfold y0 in |- *.
apply expf_L1_y0.
tauto.
fold y0 in |- *.
tauto.
fold y0 in |- *.
tauto.
assert (expf m1 t y0).
apply expf_symm.
unfold y0 in |- *.
unfold m1 in |- *.
apply expf_L1_y0.
tauto.
fold y0 in |- *.
tauto.
fold y0 in |- *.
apply expf_symm.
tauto.
apply expf_symm.
apply expf_trans with y0.
tauto.
tauto.
intro.
unfold m1 in |- *.
apply expf_symm.
apply expf_impl_expf_L1.
tauto.
fold y0 in |- *.
tauto.
intro.
elim H6.
apply expf_symm.
tauto.
fold y0 in |- *.
intro.
elim b.
apply expf_trans with z.
apply expf_symm.
tauto.
apply expf_symm.
tauto.
apply expf_symm.
tauto.
clear b.
intro.
elim H4.
clear H4.
intro.
decompose [and] H4.
clear H4.
assert (~ expf m y0 t).
intro.
elim H5.
apply expf_symm.
tauto.
assert (~ expf m x t).
intro.
elim H6.
apply expf_symm.
tauto.
unfold m1 in |- *.
generalize (expf_L1_eq m x y t z H H1 H7 H4).
intro.
apply expf_symm.
assert (expf m t z).
apply expf_symm.
tauto.
tauto.
clear H4.
intro.
elim H4.
clear H4.
intro.
elim H4.
clear H4.
intros.
assert (~ expf m x z).
intro.
elim H4.
apply expf_symm.
tauto.
assert (~ expf m y0 z).
intro.
elim H5.
apply expf_symm.
tauto.
unfold m1 in |- *.
generalize (expf_L1_eq m x y z t H H1 H6 H7).
tauto.
clear H4.
intro.
elim H4.
clear H4.
intros.
elim AA.
intro.
assert (expf m t x).
apply expf_trans with z.
apply expf_symm.
tauto.
tauto.
assert (expf m1 z x).
unfold m1 in |- *.
apply expf_symm.
apply expf_L1_x.
tauto.
fold y0 in |- *.
tauto.
apply expf_symm.
tauto.
assert (expf m1 t x).
apply expf_symm.
unfold m1 in |- *.
apply expf_L1_x.
tauto.
fold y0 in |- *.
tauto.
apply expf_symm.
tauto.
apply expf_trans with x.
tauto.
apply expf_symm.
tauto.
intro.
unfold m1 in |- *.
assert (~ expf m x z).
intro.
elim b.
apply expf_symm.
tauto.
assert (~ expf m y0 z).
intro.
elim H5.
apply expf_symm.
tauto.
generalize (expf_L1_eq m x y z t H H1 H6 H7).
tauto.
