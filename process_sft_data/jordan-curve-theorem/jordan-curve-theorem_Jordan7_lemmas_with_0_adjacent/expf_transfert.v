Require Export Jordan6.

Lemma expf_transfert:forall (m:fmap)(x z t:dart), inv_hmap m -> exd m x -> let x0 := cA m zero x in let x_1:= cA_1 m one x in let xb0:= bottom m zero x in let xh0:= top m zero x in let xh0_1:= cA_1 m one xh0 in ~expf m x0 xb0 -> (expf m xb0 z /\ expf m x0 t \/ expf m xb0 t /\ expf m x0 z \/ expf m z t) -> ((expf m x_1 z \/ expf m xh0_1 z) /\ (expf m x_1 t \/ expf m xh0_1 t) \/ expf m z t /\ ~expf m x_1 z /\ ~expf m xh0_1 z).
Proof.
intros.
assert (expf m xb0 xh0_1).
unfold xb0 in |- *.
unfold xh0_1 in |- *.
unfold xh0 in |- *.
apply expf_xb0_xh0_1.
tauto.
tauto.
assert (expf m x0 x_1).
unfold x0 in |- *.
unfold x_1 in |- *.
apply expf_x0_x_1.
tauto.
tauto.
elim (expf_dec m x_1 z).
intro.
elim (expf_dec m x_1 t).
tauto.
elim (expf_dec m xh0_1 t).
tauto.
intros.
assert (~ expf m xb0 t).
intro.
apply b.
apply expf_trans with xb0.
apply expf_symm.
tauto.
tauto.
assert (~ expf m x0 t).
intro.
apply b0.
apply expf_trans with x0.
apply expf_symm.
tauto.
tauto.
assert (expf m z t).
tauto.
absurd (expf m x_1 t).
tauto.
apply expf_trans with z.
tauto.
tauto.
elim (expf_dec m xh0_1 z).
elim (expf_dec m x_1 t).
tauto.
elim (expf_dec m xh0_1 t).
tauto.
intros.
assert (~ expf m x0 z).
intro.
absurd (expf m x_1 z).
tauto.
apply expf_trans with x0.
apply expf_symm.
tauto.
tauto.
assert (~ expf m xb0 t).
intro.
absurd (expf m xh0_1 t).
tauto.
apply expf_trans with xb0.
apply expf_symm.
tauto.
tauto.
assert (~ expf m x0 t).
intro.
absurd (expf m x_1 t).
tauto.
apply expf_trans with x0.
apply expf_symm.
tauto.
tauto.
assert (expf m z t).
tauto.
absurd (expf m xh0_1 t).
tauto.
apply expf_trans with z.
tauto.
tauto.
intros.
assert (~ expf m xb0 z).
intro.
absurd (expf m xh0_1 z).
tauto.
apply expf_trans with xb0.
apply expf_symm.
tauto.
tauto.
assert (~ expf m x0 z).
intro.
absurd (expf m x_1 z).
tauto.
apply expf_trans with x0.
apply expf_symm.
tauto.
tauto.
assert (expf m z t).
tauto.
tauto.
