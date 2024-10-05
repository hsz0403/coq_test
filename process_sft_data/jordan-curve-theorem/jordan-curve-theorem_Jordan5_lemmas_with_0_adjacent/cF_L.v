Require Export Jordan4.
Definition betweenf:= MF.between.

Lemma cF_L:forall(m:fmap)(k:dim)(x y z:dart), inv_hmap m -> prec_L m k x y -> cF (L m k x y) z = if eq_dim_dec k zero then cA_1 m one (if eq_dart_dec y z then x else if eq_dart_dec (cA m zero x) z then cA_1 m zero y else cA_1 m zero z) else (if eq_dart_dec y (cA_1 m zero z) then x else if eq_dart_dec (cA m one x) (cA_1 m zero z) then cA_1 m one y else cA_1 m one (cA_1 m zero z)).
Proof.
unfold cF in |- *.
intros.
simpl in |- *.
elim (eq_dim_dec k zero).
intro.
elim (eq_dim_dec k one).
intro.
rewrite a0 in a.
inversion a.
tauto.
intro.
elim (eq_dim_dec k one).
tauto.
intro.
induction k.
tauto.
tauto.
