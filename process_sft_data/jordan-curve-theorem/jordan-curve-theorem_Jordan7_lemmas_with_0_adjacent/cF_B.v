Require Export Jordan6.

Lemma cF_B:forall(m:fmap)(k:dim)(x z:dart), inv_hmap m -> succ m k x -> cF (B m k x) z = if eq_dim_dec k zero then cA_1 (B m zero x) one (if eq_dart_dec (A m zero x) z then top m zero x else if eq_dart_dec (bottom m zero x) z then x else cA_1 m zero z) else (if eq_dart_dec (A m one x) (cA_1 (B m one x) zero z) then top m one x else if eq_dart_dec (bottom m one x) (cA_1 (B m one x) zero z) then x else cA_1 m one (cA_1 (B m one x) zero z)).
Proof.
intros.
unfold cF in |- *.
elim (eq_dim_dec k zero).
intro.
rewrite a.
rewrite cA_1_B.
tauto.
tauto.
rewrite a in H0.
tauto.
intro.
induction k.
tauto.
rewrite cA_1_B.
tauto.
tauto.
tauto.
