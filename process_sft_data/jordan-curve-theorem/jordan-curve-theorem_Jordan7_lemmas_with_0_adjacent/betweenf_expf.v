Require Export Jordan6.

Lemma betweenf_expf:forall(m:fmap)(z v t:dart), inv_hmap m -> exd m z -> betweenf m z v t -> (expf m z v /\ expf m z t).
Proof.
unfold betweenf in |- *.
unfold expf in |- *.
intros.
generalize (MF.between_expo1 m z v t H H0 H1).
intros.
generalize (MF.expo_expo1 m z v).
generalize (MF.expo_expo1 m z t).
tauto.
