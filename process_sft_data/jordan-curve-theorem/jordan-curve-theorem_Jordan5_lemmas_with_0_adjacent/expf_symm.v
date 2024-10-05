Require Export Jordan4.
Definition betweenf:= MF.between.

Lemma expf_symm:forall(m:fmap)(z t:dart), expf m z t -> expf m t z.
Proof.
unfold expf in |- *.
split.
tauto.
apply MF.expo_symm.
tauto.
tauto.
