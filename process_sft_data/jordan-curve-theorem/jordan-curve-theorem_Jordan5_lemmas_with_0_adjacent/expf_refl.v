Require Export Jordan4.
Definition betweenf:= MF.between.

Lemma expf_refl: forall(m:fmap)(z:dart), inv_hmap m -> exd m z -> expf m z z.
Proof.
unfold expf in |- *.
split.
tauto.
apply MF.expo_refl.
tauto.
