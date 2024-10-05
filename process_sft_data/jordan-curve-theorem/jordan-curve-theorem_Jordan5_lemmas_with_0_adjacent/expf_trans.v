Require Export Jordan4.
Definition betweenf:= MF.between.

Lemma expf_trans:forall (m : fmap) (z t u : dart), expf m z t -> expf m t u -> expf m z u.
Proof.
unfold expf in |- *.
split.
tauto.
apply MF.expo_trans with t.
tauto.
tauto.
