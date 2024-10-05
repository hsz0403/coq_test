Require Export Jordan8.
Open Scope nat_scope.
Open Scope nat_scope.
Open Scope Z_scope.

Lemma other_faces_in_cut_B0:forall (m:fmap)(x z t:dart), inv_hmap m -> succ m zero x -> let y := A m zero x in let x0 := bottom m zero x in ~expf m y x0 -> ~expf m y z -> ~expf m x0 z -> (expf m z t <-> expf (B m zero x) z t).
Proof.
simpl in |- *.
intros.
generalize (expf_B0_CNS m x z t H H0).
simpl in |- *.
assert (cA m zero x = A m zero x).
rewrite cA_eq.
elim (succ_dec m zero x).
tauto.
tauto.
tauto.
elim (expf_dec m (cA m zero x) (bottom m zero x)).
rewrite H4.
tauto.
intro.
rewrite H4.
rewrite H4 in b.
tauto.
