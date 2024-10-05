Require Export Jordan4.
Definition betweenf:= MF.between.

Lemma nf_L_B_aux :forall(m:fmap)(k:dim)(x:dart), inv_hmap m -> succ m k x -> let y := A m k x in let m0 := B m k x in let m1 := L m0 k x (A m k x) in nf m1 = match k with | zero => let x_1 := cA_1 m0 one x in nf m0 + (if expf_dec m0 x_1 y then 1 else -1) | one => let y0 := cA m0 zero y in nf m0 + (if expf_dec m0 x y0 then 1 else -1) end.
Proof.
simpl in |- *.
tauto.
