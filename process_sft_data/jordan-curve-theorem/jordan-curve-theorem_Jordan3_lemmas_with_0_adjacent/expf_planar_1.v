Require Export Jordan2.
Fixpoint eqc(m:fmap)(x y:dart){struct m}:Prop:= match m with V => False | I m0 x0 _ _ => x=x0 /\ y=x0 \/ eqc m0 x y | L m0 _ x0 y0 => eqc m0 x y \/ eqc m0 x x0 /\ eqc m0 y0 y \/ eqc m0 x y0 /\ eqc m0 x0 y end.
Definition expf(m:fmap)(x y:dart):Prop:= inv_hmap m /\ MF.expo m x y.
Require Import ZArith.
Open Scope Z_scope.
Fixpoint nd(m:fmap):Z := match m with V => 0 | I m0 x _ _ => nd m0 + 1 | L m0 _ _ _ => nd m0 end.
Fixpoint nv(m:fmap):Z := match m with V => 0 | I m0 x _ _ => nv m0 + 1 | L m0 zero x y => nv m0 | L m0 one x y => nv m0 - 1 end.
Fixpoint ne(m:fmap):Z := match m with V => 0 | I m0 x _ _ => ne m0 + 1 | L m0 zero x y => ne m0 - 1 | L m0 one x y => ne m0 end.
Fixpoint nf(m:fmap):Z := match m with V => 0 | I m0 x _ _ => nf m0 + 1 | L m0 zero x y => let x_1:= cA_1 m0 one x in nf m0 + if expf_dec m0 x_1 y then 1 else -1 | L m0 one x y => let y0 := cA m0 zero y in nf m0 + if expf_dec m0 x y0 then 1 else -1 end.
Fixpoint nc(m:fmap):Z := match m with V => 0 | I m0 x _ _ => nc m0 + 1 | L m0 _ x y => nc m0 - if eqc_dec m0 x y then 0 else 1 end.
Definition ec(m:fmap): Z:= nv m + ne m + nf m - nd m.
Definition genus(m:fmap):= (nc m) - (ec m)/2.
Definition planar(m:fmap):= genus m = 0.
Fixpoint plf(m:fmap):Prop:= match m with V => True | I m0 x _ _ => plf m0 | L m0 zero x y => plf m0 /\ (~eqc m0 x y \/ expf m0 (cA_1 m0 one x) y) | L m0 one x y => plf m0 /\ (~eqc m0 x y \/ expf m0 x (cA m0 zero y)) end.

Lemma expf_planar_1: forall (m:fmap)(x y:dart), inv_hmap m -> planar m -> prec_L m one x y -> expf m x (cA m zero y) -> planar (L m one x y).
Proof.
unfold planar in |- *.
unfold genus in |- *.
unfold ec in |- *.
simpl in |- *.
intros m x y Inv E Pr Exp.
elim (eqc_dec m x y).
intro.
elim (expf_dec m x (cA m zero y)).
intro.
assert (nv m - 1 + ne m + (nf m + 1) - nd m = nv m + ne m + nf m - nd m).
omega.
rewrite H.
omega.
tauto.
intro.
elim b.
eapply eqc_cA_eqc.
tauto.
apply expf_eqc.
tauto.
unfold expf in Exp.
decompose [and] Exp.
apply H0.
