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

Theorem genus_theorem : forall m:fmap, inv_hmap m -> 2 * (nc m) >= (ec m).
Proof.
intros.
rename H into Invm.
unfold ec.
induction m.
simpl in |- *.
omega.
unfold nc in |- *.
fold nc in |- *.
unfold nv in |- *; fold nv in |- *.
unfold ne in |- *; fold ne in |- *.
unfold nf in |- *; fold nf in |- *.
unfold nd in |- *; fold nd in |- *.
unfold inv_hmap in Invm.
fold inv_hmap in Invm.
assert (2 * nc m >= nv m + ne m + nf m - nd m).
tauto.
omega.
unfold inv_hmap in Invm; fold inv_hmap in Invm.
induction d.
unfold nc in |- *; fold nc in |- *.
unfold nv in |- *; fold nv in |- *.
unfold ne in |- *; fold ne in |- *.
unfold nf in |- *; fold nf in |- *.
unfold nd in |- *; fold nd in |- *.
elim (expf_dec m (cA_1 m one d0) d1).
intro.
elim (eqc_dec m d0 d1).
intro.
assert (2 * nc m >= nv m + ne m + nf m - nd m).
tauto.
omega.
intro.
assert (eqc m (cA_1 m one d0) d1).
apply expf_eqc.
tauto.
unfold expf in a.
tauto.
absurd (eqc m d0 d1).
tauto.
apply (eqc_cA_1_eqc m one d0 d1).
tauto.
tauto.
intro.
elim (eqc_dec m d0 d1).
intro.
assert (2 * nc m >= nv m + ne m + nf m - nd m).
tauto.
omega.
intro.
assert (2 * nc m >= nv m + ne m + nf m - nd m).
tauto.
omega.
assert (2 * nc m >= nv m + ne m + nf m - nd m).
tauto.
clear IHm.
unfold nc in |- *.
fold nc in |- *.
unfold nv in |- *; fold nv in |- *.
unfold ne in |- *; fold ne in |- *.
unfold nf in |- *; fold nf in |- *.
unfold nd in |- *; fold nd in |- *.
unfold prec_L in Invm.
elim (eqc_dec m d0 d1).
intro.
elim (expf_dec m d0 (cA m zero d1)).
intro.
omega.
intro.
omega.
elim (expf_dec m d0 (cA m zero d1)).
intros.
assert (eqc m d0 (cA m zero d1)).
apply expf_eqc.
tauto.
unfold expf in a.
tauto.
assert (eqc m d0 d1).
eapply eqc_cA_eqc.
tauto.
apply H0.
tauto.
intro.
intro.
omega.
