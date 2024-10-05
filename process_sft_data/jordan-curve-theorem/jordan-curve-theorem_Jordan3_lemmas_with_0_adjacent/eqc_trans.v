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

Lemma eqc_trans: forall(m:fmap)(x y z:dart), eqc m x y -> eqc m y z -> eqc m x z.
Proof.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
intros.
elim H.
elim H0.
tauto.
intro.
intros.
elim H2.
intros.
rewrite H3.
rewrite H4 in H1.
tauto.
intros.
elim H0.
intro.
elim H2.
intros.
rewrite H4.
rewrite H3 in H1.
tauto.
right.
eapply IHm.
apply H1.
tauto.
simpl in |- *.
intros.
elim H.
clear H.
elim H0.
clear H0.
left.
eapply IHm.
apply H0.
tauto.
clear H0.
intros.
elim H.
clear H.
intro.
right.
left.
split.
apply (IHm x y d0).
tauto.
tauto.
tauto.
intro.
right.
right.
split.
apply (IHm x y d1).
tauto.
tauto.
tauto.
clear H.
intro.
elim H.
clear H.
intro.
elim H0.
clear H0.
intro.
right.
left.
split.
tauto.
apply (IHm d1 y z).
tauto.
tauto.
intros.
elim H1.
intros.
clear H1.
right.
left.
tauto.
intro.
clear H1.
left.
apply (IHm x d0 z).
tauto.
tauto.
intro.
clear H.
elim H0.
clear H0.
intro.
right.
right.
split.
tauto.
apply (IHm d0 y z).
tauto.
tauto.
clear H0.
intro.
elim H.
clear H.
intro.
left.
apply (IHm x d1 z).
tauto.
tauto.
intro.
clear H.
right.
right.
tauto.
