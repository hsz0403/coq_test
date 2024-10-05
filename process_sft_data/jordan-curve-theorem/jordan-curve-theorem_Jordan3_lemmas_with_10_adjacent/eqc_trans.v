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

Lemma eqc_exd_exd : forall (m:fmap)(x y:dart), eqc m x y -> (exd m x /\ exd m y).
Proof.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
intros.
elim H.
intro.
decompose [and] H0.
rewrite H1.
rewrite H2.
tauto.
generalize (IHm x y).
tauto.
simpl in |- *.
intros.
generalize (IHm x y).
generalize (IHm x d0).
generalize (IHm x d1).
generalize (IHm d1 y).
generalize (IHm d0 y).
Admitted.

Lemma eqc_dec: forall (m:fmap)(x y:dart), {eqc m x y} + {~eqc m x y}.
Proof.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
intros.
elim (IHm x y).
tauto.
elim (eq_dart_dec x d).
elim (eq_dart_dec y d).
tauto.
tauto.
tauto.
simpl in |- *.
intros x y.
elim (IHm x y).
tauto.
elim (IHm x d0).
elim (IHm d1 y).
tauto.
elim (IHm x d1).
elim (IHm d0 y).
tauto.
tauto.
tauto.
elim (IHm d1 y).
elim (IHm x d1).
elim (IHm d0 y).
tauto.
tauto.
tauto.
elim (IHm x d1).
elim (IHm d0 y).
tauto.
tauto.
elim (IHm d0 y).
tauto.
Admitted.

Lemma eqc_refl: forall(m:fmap)(x:dart), exd m x -> eqc m x x.
Proof.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
intros.
generalize (IHm x).
intro.
assert (d = x -> x = d).
intro.
symmetry in |- *.
tauto.
tauto.
simpl in |- *.
intros.
generalize (IHm x).
Admitted.

Lemma eqc_symm: forall(m:fmap)(x y:dart), eqc m x y -> eqc m y x.
Proof.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
intros.
elim H.
tauto.
intro.
generalize (IHm x y).
tauto.
simpl in |- *.
intros.
elim H.
left.
apply IHm.
tauto.
clear H.
intro.
elim H.
clear H.
intro.
right.
right.
split.
apply IHm.
tauto.
apply IHm.
tauto.
intros.
right.
left.
split.
apply IHm; tauto.
Admitted.

Lemma eqc_cA_r : forall (m:fmap)(k:dim)(x:dart), inv_hmap m -> exd m x -> eqc m x (cA m k x).
Proof.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
intros.
elim (eq_dart_dec d x).
generalize (eqc_refl m x).
intros.
symmetry in a.
tauto.
intro.
generalize (IHm k x).
tauto.
simpl in |- *.
unfold prec_L in |- *.
intros.
decompose [and] H.
clear H.
elim (eq_dim_dec d k).
intro.
elim (eq_dart_dec d0 x).
intro.
rewrite <- a0.
right.
left.
split.
apply eqc_refl.
rewrite a0.
tauto.
apply eqc_refl.
tauto.
intro.
elim (eq_dart_dec (cA_1 m k d1) x).
intro.
assert (d1 = cA m k x).
rewrite <- a0.
rewrite cA_cA_1.
tauto.
tauto.
tauto.
right.
right.
rewrite H.
generalize (IHm k d0 H1 H3).
generalize (IHm k x H1 H0).
tauto.
intro.
generalize (IHm k x).
tauto.
generalize (IHm k x).
Admitted.

Lemma eqc_cA_1_r : forall (m:fmap)(k:dim)(x:dart), inv_hmap m -> exd m x -> eqc m x (cA_1 m k x).
Proof.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
intros.
elim (eq_dart_dec d x).
generalize (eqc_refl m x).
intros.
symmetry in a.
tauto.
intro.
generalize (IHm k x).
tauto.
simpl in |- *.
unfold prec_L in |- *.
intros.
decompose [and] H.
clear H.
elim (eq_dim_dec d k).
intro.
elim (eq_dart_dec d1 x).
intro.
rewrite <- a0.
right.
right.
split.
apply eqc_refl.
tauto.
apply eqc_refl.
tauto.
intro.
elim (eq_dart_dec (cA m k d0) x).
intro.
assert (d0 = cA_1 m k x).
rewrite <- a0.
rewrite cA_1_cA.
tauto.
tauto.
tauto.
right.
left.
rewrite H.
generalize (IHm k x).
generalize (IHm k d1).
tauto.
intro.
generalize (IHm k x).
tauto.
generalize (IHm k x).
Admitted.

Lemma eqc_eqc_cA : forall (m:fmap)(k:dim)(x y:dart), inv_hmap m -> eqc m x y -> eqc m x (cA m k y).
Proof.
intros.
apply eqc_trans with y.
tauto.
apply eqc_cA_r.
tauto.
generalize (eqc_exd_exd m x y).
Admitted.

Lemma eqc_eqc_cA_1 : forall (m:fmap)(k:dim)(x y:dart), inv_hmap m -> eqc m x y -> eqc m x (cA_1 m k y).
Proof.
intros.
apply eqc_trans with y.
tauto.
apply eqc_cA_1_r.
tauto.
generalize (eqc_exd_exd m x y).
Admitted.

Lemma eqc_cA_1_eqc : forall (m:fmap)(k:dim)(x y:dart), inv_hmap m -> eqc m (cA_1 m k x) y -> eqc m x y.
Proof.
intros.
generalize (eqc_cA_1_r m k x).
intros.
apply eqc_trans with (cA_1 m k x).
apply H1.
tauto.
generalize (eqc_exd_exd m (cA_1 m k x) y).
intros.
generalize (exd_cA_1 m k x).
tauto.
Admitted.

Lemma eqc_cA_eqc : forall (m:fmap)(k:dim)(x y:dart), inv_hmap m -> eqc m x (cA m k y) -> eqc m x y.
Proof.
intros.
generalize (eqc_cA_r m k y H).
intros.
apply eqc_trans with (cA m k y).
tauto.
apply eqc_symm.
apply H1.
generalize (eqc_exd_exd m x (cA m k y)).
intros.
generalize (exd_cA m k y).
Admitted.

Lemma eqc_eqc_cF : forall (m:fmap)(x y:dart), inv_hmap m -> eqc m x y -> eqc m x (cF m y).
Proof.
unfold cF in |- *.
intros.
assert (eqc m x (cA_1 m zero y)).
apply eqc_eqc_cA_1.
tauto.
tauto.
eapply eqc_eqc_cA_1.
tauto.
Admitted.

Lemma exd_Iter_cF : forall (m:fmap)(n:nat)(z:dart), inv_hmap m -> exd m z -> exd m (Iter (cF m) n z).
Proof.
intros.
induction n.
simpl in |- *.
tauto.
simpl in |- *.
generalize (exd_cF m (Iter (cF m) n z)).
Admitted.

Lemma eqc_Iter_cF : forall (m:fmap)(n:nat)(z:dart), inv_hmap m -> exd m z -> eqc m z (Iter (cF m) n z).
Proof.
intros.
induction n.
simpl in |- *.
apply eqc_refl.
tauto.
simpl in |- *.
eapply eqc_trans.
apply IHn.
apply eqc_eqc_cF.
tauto.
apply eqc_refl.
apply exd_Iter_cF.
tauto.
Admitted.

Lemma expf_eqc : forall(m:fmap)(x y:dart), inv_hmap m -> MF.expo m x y -> eqc m x y.
Proof.
intros.
assert (exd m x).
unfold MF.expo in H0.
tauto.
assert (MF.f = cF).
tauto.
unfold MF.expo in H0.
rewrite H2 in H0.
intuition.
elim H4.
intros n In.
rewrite <- In.
apply eqc_Iter_cF.
tauto.
Admitted.

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
