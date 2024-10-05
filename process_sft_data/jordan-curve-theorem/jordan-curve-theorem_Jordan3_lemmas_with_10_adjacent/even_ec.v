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

Lemma inv_hmap_dec:forall(m:fmap), {inv_hmap m} + {~inv_hmap m}.
Proof.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
unfold prec_I in |- *.
generalize (eq_dart_dec d nil).
generalize (exd_dec m d).
tauto.
simpl in |- *.
unfold prec_L in |- *.
generalize (exd_dec m d0).
generalize (exd_dec m d1).
generalize (succ_dec m d d0).
generalize (pred_dec m d d1).
generalize (eq_dart_dec (cA m d d0) d1).
Admitted.

Lemma expf_dec : forall(m:fmap)(x y:dart), {expf m x y} + {~expf m x y}.
Proof.
unfold expf in |- *.
intros.
generalize (MF.expo_dec m x y).
generalize (inv_hmap_dec m).
Admitted.

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
Admitted.

Theorem genus_corollary : forall m:fmap, inv_hmap m -> genus m >= 0.
Proof.
intros.
unfold genus in |- *.
generalize (genus_theorem m H).
generalize (even_ec m).
generalize (ec m).
generalize (nc m).
intros a b.
intros.
cut (a >= b / 2).
intro.
omega.
assert (b = 2 * Z.div2 b).
apply Zeven_div2.
tauto.
rewrite H2 in H1.
assert (a >= Z.div2 b).
omega.
rewrite H2.
rewrite Zmult_comm.
assert (Z.div2 b * 2 / 2 = Z.div2 b).
apply Z_div_mult.
omega.
rewrite H4.
Admitted.

Lemma Euler_Poincare: forall m:fmap, inv_hmap m -> planar m -> ec m / 2 = nc m.
Proof.
unfold planar in |- *.
unfold genus in |- *.
intros.
Admitted.

Lemma planar_dec:forall m:fmap, {planar m} + {~planar m}.
Proof.
unfold planar in |- *.
intro.
Admitted.

Lemma planar_V: planar V.
Proof.
unfold planar in |- *.
unfold genus in |- *.
unfold ec in |- *.
simpl in |- *.
Admitted.

Lemma planar_I: forall (m:fmap)(x:dart)(t:tag)(p:point), inv_hmap m -> planar m -> prec_I m x -> planar (I m x t p).
Proof.
unfold planar in |- *.
unfold genus in |- *.
unfold ec in |- *.
unfold prec_I in |- *.
simpl in |- *.
intros.
assert (nv m + 1 + (ne m + 1) + (nf m + 1) - (nd m + 1) = nv m + ne m + nf m - nd m + 1 * 2).
omega.
rewrite H2.
rewrite Z_div_plus.
omega.
Admitted.

Lemma expf_planar_0: forall (m:fmap)(x y:dart), inv_hmap m -> planar m -> prec_L m zero x y -> expf m (cA_1 m one x) y -> planar (L m zero x y).
Proof.
unfold planar in |- *.
unfold genus in |- *.
unfold ec in |- *.
simpl in |- *.
unfold prec_L in |- *.
intros.
elim (expf_dec m (cA_1 m one x) y).
intro.
elim (eqc_dec m x y).
intro.
assert (nv m + (ne m - 1) + (nf m + 1) - nd m = nv m + ne m + nf m - nd m).
omega.
rewrite H3.
omega.
intro.
elim b.
eapply eqc_cA_1_eqc.
tauto.
apply expf_eqc.
tauto.
unfold expf in a.
decompose [and] a.
apply H4.
Admitted.

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
Admitted.

Lemma not_eqc_planar: forall (m:fmap)(k:dim)(x y:dart), inv_hmap m -> planar m -> prec_L m k x y -> ~eqc m x y -> planar (L m k x y).
Proof.
unfold planar in |- *.
unfold genus in |- *.
unfold ec in |- *.
unfold prec_L in |- *.
intros.
induction k.
simpl in |- *.
elim (eqc_dec m x y).
tauto.
intro.
elim (expf_dec m (cA_1 m one x) y).
intro.
elim b.
eapply eqc_cA_1_eqc.
tauto.
apply expf_eqc.
tauto.
unfold expf in a.
decompose [and] a.
apply H4.
intro.
assert (nv m + (ne m - 1) + (nf m + -1) - nd m = nv m + ne m + nf m - nd m + -1 * 2).
omega.
rewrite H3 in |- *.
clear H3.
rewrite Z_div_plus in |- *.
omega.
omega.
simpl in |- *.
elim (eqc_dec m x y).
tauto.
intro.
elim (expf_dec m x (cA m zero y)).
intro.
elim b.
eapply eqc_cA_eqc.
tauto.
apply expf_eqc.
tauto.
unfold expf in a.
decompose [and] a.
apply H4.
intro.
assert (nv m - 1 + ne m + (nf m + -1) - nd m = nv m + ne m + nf m - nd m + -1 * 2).
omega.
rewrite H3 in |- *.
clear H3.
rewrite Z_div_plus in |- *.
omega.
Admitted.

Theorem plf_planar:forall (m:fmap), inv_hmap m -> plf m -> planar m.
Proof.
induction m.
simpl in |- *.
intros.
apply planar_V.
simpl in |- *.
intros.
apply planar_I.
tauto.
tauto.
tauto.
induction d.
simpl in |- *.
intros.
decompose [and] H0.
elim H2.
intro.
apply not_eqc_planar.
tauto.
tauto.
tauto.
tauto.
intro.
apply expf_planar_0.
tauto.
tauto.
tauto.
tauto.
simpl in |- *.
intros.
decompose [and] H0.
elim H2.
intro.
apply not_eqc_planar.
tauto.
tauto.
tauto.
tauto.
intro.
apply expf_planar_1.
tauto.
tauto.
tauto.
Admitted.

Theorem even_ec : forall m:fmap, inv_hmap m -> Zeven (ec m).
Proof.
unfold ec in |- *.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
cut (nv m + 1 + (ne m + 1) + (nf m + 1) - (nd m + 1) = Z.succ (Z.succ (nv m + ne m + nf m - nd m))).
intros.
rewrite H.
apply Zeven_Sn.
apply Zodd_Sn.
tauto.
omega.
induction d.
simpl in |- *.
unfold prec_L in |- *.
elim (expf_dec m (cA_1 m one d0) d1).
intro.
assert (nv m + ne m + nf m - nd m = nv m + (ne m - 1) + (nf m + 1) - nd m).
omega.
rewrite <- H.
tauto.
intro.
assert (nv m + (ne m - 1) + (nf m + -1) - nd m = Z.pred (Z.pred (nv m + ne m + nf m - nd m))).
unfold Z.pred in |- *.
omega.
rewrite H.
intros.
apply Zeven_pred.
apply Zodd_pred.
tauto.
simpl in |- *.
unfold prec_L in |- *.
elim (eq_dart_dec d1 (cA m one d0)).
intro.
symmetry in a.
tauto.
intros.
elim (expf_dec m d0 (cA m zero d1)).
intro.
assert (nv m - 1 + ne m + (nf m + 1) - nd m = nv m + ne m + nf m - nd m).
omega.
rewrite H0.
tauto.
intro.
assert (nv m - 1 + ne m + (nf m + -1) - nd m = Z.pred (Z.pred (nv m + ne m + nf m - nd m))).
unfold Z.pred in |- *.
omega.
rewrite H0.
apply Zeven_pred.
apply Zodd_pred.
tauto.
