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

Theorem plf_Euler_Poincare: forall m:fmap, inv_hmap m -> plf m -> ec m / 2 = nc m.
Proof.
intros.
apply Euler_Poincare.
tauto.
apply plf_planar.
tauto.
Admitted.

Lemma expf_planar_rcp_0: forall (m:fmap)(x y:dart), inv_hmap m -> prec_L m zero x y -> planar (L m zero x y) -> expf m (cA_1 m one x) y -> planar m.
Proof.
unfold planar.
unfold genus in |- *.
unfold ec in |- *.
unfold prec_L in |- *.
simpl in |- *.
intros m x y Pr Inv.
elim (expf_dec m (cA_1 m one x) y).
intro.
elim (eqc_dec m x y).
intros.
assert (nv m + (ne m - 1) + (nf m + 1) - nd m = nv m + ne m + nf m - nd m).
omega.
rewrite <- H1.
omega.
intro.
elim b.
eapply eqc_cA_1_eqc.
tauto.
apply expf_eqc.
tauto.
unfold expf in a.
decompose [and] a.
apply H0.
Admitted.

Lemma expf_planar_rcp_1: forall (m:fmap)(x y:dart), inv_hmap m -> prec_L m one x y -> planar (L m one x y) -> expf m x (cA m zero y) -> planar m.
Proof.
unfold planar in |- *.
unfold genus in |- *.
unfold ec in |- *.
unfold prec_L in |- *.
simpl in |- *.
intros m x y Pr Inv.
elim (expf_dec m x (cA m zero y)).
elim (eqc_dec m x y).
intros.
assert (nv m - 1 + ne m + (nf m + 1) - nd m = nv m + ne m + nf m - nd m).
omega.
rewrite <- H1.
omega.
intros.
elim b.
eapply eqc_cA_eqc.
tauto.
apply expf_eqc.
tauto.
unfold expf in a.
decompose [and] a.
apply H2.
Admitted.

Theorem weak_planarity_criterion_0: forall (m:fmap)(x y:dart), inv_hmap m -> prec_L m zero x y -> expf m (cA_1 m one x) y -> (planar m <-> planar (L m zero x y)).
Proof.
intros m x y Inv Pr Exp.
split.
intro.
eapply expf_planar_0.
tauto.
tauto.
tauto.
tauto.
intro.
eapply expf_planar_rcp_0.
tauto.
apply Pr.
tauto.
Admitted.

Theorem weak_planarity_criterion_1: forall (m:fmap)(x y:dart), inv_hmap m -> prec_L m one x y -> expf m x (cA m zero y) -> (planar m <-> planar (L m one x y)).
Proof.
intros m x y Inv Pr Exp.
split.
intro.
eapply expf_planar_1.
tauto.
tauto.
tauto.
tauto.
intro.
eapply expf_planar_rcp_1.
tauto.
apply Pr.
tauto.
Admitted.

Lemma planarity_criterion_RCP_0: forall (m:fmap)(x y:dart), inv_hmap m -> prec_L m zero x y -> planar m -> planar (L m zero x y) -> (~ eqc m x y \/ expf m (cA_1 m one x) y).
Proof.
unfold planar in |- *.
unfold genus in |- *.
unfold ec in |- *.
simpl in |- *.
intros m x y Inv Pr E.
unfold prec_L in Pr.
elim (expf_dec m (cA_1 m one x) y).
tauto.
elim (eqc_dec m x y).
intros.
assert (nv m + (ne m - 1) + (nf m + -1) - nd m = nv m + ne m + nf m - nd m - 2).
omega.
rewrite H0 in H.
generalize E H.
generalize (nv m + ne m + nf m - nd m).
intros.
assert (z + -1 * 2 = z - 2).
omega.
rewrite <- H2 in H1.
rewrite Z_div_plus in H1.
absurd (nc m - z / 2 = 0).
omega.
tauto.
omega.
Admitted.

Lemma planarity_criterion_RCP_1: forall (m:fmap)(x y:dart), inv_hmap m -> prec_L m one x y -> planar m -> planar (L m one x y) -> (~ eqc m x y \/ expf m x (cA m zero y)).
Proof.
unfold planar in |- *.
unfold genus in |- *.
unfold ec in |- *.
simpl in |- *.
intros m x y Inv Pr E.
unfold prec_L in Pr.
elim (expf_dec m x (cA m zero y)).
tauto.
elim (eqc_dec m x y).
intros.
assert (nv m - 1 + ne m + (nf m + -1) - nd m = nv m + ne m + nf m - nd m - 2).
omega.
rewrite H0 in H.
generalize E H.
generalize (nv m + ne m + nf m - nd m).
intros.
assert ((z + -1 * 2) / 2 = z / 2 + -1).
apply Z_div_plus.
auto with zarith.
assert (z + -1 * 2 = z - 2).
omega.
rewrite H3 in H2.
assert (z / 2 = (z - 2) / 2).
omega.
rewrite <- H4 in H2.
absurd (z / 2 = z / 2 + -1).
omega.
tauto.
Admitted.

Lemma not_eqc_planar_0:forall (m:fmap)(x y:dart), inv_hmap m -> prec_L m zero x y -> planar m -> ~eqc m x y -> planar (L m zero x y).
Proof.
unfold planar in |- *.
unfold genus in |- *.
unfold ec in |- *.
simpl in |- *.
intros m x y Inv Pr E.
unfold prec_L in Pr.
elim (eqc_dec m x y).
tauto.
elim (expf_dec m (cA_1 m one x) y).
intros.
elim H.
eapply eqc_cA_1_eqc.
tauto.
apply expf_eqc.
tauto.
unfold expf in a.
decompose [and] a.
apply H1.
intros.
assert (nv m + (ne m - 1) + (nf m + -1) - nd m = nv m + ne m + nf m - nd m + -1 * 2).
omega.
rewrite H0.
rewrite Z_div_plus.
generalize E.
generalize (nv m + ne m + nf m - nd m).
intros.
omega.
Admitted.

Lemma not_eqc_planar_1:forall (m:fmap)(x y:dart), inv_hmap m -> prec_L m one x y -> planar m -> ~eqc m x y -> planar (L m one x y).
Proof.
unfold planar in |- *.
unfold genus in |- *.
unfold ec in |- *.
simpl in |- *.
intros m x y Inv Pr E.
unfold prec_L in Pr.
elim (eqc_dec m x y).
tauto.
elim (expf_dec m x (cA m zero y)).
intros.
elim H.
eapply eqc_cA_eqc.
tauto.
apply expf_eqc.
tauto.
unfold expf in a.
decompose [and] a.
apply H1.
intros.
assert (nv m - 1 + ne m + (nf m + -1) - nd m = nv m + ne m + nf m - nd m + -1 * 2).
omega.
rewrite H0.
rewrite Z_div_plus.
generalize E.
generalize (nv m + ne m + nf m - nd m).
intros.
omega.
Admitted.

Theorem planarity_criterion_1: forall (m:fmap)(x y:dart), inv_hmap m -> prec_L m one x y -> planar m -> (planar (L m one x y) <-> (~ eqc m x y \/ expf m x (cA m zero y))).
Proof.
intros.
split.
intro.
simpl in |- *.
apply planarity_criterion_RCP_1.
tauto.
tauto.
tauto.
tauto.
simpl in |- *.
intro.
elim H2.
apply not_eqc_planar_1.
tauto.
tauto.
tauto.
apply expf_planar_1.
tauto.
tauto.
Admitted.

Lemma incr_genus_0:forall(m:fmap)(x y:dart), inv_hmap m -> prec_L m zero x y -> genus m <= genus (L m zero x y).
Proof.
unfold planar in |- *.
unfold genus in |- *.
unfold ec in |- *.
simpl in |- *.
unfold prec_L in |- *.
intros m x y Inv Pr.
elim (expf_dec m (cA_1 m one x) y).
elim (eqc_dec m x y).
intros.
assert (nv m + (ne m - 1) + (nf m + 1) - nd m = nv m + ne m + nf m - nd m).
omega.
rewrite H.
omega.
intros.
elim b.
eapply eqc_cA_1_eqc.
tauto.
apply expf_eqc.
tauto.
unfold expf in a.
decompose [and] a.
apply H0.
elim (eqc_dec m x y).
intros.
assert (nv m + (ne m - 1) + (nf m + -1) - nd m = nv m + ne m + nf m - nd m + -1 * 2).
omega.
rewrite H.
rewrite Z_div_plus.
generalize (nv m + ne m + nf m - nd m).
intros.
omega.
omega.
intros.
assert (nv m + (ne m - 1) + (nf m + -1) - nd m = nv m + ne m + nf m - nd m + -1 * 2).
omega.
rewrite H.
rewrite Z_div_plus.
generalize (nv m + ne m + nf m - nd m).
intros.
omega.
Admitted.

Lemma incr_genus_1:forall(m:fmap)(x y:dart), inv_hmap m -> prec_L m one x y -> genus m <= genus (L m one x y).
Proof.
unfold genus in |- *.
unfold ec in |- *.
simpl in |- *.
unfold prec_L in |- *.
intros m x y Inv Pr.
elim (expf_dec m x (cA m zero y)).
elim (eqc_dec m x y).
intros.
assert (nv m - 1 + ne m + (nf m + 1) - nd m = nv m + ne m + nf m - nd m).
omega.
rewrite H.
omega.
intros.
elim b.
eapply eqc_cA_eqc.
tauto.
apply expf_eqc.
tauto.
unfold expf in a.
decompose [and] a.
apply H0.
intros.
elim (eqc_dec m x y).
intros.
assert (nv m - 1 + ne m + (nf m + -1) - nd m = nv m + ne m + nf m - nd m + -1 * 2).
omega.
rewrite H.
rewrite Z_div_plus.
omega.
omega.
intro.
assert (nv m - 1 + ne m + (nf m + -1) - nd m = nv m + ne m + nf m - nd m + -1 * 2).
omega.
rewrite H.
rewrite Z_div_plus.
omega.
Admitted.

Theorem incr_genus:forall(m:fmap)(k:dim)(x y:dart), inv_hmap m -> prec_L m k x y -> genus m <= genus (L m k x y).
Proof.
induction k.
apply incr_genus_0.
Admitted.

Theorem inversion_planarity:forall(m:fmap)(k:dim)(x y:dart), inv_hmap m -> prec_L m k x y -> planar (L m k x y) -> planar m.
Proof.
unfold planar in |- *.
intros.
assert (genus m <= genus (L m k x y)).
apply incr_genus.
tauto.
tauto.
generalize (genus_corollary m H).
Admitted.

Theorem planarity_crit_0: forall (m:fmap)(x y:dart), inv_hmap m -> prec_L m zero x y -> (planar (L m zero x y) <-> (planar m /\ (~ eqc m x y \/ expf m (cA_1 m one x) y))).
Proof.
intros.
split.
intro.
assert (planar m).
eapply inversion_planarity.
tauto.
apply H0.
tauto.
split.
tauto.
generalize (planarity_criterion_0 m x y H H0 H2).
tauto.
generalize (planarity_criterion_0 m x y H H0).
Admitted.

Theorem planarity_crit_1: forall (m:fmap)(x y:dart), inv_hmap m -> prec_L m one x y -> (planar (L m one x y) <-> (planar m /\ (~ eqc m x y \/ expf m x (cA m zero y)))).
Proof.
intros.
split.
intro.
assert (planar m).
eapply inversion_planarity.
tauto.
apply H0.
tauto.
split.
tauto.
generalize (planarity_criterion_1 m x y H H0 H2).
tauto.
generalize (planarity_criterion_1 m x y H H0).
Admitted.

Lemma eq_genus_I : forall(m:fmap)(x:dart)(t:tag)(p:point), inv_hmap (I m x t p) -> genus (I m x t p) = genus m.
Proof.
unfold genus in |- *.
unfold ec in |- *.
simpl in |- *.
intros.
assert (nv m + 1 + (ne m + 1) + (nf m + 1) - (nd m + 1) = nv m + ne m + nf m - nd m + 1 * 2).
omega.
rewrite H0 in |- *.
rewrite Z_div_plus in |- *.
omega.
Admitted.

Theorem planar_plf: forall m:fmap, inv_hmap m -> genus m = 0 -> plf m.
Proof.
intros.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
simpl in H.
apply IHm.
tauto.
rewrite eq_genus_I in H0.
tauto.
simpl in |- *.
tauto.
induction d.
simpl in |- *.
simpl in H.
generalize (planarity_crit_0 m d0 d1).
tauto.
simpl in |- *.
simpl in H.
generalize (planarity_crit_1 m d0 d1).
Admitted.

Theorem Euler_Poincare_plf: forall m:fmap, inv_hmap m -> ec m / 2 = nc m -> plf m.
Proof.
intros.
apply planar_plf.
tauto.
unfold genus in |- *.
Admitted.

Theorem planarity_criterion_0: forall (m:fmap)(x y:dart), inv_hmap m -> prec_L m zero x y -> planar m -> (planar (L m zero x y) <-> (~ eqc m x y \/ expf m (cA_1 m one x) y)).
Proof.
intros.
split.
intro.
simpl in |- *.
apply planarity_criterion_RCP_0.
tauto.
tauto.
tauto.
tauto.
simpl in |- *.
intro.
elim H2.
apply not_eqc_planar_0.
tauto.
tauto.
tauto.
apply expf_planar_0.
tauto.
tauto.
tauto.
