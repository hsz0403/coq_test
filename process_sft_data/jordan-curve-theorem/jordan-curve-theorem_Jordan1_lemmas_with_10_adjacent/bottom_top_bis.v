Global Set Asymmetric Patterns.
Require Import Arith.
Require Import EqNat.
Require Export Reals.
Require Export Omega.
Open Scope R_scope.
Inductive dim:Set := zero : dim | one : dim.
Definition dart := nat.
Definition eq_dart_dec := eq_nat_dec.
Definition nil := 0%nat.
Open Scope Z_scope.
Inductive fmap:Set := V : fmap | I : fmap->dart->tag->point->fmap | L : fmap->dim->dart->dart->fmap.
Definition empty(m:fmap): Prop:= match m with V => True | _ => False end.
Definition inj_dart(Df:dart->Prop)(f:dart->dart):Prop:= forall x x':dart, (Df x)->(Df x')->(f x)=(f x')->x=x'.
Definition surj_dart(Df:dart->Prop)(f:dart->dart):Prop := forall y:dart, Df y -> exists x : dart, Df x /\ f x = y.
Definition bij_dart(Df:dart->Prop)(f:dart->dart):Prop:= inj_dart Df f /\ surj_dart Df f.
Fixpoint top (m:fmap)(k:dim)(z:dart){struct m}:dart:= match m with V => nil | I m0 x _ _ => if eq_dart_dec x z then z else top m0 k z | L m0 k0 x y => if eq_dim_dec k0 k then if eq_dart_dec x (top m0 k0 z) then top m0 k0 y else top m0 k0 z else top m0 k z end.
Fixpoint bottom (m:fmap)(k:dim)(z:dart){struct m}:dart:= match m with V => nil | I m0 x _ _ => if eq_dart_dec x z then z else bottom m0 k z | L m0 k0 x y => if (eq_dim_dec k0 k) then if eq_dart_dec y (bottom m0 k0 z) then bottom m0 k0 x else bottom m0 k0 z else bottom m0 k z end.

Lemma A_B_1_ter : forall (m:fmap)(k j:dim)(x y:dart), k<>j -> A (B_1 m k x) j y = A m j y.
Proof.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
tauto.
intros k j x y.
simpl in |- *.
elim (eq_dim_dec d k).
elim (eq_dart_dec d1 x).
elim (eq_dim_dec d j).
elim (eq_dart_dec d0 y).
intros.
rewrite <- a0 in H; rewrite <- a2 in H.
tauto.
tauto.
tauto.
simpl in |- *.
elim (eq_dim_dec d j).
intros.
rewrite <- a0 in H.
tauto.
intros.
rewrite IHm in |- *.
tauto.
tauto.
simpl in |- *.
elim (eq_dim_dec d j).
elim (eq_dart_dec d0 y).
tauto.
intros.
apply IHm.
tauto.
intros.
apply IHm.
Admitted.

Lemma top_nil : forall (m:fmap)(k:dim), inv_hmap m -> top m k nil = nil.
Proof.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
intros.
elim (eq_dart_dec d nil).
tauto.
intro.
apply IHm.
tauto.
simpl in |- *.
unfold prec_L in |- *.
intros.
elim (eq_dim_dec d k).
elim (eq_dart_dec d0 (top m d nil)).
intros.
rewrite IHm in a.
absurd (d0 = nil).
apply exd_not_nil with m.
tauto; tauto.
tauto.
tauto.
tauto.
intros.
rewrite IHm.
tauto.
tauto.
intro.
rewrite IHm.
tauto.
Admitted.

Lemma bottom_nil : forall (m:fmap)(k:dim), inv_hmap m -> bottom m k nil = nil.
Proof.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
intros.
elim (eq_dart_dec d nil).
tauto.
intro.
apply IHm.
tauto.
simpl in |- *.
unfold prec_L in |- *.
intros.
elim (eq_dim_dec d k).
elim (eq_dart_dec d1 (bottom m d nil)).
intros.
rewrite IHm in a.
absurd (d1 = nil).
apply exd_not_nil with m.
tauto; tauto.
tauto.
tauto.
tauto.
intros.
rewrite IHm.
tauto.
tauto.
intro.
rewrite IHm.
tauto.
Admitted.

Lemma not_exd_top : forall (m:fmap)(k:dim)(z:dart), inv_hmap m -> ~exd m z -> top m k z = nil.
Proof.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
intros.
elim (eq_dart_dec d nil).
intro.
elim (eq_dart_dec d z).
tauto.
intro.
apply IHm.
tauto.
tauto.
intro.
elim (eq_dart_dec d z).
tauto.
intro.
apply IHm.
tauto.
tauto.
simpl in |- *.
unfold prec_L in |- *.
intros.
elim (eq_dim_dec d k).
elim (eq_dart_dec d0 (top m d z)).
intros.
rewrite IHm in a.
absurd (d0 = nil).
apply exd_not_nil with m.
tauto.
tauto.
tauto.
tauto.
tauto.
intros.
apply IHm.
tauto.
tauto.
intro.
apply IHm.
tauto.
Admitted.

Lemma not_exd_bottom : forall (m:fmap)(k:dim)(z:dart), inv_hmap m -> ~exd m z -> bottom m k z = nil.
Proof.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
intros.
elim (eq_dart_dec d nil).
intro.
elim (eq_dart_dec d z).
tauto.
intro.
apply IHm.
tauto.
tauto.
intro.
elim (eq_dart_dec d z).
tauto.
intro.
apply IHm.
tauto.
tauto.
simpl in |- *.
unfold prec_L in |- *.
intros.
elim (eq_dim_dec d k).
elim (eq_dart_dec d1 (bottom m d z)).
intros.
rewrite IHm in a.
absurd (d1 = nil).
apply exd_not_nil with m.
tauto.
tauto.
tauto.
tauto.
tauto.
intros.
apply IHm.
tauto.
tauto.
intro.
apply IHm.
tauto.
Admitted.

Lemma exd_top:forall (m:fmap)(k:dim)(z:dart), inv_hmap m -> exd m z -> exd m (top m k z).
Proof.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
unfold prec_I in |- *.
intros.
elim (eq_dart_dec d z).
tauto.
intros.
generalize (IHm k z).
tauto.
simpl in |- *.
unfold prec_L in |- *.
intros.
elim (eq_dim_dec d k).
elim (eq_dart_dec d0 (top m d z)).
intros.
apply IHm.
tauto.
tauto.
intros.
apply IHm.
tauto.
tauto.
intro.
apply IHm.
tauto.
Admitted.

Lemma exd_bottom:forall (m:fmap)(k:dim)(z:dart), inv_hmap m -> exd m z -> exd m (bottom m k z).
Proof.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
unfold prec_I in |- *.
intros.
elim (eq_dart_dec d z).
tauto.
intros.
generalize (IHm k z).
tauto.
simpl in |- *.
unfold prec_L in |- *.
intros.
elim (eq_dim_dec d k).
elim (eq_dart_dec d1 (bottom m d z)).
intros.
apply IHm.
tauto.
tauto.
intros.
apply IHm.
tauto.
tauto.
intro.
apply IHm.
tauto.
Admitted.

Lemma nosucc_top : forall (m:fmap)(k:dim)(z:dart), inv_hmap m -> exd m z -> ~succ m k z -> top m k z = z.
Proof.
induction m.
unfold succ in |- *.
simpl in |- *.
tauto.
unfold succ in |- *.
simpl in |- *.
intros.
elim (eq_dart_dec d z).
tauto.
intro.
unfold succ in IHm.
apply IHm.
tauto.
tauto.
tauto.
unfold succ in |- *.
simpl in |- *.
unfold prec_L in |- *.
intros k z Inv E.
elim (eq_dim_dec d k).
intro.
rewrite a.
elim (eq_dart_dec d0 z).
elim (eq_dart_dec d0 (top m k z)).
intros.
absurd (d1 <> nil).
tauto.
apply exd_not_nil with m.
tauto.
tauto.
intros.
absurd (d1 <> nil).
tauto.
apply exd_not_nil with m.
tauto.
tauto.
elim (eq_dart_dec d0 (top m k z)).
intros.
decompose [and] Inv.
generalize (IHm k z H0 E).
unfold succ in |- *.
intro.
rewrite H5 in a0.
tauto; tauto.
tauto.
intros.
apply IHm.
tauto.
tauto.
unfold succ in |- *.
tauto.
intros.
apply IHm.
tauto.
tauto.
Admitted.

Lemma nopred_bottom : forall (m:fmap)(k:dim)(z:dart), inv_hmap m -> exd m z -> ~pred m k z -> bottom m k z = z.
Proof.
induction m.
unfold pred in |- *.
simpl in |- *.
tauto.
unfold pred in |- *.
simpl in |- *.
intros.
elim (eq_dart_dec d z).
tauto.
intro.
unfold pred in IHm.
apply IHm.
tauto.
tauto.
tauto.
unfold pred in |- *.
simpl in |- *.
unfold prec_L in |- *.
intros k z Inv E.
elim (eq_dim_dec d k).
intro.
rewrite a.
elim (eq_dart_dec d1 z).
elim (eq_dart_dec d1 (bottom m k z)).
intros.
absurd (d0 <> nil).
tauto.
apply exd_not_nil with m.
tauto.
tauto.
intros.
absurd (d0 <> nil).
tauto.
apply exd_not_nil with m.
tauto.
tauto.
elim (eq_dart_dec d1 (bottom m k z)).
intros.
decompose [and] Inv.
generalize (IHm k z H0 E).
unfold pred in |- *.
intro.
rewrite H5 in a0.
tauto; tauto.
tauto.
intros.
apply IHm.
tauto.
tauto.
unfold pred in |- *.
tauto.
intros.
apply IHm.
tauto.
tauto.
Admitted.

Lemma top_bottom_bis:forall(m:fmap)(k:dim)(z:dart), inv_hmap m -> exd m z -> top m k (bottom m k z) = top m k z.
Proof.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
unfold prec_I in |- *.
unfold succ in |- *.
simpl in |- *.
intros.
elim (eq_dart_dec d z).
elim (eq_dart_dec d z).
tauto.
tauto.
elim (eq_dart_dec d (bottom m k z)).
intros.
rewrite a in H.
generalize (exd_bottom m k z).
tauto.
intros.
apply IHm.
tauto.
tauto.
unfold succ in |- *.
simpl in |- *.
unfold prec_L in |- *.
unfold succ in |- *.
simpl in |- *.
intros.
elim (eq_dim_dec d k).
elim (eq_dart_dec d1 (bottom m d z)).
elim (eq_dart_dec d0 (top m d (bottom m d d0))).
intros.
elim (eq_dart_dec d0 (top m d z)).
intro.
tauto.
intro.
rewrite a0.
rewrite IHm.
tauto.
tauto.
tauto.
elim (eq_dart_dec d0 (top m d z)).
intros.
rewrite IHm in b.
rewrite nosucc_top in b.
tauto.
tauto; tauto.
tauto.
unfold succ in |- *.
tauto.
tauto.
tauto.
intros.
rewrite IHm in b0.
rewrite nosucc_top in b0.
tauto.
tauto.
tauto.
unfold succ in |- *.
tauto.
tauto.
tauto.
elim (eq_dart_dec d0 (top m d (bottom m d z))).
intros.
elim (eq_dart_dec d0 (top m d z)).
tauto.
intros.
rewrite IHm in a.
tauto.
tauto.
tauto.
intros.
elim (eq_dart_dec d0 (top m d z)).
intros.
rewrite IHm in b.
tauto.
tauto.
tauto.
intro.
rewrite IHm.
tauto.
tauto.
tauto.
intro.
rewrite IHm.
tauto.
tauto.
Admitted.

Lemma cA_bottom : forall (m:fmap)(k:dim)(z:dart), inv_hmap m -> exd m z -> ~succ m k z -> cA m k z = bottom m k z.
Proof.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
unfold prec_I in |- *.
unfold succ in |- *.
simpl in |- *.
intros.
elim (eq_dart_dec d z).
tauto.
intro.
apply IHm; tauto.
unfold succ in |- *.
simpl in |- *.
unfold prec_L in |- *.
intros k z Inv E.
decompose [and] Inv.
elim (eq_dim_dec d k).
elim (eq_dart_dec d0 z).
intros.
absurd (d1 <> nil).
tauto.
apply exd_not_nil with m.
tauto.
tauto.
elim (eq_dart_dec (cA_1 m k d1) z).
intros.
clear Inv.
elim (eq_dart_dec d1 (bottom m d z)).
intro.
rewrite a0.
apply IHm.
tauto.
tauto.
rewrite a0 in H2.
tauto.
intro.
rewrite <- IHm in b0.
rewrite <- a in b0.
rewrite a0 in b0.
rewrite cA_cA_1 in b0.
tauto.
tauto.
tauto.
tauto.
tauto.
unfold succ in |- *.
rewrite a0.
tauto.
intros.
elim (eq_dart_dec d1 (bottom m d z)).
intro.
clear Inv.
rewrite a in a0.
rewrite <- IHm in a0.
rewrite a.
rewrite a0 in b.
rewrite cA_1_cA in b.
tauto.
tauto.
tauto.
tauto.
tauto.
unfold succ in |- *.
tauto.
intro.
rewrite a.
apply IHm.
tauto.
tauto.
unfold succ in |- *.
tauto.
intros.
apply IHm.
tauto.
tauto.
unfold succ in |- *.
Admitted.

Lemma cA_1_top : forall (m:fmap)(k:dim)(z:dart), inv_hmap m -> exd m z -> ~pred m k z -> cA_1 m k z = top m k z.
Proof.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
unfold prec_I in |- *.
unfold pred in |- *.
simpl in |- *.
intros.
elim (eq_dart_dec d z).
tauto.
intro.
apply IHm; tauto.
unfold pred in |- *.
simpl in |- *.
unfold prec_L in |- *.
intros k z Inv E.
decompose [and] Inv.
elim (eq_dim_dec d k).
elim (eq_dart_dec d1 z).
intros.
absurd (d0 <> nil).
tauto.
apply exd_not_nil with m.
tauto.
tauto.
elim (eq_dart_dec (cA m k d0) z).
intros.
clear Inv.
elim (eq_dart_dec d0 (top m d z)).
intro.
rewrite a0 in |- *.
apply IHm.
tauto.
tauto.
rewrite a0 in H3.
tauto.
intro.
rewrite <- IHm in b0.
rewrite <- a in b0.
rewrite a0 in b0.
rewrite cA_1_cA in b0.
tauto.
tauto.
tauto.
tauto.
tauto.
unfold pred in |- *.
rewrite a0 in |- *.
tauto.
intros.
elim (eq_dart_dec d0 (top m d z)).
intro.
clear Inv.
rewrite a in a0.
rewrite <- IHm in a0.
rewrite a in |- *.
rewrite a0 in b.
rewrite cA_cA_1 in b.
tauto.
tauto.
tauto.
tauto.
tauto.
unfold pred in |- *.
tauto.
intro.
rewrite a in |- *.
apply IHm.
tauto.
tauto.
unfold pred in |- *.
tauto.
intros.
apply IHm.
tauto.
tauto.
unfold pred in |- *.
Admitted.

Lemma cA_eq_aux : forall(m:fmap)(k:dim)(z:dart), inv_hmap m -> exd m z -> cA m k z = if succ_dec m k z then A m k z else bottom m k z.
Proof.
intros.
elim (succ_dec m k z).
intro.
generalize (A_cA m k z (A m k z) H H0).
intros.
apply H1.
apply succ_exd_A.
tauto.
tauto.
tauto.
apply cA_bottom.
tauto.
Admitted.

Lemma cA_eq : forall(m:fmap)(k:dim)(z:dart), inv_hmap m -> cA m k z = if succ_dec m k z then A m k z else bottom m k z.
Proof.
intros.
elim (succ_dec m k z).
intro.
assert (exd m z).
apply succ_exd with k.
tauto.
tauto.
generalize (A_cA m k z (A m k z) H H0).
intros.
apply H1.
apply succ_exd_A.
tauto.
tauto.
tauto.
intro.
elim (exd_dec m z).
intro.
apply cA_bottom.
tauto.
tauto.
tauto.
intro.
rewrite not_exd_bottom.
rewrite not_exd_cA.
tauto.
tauto.
tauto.
tauto.
Admitted.

Lemma cA_1_eq_aux : forall(m:fmap)(k:dim)(z:dart), inv_hmap m -> exd m z -> cA_1 m k z = if pred_dec m k z then A_1 m k z else top m k z.
Proof.
intros.
elim (pred_dec m k z).
intro.
generalize (A_1_cA_1 m k z (A_1 m k z) H H0).
intros.
apply H1.
apply pred_exd_A_1.
tauto.
tauto.
tauto.
apply cA_1_top.
tauto.
Admitted.

Lemma cA_1_eq : forall(m:fmap)(k:dim)(z:dart), inv_hmap m -> cA_1 m k z = if pred_dec m k z then A_1 m k z else top m k z.
Proof.
intros.
elim (pred_dec m k z).
intro.
assert (exd m z).
apply pred_exd with k.
tauto.
tauto.
generalize (A_1_cA_1 m k z (A_1 m k z) H H0).
intros.
apply H1.
apply pred_exd_A_1.
tauto.
tauto.
tauto.
intro.
elim (exd_dec m z).
intro.
apply cA_1_top.
tauto.
tauto.
tauto.
intro.
rewrite not_exd_top.
rewrite not_exd_cA_1.
tauto.
tauto.
tauto.
tauto.
Admitted.

Lemma top_bottom : forall (m:fmap)(k:dim)(z:dart), inv_hmap m -> exd m z -> ~succ m k z -> top m k (bottom m k z) = z.
Proof.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
unfold prec_I in |- *.
unfold succ in |- *.
simpl in |- *.
intros.
elim (eq_dart_dec d z).
elim (eq_dart_dec d z).
tauto.
tauto.
elim (eq_dart_dec d (bottom m k z)).
intros.
rewrite a in H.
generalize (exd_bottom m k z).
tauto.
intros.
apply IHm.
tauto.
tauto.
unfold succ in |- *.
tauto.
simpl in |- *.
unfold prec_L in |- *.
unfold succ in |- *.
simpl in |- *.
intros.
generalize H1.
elim (eq_dim_dec d k).
clear H1.
elim (eq_dart_dec d0 z).
intros.
absurd (d1 <> nil).
tauto.
apply exd_not_nil with m.
tauto.
tauto.
elim (eq_dart_dec d1 (bottom m d z)).
elim (eq_dart_dec d0 (top m d (bottom m d d0))).
intros.
rewrite a0.
apply IHm.
tauto.
tauto.
unfold succ in |- *.
rewrite a1.
tauto.
intros.
rewrite IHm in b.
tauto.
tauto.
tauto.
tauto.
elim (eq_dart_dec d0 (top m d (bottom m d z))).
intros.
rewrite IHm in a.
tauto.
tauto.
tauto.
unfold succ in |- *.
rewrite a0.
tauto.
intros.
apply IHm.
tauto.
tauto.
unfold succ in |- *.
rewrite a.
tauto.
intros.
apply IHm.
tauto.
tauto.
unfold succ.
Admitted.

Lemma bottom_top : forall (m:fmap)(k:dim)(z:dart), inv_hmap m -> exd m z -> ~pred m k z -> bottom m k (top m k z) = z.
Proof.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
unfold prec_I in |- *.
unfold pred in |- *.
simpl in |- *.
intros.
elim (eq_dart_dec d z).
elim (eq_dart_dec d z).
tauto.
tauto.
elim (eq_dart_dec d (top m k z)).
intros.
rewrite a in H.
generalize (exd_top m k z).
tauto.
intros.
apply IHm.
tauto.
tauto.
unfold pred in |- *.
tauto.
simpl in |- *.
unfold prec_L in |- *.
unfold pred in |- *.
simpl in |- *.
intros.
generalize H1.
elim (eq_dim_dec d k).
clear H1.
elim (eq_dart_dec d1 z).
intros.
absurd (d0 <> nil).
tauto.
apply exd_not_nil with m.
tauto.
tauto.
elim (eq_dart_dec d0 (top m d z)).
elim (eq_dart_dec d1 (bottom m d (top m d d1))).
intros.
rewrite a0.
apply IHm.
tauto.
tauto.
unfold pred in |- *.
rewrite a1.
tauto.
intros.
rewrite IHm in b.
tauto.
tauto.
tauto.
tauto.
elim (eq_dart_dec d1 (bottom m d (top m d z))).
intros.
rewrite IHm in a.
tauto.
tauto.
tauto.
unfold pred in |- *.
rewrite a0.
tauto.
intros.
apply IHm.
tauto.
tauto.
unfold pred in |- *.
rewrite a.
tauto.
intros.
apply IHm.
tauto.
tauto.
unfold pred.
Admitted.

Lemma top_A : forall (m:fmap)(k:dim)(z:dart), inv_hmap m -> succ m k z -> top m k (A m k z) = top m k z.
Proof.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
unfold prec_I in |- *.
unfold succ in |- *.
simpl in |- *.
intros.
elim (eq_dart_dec d (A m k z)).
intro.
rewrite a in H.
absurd (exd m (A m k z)).
tauto.
apply succ_exd_A.
tauto.
unfold succ in |- *.
tauto.
elim (eq_dart_dec d z).
intros.
rewrite a in H.
absurd (exd m z).
tauto.
apply succ_exd with k.
tauto.
unfold succ in |- *.
tauto.
intros.
apply IHm.
tauto.
tauto.
unfold succ in |- *.
simpl in |- *.
unfold prec_L in |- *.
intros.
generalize H0.
clear H0.
elim (eq_dim_dec d k).
elim (eq_dart_dec d0 z).
elim (eq_dart_dec d0 (top m d d1)).
elim (eq_dart_dec d0 (top m d z)).
tauto.
intros.
rewrite cA_eq in H.
generalize H.
clear H.
elim (succ_dec m d d0).
tauto.
intros.
rewrite a in H.
rewrite bottom_top in H.
tauto.
tauto.
tauto.
tauto.
tauto.
elim (eq_dart_dec d0 (top m d z)).
tauto.
intros.
rewrite <- a in b.
rewrite nosucc_top in b.
tauto.
tauto.
tauto.
tauto.
elim (eq_dart_dec d0 (top m d (A m k z))).
elim (eq_dart_dec d0 (top m d z)).
tauto.
intros.
rewrite a0 in a.
rewrite IHm in a.
rewrite a0 in b.
tauto.
tauto.
unfold succ in |- *.
tauto.
elim (eq_dart_dec d0 (top m d z)).
intros.
rewrite a0 in b.
rewrite IHm in b.
rewrite a0 in a.
tauto.
tauto.
unfold succ in |- *; tauto.
intros.
rewrite a.
apply IHm.
tauto.
unfold succ in |- *.
tauto.
intros.
apply IHm.
tauto.
unfold succ in |- *.
Admitted.

Lemma bottom_A : forall (m:fmap)(k:dim)(z:dart), inv_hmap m -> succ m k z -> bottom m k (A m k z) = bottom m k z.
Proof.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
unfold prec_I in |- *.
unfold succ in |- *.
simpl in |- *.
intros.
elim (eq_dart_dec d (A m k z)).
intro.
rewrite a in H.
absurd (exd m (A m k z)).
tauto.
apply succ_exd_A.
tauto.
unfold succ in |- *.
tauto.
elim (eq_dart_dec d z).
intros.
rewrite a in H.
absurd (exd m z).
tauto.
apply succ_exd with k.
tauto.
unfold succ in |- *.
tauto.
intros.
apply IHm.
tauto.
tauto.
unfold succ in |- *.
simpl in |- *.
unfold prec_L in |- *.
intros.
generalize H0.
clear H0.
elim (eq_dim_dec d k).
elim (eq_dart_dec d0 z).
elim (eq_dart_dec d1 (bottom m d d1)).
elim (eq_dart_dec d1 (bottom m d z)).
tauto.
intros.
rewrite a0.
tauto.
elim (eq_dart_dec d1 (bottom m d z)).
intros.
rewrite cA_eq in H.
generalize H.
clear H.
elim (succ_dec m d d0).
tauto.
intros.
rewrite a0 in H.
symmetry in a.
tauto.
tauto.
intros.
rewrite nopred_bottom in b0.
tauto.
tauto.
tauto.
tauto.
elim (eq_dart_dec d1 (bottom m d (A m k z))).
elim (eq_dart_dec d1 (bottom m d z)).
tauto.
intros.
rewrite a0 in a.
rewrite a0 in b.
rewrite IHm in a.
tauto.
tauto.
unfold succ in |- *.
tauto.
elim (eq_dart_dec d1 (bottom m d z)).
intros.
rewrite a0 in b.
rewrite a0 in a.
rewrite IHm in b.
tauto.
tauto.
unfold succ in |- *.
tauto.
intros.
rewrite a.
apply IHm.
tauto.
unfold succ in |- *.
tauto.
intros.
apply IHm.
tauto.
unfold succ in |- *.
Admitted.

Lemma bottom_top_bis:forall(m:fmap)(k:dim)(z:dart), inv_hmap m -> exd m z -> bottom m k (top m k z) = bottom m k z.
Proof.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
unfold prec_I in |- *.
unfold pred in |- *.
simpl in |- *.
intros.
elim (eq_dart_dec d z).
elim (eq_dart_dec d z).
tauto.
tauto.
elim (eq_dart_dec d (top m k z)).
intros.
rewrite a in H.
generalize (exd_top m k z).
tauto.
intros.
apply IHm.
tauto.
tauto.
simpl in |- *.
unfold prec_L in |- *.
unfold pred in |- *.
unfold succ in |- *.
simpl in |- *.
intros.
elim (eq_dim_dec d k).
elim (eq_dart_dec d0 (top m d z)).
elim (eq_dart_dec d1 (bottom m d (top m d d1))).
intros.
elim (eq_dart_dec d1 (bottom m d z)).
intro.
tauto.
intro.
rewrite a0 in |- *.
rewrite IHm in |- *.
tauto.
tauto.
tauto.
elim (eq_dart_dec d1 (bottom m d z)).
intros.
rewrite IHm in b.
rewrite nopred_bottom in b.
tauto.
tauto; tauto.
tauto.
unfold pred in |- *.
tauto.
tauto.
tauto.
intros.
rewrite IHm in b0.
rewrite nopred_bottom in b0.
tauto.
tauto.
tauto.
unfold pred in |- *.
tauto.
tauto.
tauto.
elim (eq_dart_dec d1 (bottom m d (top m d z))).
intros.
elim (eq_dart_dec d1 (bottom m d z)).
tauto.
intros.
rewrite IHm in a.
tauto.
tauto.
tauto.
intros.
elim (eq_dart_dec d1 (bottom m d z)).
intros.
rewrite IHm in b.
tauto.
tauto.
tauto.
intro.
rewrite IHm in |- *.
tauto.
tauto.
tauto.
intro.
rewrite IHm in |- *.
tauto.
tauto.
tauto.
