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

Lemma surj_cA : forall (m:fmap)(k:dim), inv_hmap m -> surj_dart (exd m) (cA m k).
Proof.
unfold surj_dart in |- *.
intros.
split with (cA_1 m k y).
split.
generalize (exd_cA_cA_1 m k y).
tauto.
apply cA_cA_1.
tauto.
Admitted.

Lemma surj_cA_1 : forall (m:fmap)(k:dim), inv_hmap m -> surj_dart (exd m) (cA_1 m k).
Proof.
unfold surj_dart in |- *.
intros.
split with (cA m k y).
split.
generalize (exd_cA_cA_1 m k y).
tauto.
apply cA_1_cA.
tauto.
Admitted.

Theorem bij_cA : forall (m:fmap)(k:dim), inv_hmap m -> bij_dart (exd m) (cA m k).
Proof.
unfold bij_dart in |- *.
intros.
split.
apply inj_cA.
tauto.
apply surj_cA.
Admitted.

Theorem bij_cA_1 : forall (m:fmap)(k:dim), inv_hmap m -> bij_dart (exd m) (cA_1 m k).
Proof.
unfold bij_dart in |- *.
intros.
split.
apply inj_cA_1.
tauto.
apply surj_cA_1.
Admitted.

Lemma not_exd_D : forall (m:fmap)(x:dart), inv_hmap m -> ~exd (D m x) x.
Proof.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
intro.
unfold prec_I in |- *.
elim (eq_dart_dec d x).
intros.
rewrite <- a.
tauto.
simpl in |- *.
intros.
generalize (IHm x); tauto.
simpl in |- *.
intros.
apply IHm.
Admitted.

Lemma exd_D : forall (m:fmap)(x z:dart), inv_hmap m -> x <> z -> (exd m z <-> exd (D m x) z).
Proof.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
intros.
unfold prec_I in H.
elim (eq_dart_dec d x).
intro.
rewrite a.
tauto.
simpl in |- *.
generalize (IHm x z).
tauto.
intros.
simpl in |- *.
apply IHm.
simpl in H.
tauto.
Admitted.

Lemma exd_B : forall (m:fmap)(k:dim)(x z:dart), exd m z <-> exd (B m k x) z.
Proof.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
intros.
generalize (IHm k x z).
tauto.
simpl in |- *.
intros k x z.
elim (eq_dim_dec d k).
elim (eq_dart_dec d0 x).
generalize (IHm k x z).
tauto.
simpl in |- *.
generalize (IHm k x z).
tauto.
simpl in |- *.
intro.
Admitted.

Lemma exd_B_1 : forall (m:fmap)(k:dim)(x z:dart), exd m z <-> exd (B_1 m k x) z.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
intros.
generalize (IHm k x z).
tauto.
simpl in |- *.
intros k x z.
elim (eq_dim_dec d k).
elim (eq_dart_dec d1 x).
generalize (IHm k x z).
tauto.
simpl in |- *.
generalize (IHm k x z).
tauto.
simpl in |- *.
intro.
Admitted.

Lemma not_succ_B:forall(m:fmap)(k:dim)(z:dart), inv_hmap m -> ~succ m k z -> B m k z = m.
Proof.
induction m.
simpl in |- *.
tauto.
unfold succ in |- *.
simpl in |- *.
intros.
unfold succ in IHm.
rewrite IHm.
tauto.
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
intros.
elim H0.
apply exd_not_nil with m.
tauto.
tauto.
unfold succ in IHm.
intros.
rewrite IHm.
tauto.
tauto.
tauto.
intros.
rewrite IHm.
tauto.
tauto.
unfold succ in |- *.
Admitted.

Lemma not_pred_B_1:forall(m:fmap)(k:dim)(z:dart), inv_hmap m -> ~pred m k z -> B_1 m k z = m.
Proof.
induction m.
simpl in |- *.
tauto.
unfold pred in |- *.
simpl in |- *.
intros.
unfold pred in IHm.
rewrite IHm.
tauto.
tauto.
tauto.
unfold pred in |- *.
simpl in |- *.
unfold prec_L in |- *.
intros.
generalize H0.
clear H0.
elim (eq_dim_dec d k).
elim (eq_dart_dec d1 z).
intros.
elim H0.
apply exd_not_nil with m.
tauto.
tauto.
unfold pred in IHm.
intros.
rewrite IHm.
tauto.
tauto.
tauto.
intros.
rewrite IHm.
tauto.
tauto.
unfold pred in |- *.
Admitted.

Lemma A_B_bis : forall (m:fmap)(k:dim)(x y:dart), y<>x -> A (B m k x) k y = A m k y.
Proof.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
intros.
apply IHm.
tauto.
intros k x y.
simpl in |- *.
elim (eq_dim_dec d k).
elim (eq_dart_dec d0 x).
elim (eq_dart_dec d0 y).
intros.
rewrite <-a0 in H.
rewrite <-a in H.
tauto.
tauto.
simpl in |- *.
elim (eq_dim_dec d k).
elim (eq_dart_dec d0 y).
tauto.
intros.
apply IHm.
tauto.
tauto.
simpl in |- *.
elim (eq_dim_dec d k).
tauto.
intros.
apply IHm.
Admitted.

Lemma A_B_ter : forall (m:fmap)(k j:dim)(x y:dart), k<>j -> A (B m k x) j y = A m j y.
Proof.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
tauto.
intros k j x y.
simpl in |- *.
elim (eq_dim_dec d k).
elim (eq_dart_dec d0 x).
elim (eq_dim_dec d j).
elim (eq_dart_dec d0 y).
intros.
rewrite <-a0 in H; rewrite <-a2 in H.
tauto.
tauto.
tauto.
simpl in |- *.
elim (eq_dim_dec d j).
intros.
rewrite <-a in H; rewrite <-a0 in H; tauto.
intros; apply IHm; tauto.
simpl in |- *.
elim (eq_dim_dec d j).
elim (eq_dart_dec d0 y).
tauto.
intros; apply IHm; tauto.
Admitted.

Lemma B_not_exd : forall (m:fmap)(k:dim)(x:dart), inv_hmap m -> ~exd m x -> B m k x = m.
Proof.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
intros.
rewrite IHm.
tauto.
tauto.
tauto.
unfold B in |- *.
fold B in |- *.
unfold inv_hmap in |- *.
fold inv_hmap in |- *.
intros.
simpl in H0.
elim (eq_dim_dec d k).
elim (eq_dart_dec d0 x).
intros.
unfold prec_L in H.
rewrite a in H.
tauto.
rewrite IHm.
tauto.
tauto.
tauto.
rewrite IHm.
tauto.
tauto.
Admitted.

Lemma B_nil : forall (m:fmap)(k:dim), inv_hmap m -> B m k nil = m.
Proof.
intros.
apply B_not_exd.
tauto.
apply not_exd_nil.
Admitted.

Lemma B_1_not_exd : forall (m:fmap)(k:dim)(x:dart), inv_hmap m -> ~exd m x -> B_1 m k x = m.
Proof.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
intros.
rewrite IHm.
tauto.
tauto.
tauto.
unfold B_1 in |- *.
fold B_1 in |- *.
unfold inv_hmap in |- *.
fold inv_hmap in |- *.
intros.
simpl in H0.
elim (eq_dim_dec d k).
elim (eq_dart_dec d1 x).
intros.
unfold prec_L in H.
rewrite a in H.
tauto.
rewrite IHm.
tauto.
tauto.
tauto.
rewrite IHm.
tauto.
tauto.
Admitted.

Lemma B_1_nil : forall (m:fmap)(k:dim), inv_hmap m -> B_1 m k nil = m.
Proof.
intros.
apply B_1_not_exd.
tauto.
apply not_exd_nil.
Admitted.

Lemma A_1_B : forall (m:fmap)(k:dim)(x:dart), inv_hmap m -> A_1 (B m k x) k (A m k x) = nil.
Proof.
intros m k x.
elim (eq_dart_dec x nil).
intros.
rewrite a.
rewrite B_nil.
rewrite A_nil.
rewrite A_1_nil.
tauto.
tauto.
tauto.
tauto.
intro.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
intros.
apply IHm.
tauto.
simpl in |- *.
elim (eq_dim_dec d k).
elim (eq_dart_dec d0 x).
intros.
unfold prec_L in H.
unfold pred in H.
elim (eq_dart_dec (A_1 m d d1) nil).
rewrite a0.
tauto.
tauto.
simpl in |- *.
elim (eq_dim_dec d k).
elim (eq_dart_dec d1 (A m k x)).
intros.
unfold prec_L in H.
assert (x = A_1 m k d1).
rewrite a.
symmetry in |- *.
apply A_1_A.
tauto.
unfold succ in |- *.
rewrite <- a.
apply (exd_not_nil m d1).
tauto.
tauto.
unfold pred in H.
rewrite a0 in H.
rewrite <- H0 in H.
tauto.
intros.
apply IHm.
tauto.
tauto.
simpl in |- *.
elim (eq_dim_dec d k).
tauto.
Admitted.

Lemma A_1_B_bis : forall (m:fmap)(k:dim)(x y:dart), inv_hmap m -> y <> A m k x -> A_1 (B m k x) k y = A_1 m k y.
Proof.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
intros.
apply IHm.
tauto.
tauto.
intros k x y.
simpl in |- *.
elim (eq_dim_dec d k).
elim (eq_dart_dec d0 x).
elim (eq_dart_dec d1 y).
intro.
symmetry in a.
tauto.
tauto.
simpl in |- *.
elim (eq_dim_dec d k).
elim (eq_dart_dec d1 y).
tauto.
intros.
apply IHm.
tauto.
tauto.
tauto.
simpl in |- *.
elim (eq_dim_dec d k).
tauto.
intros.
apply IHm.
tauto.
Admitted.

Lemma A_1_B_ter : forall (m:fmap)(k j:dim)(x y:dart), k<>j -> A_1 (B m k x) j y = A_1 m j y.
Proof.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
tauto.
intros k j x y.
simpl in |- *.
elim (eq_dim_dec d k).
elim (eq_dart_dec d0 x).
elim (eq_dim_dec d j).
elim (eq_dart_dec d1 y).
intros.
rewrite <- a0 in H; rewrite <- a2 in H.
tauto.
tauto.
tauto.
simpl in |- *.
elim (eq_dim_dec d j).
intros.
rewrite IHm.
tauto.
tauto.
intros.
apply IHm.
tauto.
simpl in |- *.
elim (eq_dim_dec d j).
elim (eq_dart_dec d1 y).
tauto.
intros.
apply IHm.
tauto.
intros.
apply IHm.
Admitted.

Lemma A_1_B_1 : forall (m:fmap)(k:dim)(x:dart), inv_hmap m -> A_1 (B_1 m k x) k x = nil.
Proof.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
intros.
apply IHm.
tauto.
simpl in |- *.
intros k x.
elim (eq_dim_dec d k).
elim (eq_dart_dec d1 x).
intros.
unfold prec_L in H.
rewrite <-a.
rewrite <-a0.
unfold pred in H.
elim (eq_nat_dec (A_1 m d d1) nil).
tauto.
intro.
tauto.
simpl in |- *.
elim (eq_dim_dec d k).
elim (eq_dart_dec d1 x).
tauto.
intros.
apply IHm.
tauto.
tauto.
simpl in |- *.
elim (eq_dim_dec d k).
tauto.
intros.
apply IHm.
Admitted.

Lemma A_B : forall (m:fmap)(k:dim)(x:dart), inv_hmap m -> A (B m k x) k x = nil.
Proof.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
intros.
apply IHm.
tauto.
simpl in |- *.
intros k x.
elim (eq_dim_dec d k).
elim (eq_dart_dec d0 x).
intros.
unfold prec_L in H.
rewrite <-a.
rewrite <-a0.
unfold succ in H.
elim (eq_nat_dec (A m d d0) nil).
tauto.
intro.
tauto.
simpl in |- *.
elim (eq_dim_dec d k).
elim (eq_dart_dec d0 x).
tauto.
intros.
apply IHm.
tauto.
tauto.
simpl in |- *.
elim (eq_dim_dec d k).
tauto.
intros.
apply IHm.
tauto.
