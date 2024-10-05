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

Lemma exd_A_exd : forall (m : fmap) (k : dim) (z : dart), inv_hmap m -> exd m (A m k z) -> exd m z.
Proof.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
unfold prec_I in |- *.
unfold exd in |- *.
fold exd in |- *.
intros.
elim H0.
clear H0.
intro.
rewrite H0 in H.
decompose [and] H.
elim H4.
apply succ_exd_A.
tauto.
unfold succ in |- *.
tauto.
intro.
right.
eapply IHm.
tauto.
apply H1.
simpl in |- *.
unfold prec_L in |- *.
unfold succ in |- *; unfold pred in |- *.
intros k z Invm.
elim (eq_dim_dec d k).
elim (eq_dart_dec d0 z).
intros.
rewrite <-a.
tauto.
intros.
eapply IHm.
tauto.
apply H.
intros.
eapply IHm.
tauto.
Admitted.

Lemma exd_A_1_exd : forall (m : fmap) (k : dim) (z : dart), inv_hmap m -> exd m (A_1 m k z) -> exd m z.
Proof.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
unfold prec_I in |- *.
unfold exd in |- *.
fold exd in |- *.
intros.
elim H0.
clear H0.
intro.
rewrite H0 in H.
decompose [and] H.
elim H4.
apply pred_exd_A_1.
tauto.
unfold pred in |- *.
tauto.
intro.
right.
eapply IHm.
tauto.
apply H1.
simpl in |- *.
unfold prec_L in |- *.
unfold succ in |- *; unfold pred in |- *.
intros k z Invm.
elim (eq_dim_dec d k).
elim (eq_dart_dec d1 z).
intros.
rewrite <- a in |- *.
tauto.
intros.
eapply IHm.
tauto.
apply H.
intros.
eapply IHm.
tauto.
Admitted.

Lemma A_1_A : forall (m:fmap)(k:dim)(z:dart), inv_hmap m -> succ m k z -> A_1 m k (A m k z) = z.
Proof.
induction m.
simpl in |- *.
simpl in |- *.
unfold succ in |- *.
unfold prec_I in |- *.
simpl in |- *.
tauto.
unfold succ in |- *.
simpl in |- *.
intros.
apply IHm.
tauto.
unfold succ in |- *.
tauto.
unfold succ in |- *.
simpl in |- *.
unfold prec_L in |- *.
intros k z Inv.
elim (eq_dim_dec d k).
elim (eq_dart_dec d0 z).
elim (eq_dart_dec d1 d1).
tauto.
tauto.
elim (eq_dart_dec d1 (A m k z)).
intros.
assert (z = A_1 m k d1).
rewrite a.
symmetry in |- *.
apply IHm.
tauto.
unfold succ in |- *.
tauto.
unfold pred in Inv.
rewrite a0 in Inv.
rewrite <- H0 in Inv.
assert (exd m z).
eapply succ_exd.
tauto.
unfold succ in |- *.
apply H.
assert (z <> nil).
apply exd_not_nil with m.
tauto.
tauto.
tauto.
intros.
apply IHm.
tauto.
unfold succ in |- *.
tauto.
intros.
apply IHm.
tauto.
unfold succ in |- *.
Admitted.

Lemma A_A_1 : forall (m:fmap)(k:dim)(z:dart), inv_hmap m -> pred m k z -> A m k (A_1 m k z) = z.
Proof.
induction m.
simpl in |- *.
simpl in |- *.
unfold pred in |- *.
unfold prec_I in |- *.
simpl in |- *.
tauto.
unfold pred in |- *.
simpl in |- *.
intros.
apply IHm.
tauto.
unfold pred in |- *.
tauto.
unfold pred in |- *.
simpl in |- *.
unfold prec_L in |- *.
intros k z Inv.
elim (eq_dim_dec d k).
elim (eq_dart_dec d1 z).
elim (eq_dart_dec d0 d0).
tauto.
tauto.
elim (eq_dart_dec d0 (A_1 m k z)).
intros.
assert (z = A m k d0).
rewrite a.
symmetry in |- *.
apply IHm.
tauto.
unfold pred in |- *.
tauto.
unfold succ in Inv.
rewrite a0 in Inv.
rewrite <- H0 in Inv.
assert (exd m z).
eapply pred_exd.
tauto.
unfold pred in |- *.
apply H.
assert (z <> nil).
apply exd_not_nil with m.
tauto.
tauto.
tauto.
intros.
apply IHm.
tauto.
unfold pred in |- *.
tauto.
intros.
apply IHm.
tauto.
unfold pred in |- *.
Admitted.

Lemma inj_A: forall (m:fmap)(k:dim), inv_hmap m -> inj_dart (succ m k) (A m k).
Proof.
intros m k Hinv.
unfold inj_dart in |- *.
intros x x' Hx Hx' Heg.
assert (x = A_1 m k (A m k x)).
rewrite A_1_A.
tauto.
tauto.
tauto.
assert (x' = A_1 m k (A m k x')).
rewrite A_1_A.
tauto.
tauto.
tauto.
rewrite Heg in H.
rewrite H.
rewrite <- Heg.
rewrite H0.
rewrite Heg.
Admitted.

Lemma inj_A_1 : forall (m:fmap)(k:dim), inv_hmap m -> inj_dart (pred m k) (A_1 m k).
Proof.
intros m k Hinv.
unfold inj_dart in |- *.
intros x x' Hx Hx' Heg.
assert (x = A m k (A_1 m k x)).
rewrite A_A_1.
tauto.
tauto.
tauto.
assert (x' = A m k (A_1 m k x')).
rewrite A_A_1.
tauto.
tauto.
tauto.
rewrite Heg in H.
rewrite H.
rewrite <- Heg.
rewrite H0.
rewrite Heg.
Admitted.

Lemma succ_pred_clos : forall (m:fmap)(k:dim)(z:dart), inv_hmap m -> exd m z -> (cA m k z <> nil /\ cA_1 m k z <> nil).
Proof.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
intros.
elim (eq_dart_dec d z).
intro.
unfold prec_I in H.
rewrite a in H.
tauto.
intro.
apply IHm.
tauto.
tauto.
simpl in |- *.
unfold prec_L in |- *.
intros.
elim (eq_dim_dec d k).
elim (eq_dart_dec d0 z).
elim (eq_dart_dec d1 z).
intros.
split.
intro.
rewrite H1 in H.
absurd (exd m nil).
apply not_exd_nil.
tauto.
tauto.
intro.
rewrite H1 in H.
absurd (exd m nil).
apply not_exd_nil.
tauto.
tauto.
intros.
split.
intro.
rewrite H1 in H.
absurd (exd m nil).
apply not_exd_nil.
tauto.
tauto.
rewrite a.
elim (eq_dart_dec (cA m k z) z).
intros.
generalize (IHm k d1).
tauto.
intro.
generalize (IHm k z).
tauto.
elim (eq_dart_dec (cA_1 m k d1) z).
intros.
split.
generalize (IHm k d0).
tauto.
elim (eq_dart_dec d1 z).
intros.
intro.
rewrite H1 in H.
absurd (exd m nil).
apply not_exd_nil.
tauto.
tauto.
elim (eq_dart_dec (cA m k d0) z).
intros.
generalize (IHm k d1).
tauto.
intros.
generalize (IHm k z).
tauto.
intros.
split.
generalize (IHm k z).
tauto.
elim (eq_dart_dec d1 z).
intros.
intro.
rewrite H1 in H.
absurd (exd m nil).
apply not_exd_nil.
tauto.
tauto.
elim (eq_dart_dec (cA m k d0) z).
intros.
generalize (IHm k d1).
tauto.
intros.
generalize (IHm k z).
tauto.
intros.
generalize (IHm k z).
Admitted.

Lemma exd_cA_cA_1 : forall (m:fmap)(k:dim)(z:dart), inv_hmap m -> exd m z -> exd m (cA m k z) /\ exd m (cA_1 m k z).
Proof.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
intro.
unfold prec_I in |- *.
intros.
elim (eq_dart_dec d z).
tauto.
generalize (IHm k z).
tauto.
intros k z.
simpl in |- *.
unfold prec_L in |- *.
intros.
elim (eq_dim_dec d k).
intro.
elim (eq_dart_dec d0 z).
intro.
split.
tauto.
elim (eq_dart_dec d1 z).
tauto.
elim (eq_dart_dec (cA m k d0) z).
intros.
generalize (IHm k d1).
tauto.
generalize (IHm k z).
tauto.
intro.
elim (eq_dart_dec (cA_1 m k d1) z).
split.
generalize (IHm k d0).
tauto.
elim (eq_dart_dec d1 z).
tauto.
elim (eq_dart_dec (cA m k d0) z).
generalize (IHm k d1).
tauto.
generalize (IHm k z).
tauto.
split.
generalize (IHm k z); tauto.
elim (eq_dart_dec d1 z).
tauto.
elim (eq_dart_dec (cA m k d0) z).
generalize (IHm k d1); tauto.
generalize (IHm k z); tauto.
Admitted.

Lemma cA_exd : forall (m:fmap)(k:dim)(z:dart), inv_hmap m -> cA m k z <> nil -> exd m z.
Proof.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
unfold prec_I in |- *.
intros k z.
elim (eq_dart_dec d z).
tauto.
intros.
right.
apply (IHm k z).
tauto.
tauto.
intros k z.
simpl in |- *.
unfold prec_L in |- *.
elim (eq_dim_dec d k).
elim (eq_dart_dec d0 z).
intros.
rewrite <- a.
tauto.
elim (eq_dart_dec (cA_1 m k d1) z).
intros.
rewrite <- a.
generalize (exd_cA_cA_1 m k d1).
tauto.
intros.
eapply IHm.
tauto.
apply H0.
intros.
eapply IHm.
tauto.
Admitted.

Lemma cA_1_exd : forall (m:fmap)(k:dim)(z:dart), inv_hmap m -> cA_1 m k z <> nil -> exd m z.
Proof.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
unfold prec_I in |- *.
intros k z.
elim (eq_dart_dec d z).
tauto.
intros.
right.
apply (IHm k z).
tauto.
tauto.
intros k z.
simpl in |- *.
unfold prec_L in |- *.
elim (eq_dim_dec d k).
elim (eq_dart_dec d1 z).
intros.
rewrite <- a.
tauto.
elim (eq_dart_dec (cA m k d0) z).
intros.
rewrite <- a.
generalize (exd_cA_cA_1 m k d0).
tauto.
intros.
eapply IHm.
tauto.
apply H0.
intros.
eapply IHm.
tauto.
Admitted.

Lemma not_exd_cA_1 : forall (m:fmap)(k:dim)(z:dart), inv_hmap m -> ~exd m z -> cA_1 m k z = nil.
Proof.
intros.
elim (eq_dart_dec (cA_1 m k z) nil).
tauto.
intro.
elim H0.
apply cA_1_exd with k.
tauto.
Admitted.

Lemma exd_cA_exd : forall (m:fmap)(k:dim)(z:dart), inv_hmap m -> exd m (cA m k z) -> exd m z.
Proof.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
unfold prec_I in |- *.
intros k z.
elim (eq_dart_dec d z).
tauto.
intros.
right.
elim H0.
clear H0.
intro.
rewrite H0 in H.
apply (cA_exd m k z).
tauto.
tauto.
apply IHm.
tauto.
intros k z.
simpl in |- *.
unfold prec_L in |- *.
elim (eq_dim_dec d k).
elim (eq_dart_dec d0 z).
intros.
rewrite <- a.
tauto.
elim (eq_dart_dec (cA_1 m k d1) z).
intros.
rewrite <- a.
generalize (exd_cA_cA_1 m k d1).
tauto.
intros.
eapply IHm.
tauto.
apply H0.
intros.
eapply IHm.
tauto.
Admitted.

Lemma exd_cA_1_exd : forall (m:fmap)(k:dim)(z:dart), inv_hmap m -> exd m (cA_1 m k z) -> exd m z.
Proof.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
unfold prec_I in |- *.
intros k z.
elim (eq_dart_dec d z).
tauto.
intros.
right.
elim H0.
clear H0.
intro.
rewrite H0 in H.
apply (cA_1_exd m k z).
tauto.
tauto.
apply IHm.
tauto.
intros k z.
simpl in |- *.
unfold prec_L in |- *.
elim (eq_dim_dec d k).
elim (eq_dart_dec d1 z).
intros.
rewrite <- a.
tauto.
elim (eq_dart_dec (cA m k d0) z).
intros.
rewrite <- a.
generalize (exd_cA_cA_1 m k d0).
tauto.
intros.
eapply IHm.
tauto.
apply H0.
intros.
eapply IHm.
tauto.
Admitted.

Lemma exd_cA:forall (m:fmap)(k:dim)(z:dart), inv_hmap m -> (exd m z <-> exd m (cA m k z)).
Proof.
intros.
generalize (exd_cA_exd m k z).
generalize (exd_cA_cA_1 m k z).
Admitted.

Lemma exd_cA_1:forall (m:fmap)(k:dim)(z:dart), inv_hmap m -> (exd m z <-> exd m (cA_1 m k z)).
Proof.
intros.
generalize (exd_cA_1_exd m k z).
generalize (exd_cA_cA_1 m k z).
Admitted.

Lemma cA_1_cA : forall (m:fmap)(k:dim)(z:dart), inv_hmap m -> exd m z -> cA_1 m k (cA m k z) = z.
Proof.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
intros k z.
unfold prec_I in |- *.
elim (eq_dart_dec d z).
elim (eq_dart_dec d z).
tauto.
tauto.
elim (eq_dart_dec d (cA m k z)).
intros.
rewrite a in H.
absurd (exd m (cA m k z)).
tauto.
generalize (exd_cA_cA_1 m k z).
tauto.
intros.
apply IHm.
tauto.
tauto.
intros k z.
simpl in |- *.
unfold prec_L in |- *.
intros.
elim (eq_dim_dec d k).
intros.
elim (eq_dart_dec d0 z).
intro.
rewrite a0.
elim (eq_dart_dec d1 d1).
tauto.
tauto.
elim (eq_dart_dec (cA_1 m k d1) z).
elim (eq_dart_dec d1 (cA m k d0)).
intros.
rewrite a0 in a1.
generalize (IHm k d0).
intros.
rewrite a1 in H1.
symmetry in |- *.
tauto.
elim (eq_dart_dec (cA m k d0) (cA m k d0)).
intros.
tauto.
tauto.
elim (eq_dart_dec d1 (cA m k z)).
intros.
rewrite a0 in b.
elim b.
apply IHm.
tauto.
tauto.
elim (eq_dart_dec (cA m k d0) (cA m k z)).
intros.
generalize (IHm k z).
intros.
rewrite <- a0 in H1.
generalize (IHm k d0).
intro.
rewrite H2 in H1.
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

Lemma cA_cA_1 : forall (m:fmap)(k:dim)(z:dart), inv_hmap m -> exd m z -> cA m k (cA_1 m k z) = z.
Proof.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
intros k z.
unfold prec_I in |- *.
elim (eq_dart_dec d z).
elim (eq_dart_dec d z).
tauto.
tauto.
elim (eq_dart_dec d (cA_1 m k z)).
intros.
rewrite a in H.
absurd (exd m (cA_1 m k z)).
tauto.
generalize (exd_cA_cA_1 m k z).
tauto.
intros.
apply IHm.
tauto.
tauto.
intros k z.
simpl in |- *.
unfold prec_L in |- *.
intros.
elim (eq_dim_dec d k).
intros.
elim (eq_dart_dec d1 z).
intro.
rewrite a0 in |- *.
elim (eq_dart_dec d0 d0).
tauto.
tauto.
elim (eq_dart_dec (cA m k d0) z).
elim (eq_dart_dec d0 (cA_1 m k d1)).
intros.
rewrite a0 in a1.
generalize (IHm k d1).
intros.
rewrite a1 in H1.
symmetry in |- *.
tauto.
elim (eq_dart_dec (cA_1 m k d1) (cA_1 m k d1)).
intros.
tauto.
tauto.
elim (eq_dart_dec d0 (cA_1 m k z)).
intros.
rewrite a0 in b.
elim b.
apply IHm.
tauto.
tauto.
elim (eq_dart_dec (cA_1 m k d1) (cA_1 m k z)).
intros.
generalize (IHm k z).
intros.
rewrite <- a0 in H1.
generalize (IHm k d1).
intro.
rewrite H2 in H1.
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

Lemma inj_cA: forall (m:fmap)(k:dim), inv_hmap m -> inj_dart (exd m) (cA m k).
Proof.
intros m k Hinv.
unfold inj_dart in |- *.
intros x x' Hx Hx' Heg.
assert (x = cA_1 m k (cA m k x)).
symmetry in |- *.
apply cA_1_cA.
tauto.
tauto.
rewrite Heg in H.
rewrite H.
apply cA_1_cA.
tauto.
Admitted.

Lemma inj_cA_1: forall (m:fmap)(k:dim), inv_hmap m -> inj_dart (exd m) (cA_1 m k).
Proof.
intros m k Hinv.
unfold inj_dart in |- *.
intros x x' Hx Hx' Heg.
assert (x = cA m k (cA_1 m k x)).
symmetry in |- *.
apply cA_cA_1.
tauto.
tauto.
rewrite Heg in H.
rewrite H.
apply cA_cA_1.
tauto.
Admitted.

Lemma fixpt_cA_cA_1 : forall (m:fmap)(k:dim)(z:dart), inv_hmap m -> exd m z -> ~succ m k z -> ~pred m k z -> cA m k z = z /\ cA_1 m k z = z.
Proof.
induction m.
simpl in |- *.
tauto.
unfold succ in |- *; unfold pred in |- *.
simpl in |- *.
intros k z.
elim (eq_dart_dec d z).
tauto.
intros.
apply IHm.
tauto.
tauto.
unfold succ in |- *; tauto.
unfold pred in |- *; tauto.
intros k z.
unfold succ in |- *; unfold pred in |- *.
simpl in |- *.
unfold prec_L in |- *.
elim (eq_dim_dec d k).
elim (eq_dart_dec d0 z).
elim (eq_dart_dec d1 z).
intros.
rewrite a0; rewrite a.
tauto.
intros.
absurd (d1 <> nil).
tauto.
intro.
rewrite H3 in H.
absurd (exd m nil).
apply not_exd_nil.
tauto.
tauto.
elim (eq_dart_dec d1 z).
intros.
absurd (d0 <> nil).
tauto.
intro.
rewrite H3 in H.
absurd (exd m nil).
apply not_exd_nil.
tauto.
tauto.
intros.
elim (eq_dart_dec (cA_1 m k d1) z).
intro.
elim (eq_dart_dec (cA m k d0) z).
intros.
rewrite a0; rewrite a1.
tauto.
intros.
split.
assert (z = d1).
assert (cA_1 m k z = z).
generalize (IHm k z).
tauto.
symmetry in H3.
rewrite H3 in a0.
assert (inj_dart (exd m) (cA_1 m k)).
apply inj_cA_1.
tauto.
unfold inj_dart in H4.
generalize (H4 z d1).
intros.
apply H5.
tauto.
tauto.
symmetry in |- *; tauto.
symmetry in H3.
tauto.
generalize (IHm k z).
unfold pred in |- *; unfold succ in |- *.
tauto.
elim (eq_dart_dec (cA m k d0) z).
intros.
generalize (IHm k z).
unfold pred in |- *; unfold succ in |- *.
intros.
assert (z = d0).
assert (cA m k z = z).
tauto.
rewrite <- H4 in a0.
assert (inj_dart (exd m) (cA m k)).
apply inj_cA.
tauto.
unfold inj_dart in H5.
generalize (H5 z d0).
intros.
symmetry in a0.
tauto.
symmetry in H4.
tauto.
intros.
generalize (IHm k z).
tauto.
intros.
generalize (IHm k z).
Admitted.

Lemma not_exd_cA : forall (m:fmap)(k:dim)(z:dart), inv_hmap m -> ~exd m z -> cA m k z = nil.
Proof.
intros.
elim (eq_dart_dec (cA m k z) nil).
tauto.
intro.
elim H0.
apply cA_exd with k.
tauto.
tauto.
