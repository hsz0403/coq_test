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

Lemma eq_dim_dec : forall i k : dim, {i=k}+{~i=k}.
Proof.
double induction i k.
tauto.
right.
discriminate.
right.
discriminate.
Admitted.

Lemma Req_dec_1 : forall r1 r2 : R, {r1 = r2} + {r1 <> r2}.
Proof.
Admitted.

Lemma eq_point_dec : forall (p q:point), {eq_point p q} + {~eq_point p q}.
Proof.
intros.
unfold eq_point in |- *.
elim p.
elim q.
simpl in |- *.
intros.
generalize (Req_dec_1 a0 a).
generalize (Req_dec_1 b0 b).
Admitted.

Lemma empty_dec: forall (m:fmap), {empty m}+{~empty m}.
Proof.
intro m.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
tauto.
right.
intro.
Admitted.

Lemma exd_dec: forall (m:fmap)(x:dart), {exd m x}+{~exd m x}.
Proof.
induction m.
right.
intro.
inversion H.
intro.
simpl.
elim (IHm x).
left.
simpl in |- *.
tauto.
intro.
elim (eq_dart_dec d x).
tauto.
tauto.
intro.
elim (IHm x).
left.
simpl in |- *.
assumption.
simpl in |- *.
Admitted.

Lemma succ_dec: forall (m:fmap)(k:dim)(x:dart), {succ m k x} + {~succ m k x}.
Proof.
intros.
unfold succ in |- *.
elim (eq_dart_dec (A m k x) nil).
tauto.
Admitted.

Lemma pred_dec: forall (m:fmap)(k:dim)(x:dart), {pred m k x} + {~pred m k x}.
Proof.
intros.
unfold pred in |- *.
elim (eq_dart_dec (A_1 m k x) nil).
tauto.
Admitted.

Lemma not_exd_nil : forall m:fmap, inv_hmap m -> ~exd m nil.
Proof.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
unfold prec_I in |- *.
intros.
intro.
elim H0.
intro.
symmetry in H1.
tauto.
tauto.
simpl in |- *.
Admitted.

Lemma exd_not_nil : forall (m:fmap)(z:dart), inv_hmap m -> exd m z -> z <> nil.
Proof.
intros.
elim (eq_dart_dec z nil).
intro.
rewrite a in H0.
assert (~ exd m nil).
apply not_exd_nil.
tauto.
tauto.
Admitted.

Lemma succ_exd : forall (m:fmap)(k:dim)(z:dart), inv_hmap m -> succ m k z -> exd m z.
Proof.
unfold succ in |- *.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
unfold prec_I in |- *.
intros k z Hinv.
elim (eq_dart_dec d z).
tauto.
intros.
right.
eapply IHm.
tauto.
apply H.
intros k z.
simpl in |- *.
unfold prec_L in |- *.
elim (eq_dim_dec d k).
elim (eq_dart_dec d0 z).
intros.
rewrite <- a in |- *.
tauto.
intros.
eapply IHm.
tauto.
apply H0.
intros.
eapply IHm.
tauto.
Admitted.

Lemma pred_exd : forall (m:fmap)(k:dim)(z:dart), inv_hmap m -> pred m k z -> exd m z.
Proof.
unfold pred in |- *.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
unfold prec_I in |- *.
intros k z Hinv.
elim (eq_dart_dec d z).
tauto.
intros.
right.
eapply IHm.
tauto.
apply H.
intros k z.
simpl in |- *.
unfold prec_L in |- *.
elim (eq_dim_dec d k).
elim (eq_dart_dec d1 z).
intros.
rewrite <-a.
tauto.
intros.
eapply IHm.
tauto.
apply H0.
intros.
eapply IHm.
tauto.
Admitted.

Lemma not_exd_A_nil: forall (m:fmap)(k:dim)(z:dart), inv_hmap m -> ~exd m z -> A m k z = nil.
Proof.
intros.
elim (eq_dart_dec (A m k z) nil).
tauto.
intros.
generalize (succ_exd m k z).
intro.
unfold succ in H1.
absurd (exd m z).
tauto.
eapply H1.
tauto.
Admitted.

Lemma not_exd_A_1_nil: forall (m:fmap)(k:dim)(z:dart), inv_hmap m -> ~exd m z -> A_1 m k z = nil.
Proof.
intros.
elim (eq_dart_dec (A_1 m k z) nil).
tauto.
intros.
generalize (pred_exd m k z).
intro.
unfold pred in H1.
absurd (exd m z).
tauto.
eapply H1.
tauto.
Admitted.

Lemma A_nil: forall (m:fmap)(k:dim), inv_hmap m -> A m k nil = nil.
Proof.
intros.
apply not_exd_A_nil.
tauto.
apply not_exd_nil.
Admitted.

Lemma A_1_nil: forall (m:fmap)(k:dim), inv_hmap m -> A_1 m k nil = nil.
Proof.
intros.
apply not_exd_A_1_nil.
tauto.
apply not_exd_nil.
Admitted.

Lemma pred_exd_A_1 : forall (m:fmap)(k:dim)(z:dart), inv_hmap m -> pred m k z -> exd m (A_1 m k z).
Proof.
induction m.
simpl in |- *.
unfold pred in |- *.
simpl in |- *.
tauto.
simpl in |- *.
unfold pred in |- *.
unfold prec_I in |- *.
intros k z Hinv Hx.
simpl in Hx.
generalize Hx.
clear Hx.
intro.
right.
apply IHm.
tauto.
unfold pred in |- *.
tauto.
unfold pred in |- *.
simpl in |- *.
unfold prec_L in |- *.
intros k z.
elim (eq_dim_dec d k).
elim (eq_dart_dec d1 z).
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

Lemma not_exd_cA : forall (m:fmap)(k:dim)(z:dart), inv_hmap m -> ~exd m z -> cA m k z = nil.
Proof.
intros.
elim (eq_dart_dec (cA m k z) nil).
tauto.
intro.
elim H0.
apply cA_exd with k.
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

Lemma succ_exd_A : forall (m:fmap)(k:dim)(z:dart), inv_hmap m -> succ m k z -> exd m (A m k z).
Proof.
induction m.
simpl in |- *.
unfold succ in |- *.
simpl in |- *.
tauto.
simpl in |- *.
unfold succ in |- *.
unfold prec_I in |- *.
intros k z Hinv Hx.
simpl in Hx.
generalize Hx.
clear Hx.
intro.
right.
apply IHm.
tauto.
unfold succ in |- *.
tauto.
unfold succ in |- *.
simpl in |- *.
unfold prec_L in |- *.
intros k z.
elim (eq_dim_dec d k).
elim (eq_dart_dec d0 z).
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
tauto.
