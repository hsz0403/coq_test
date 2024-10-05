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

Lemma bottom_A_1 : forall (m:fmap)(k:dim)(z:dart), inv_hmap m -> pred m k z -> bottom m k (A_1 m k z) = bottom m k z.
Proof.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
unfold prec_I in |- *.
unfold pred in |- *.
simpl in |- *.
intros.
elim (eq_dart_dec d (A_1 m k z)).
intro.
rewrite a in H.
absurd (exd m (A_1 m k z)).
tauto.
apply pred_exd_A_1.
tauto.
unfold pred in |- *.
tauto.
elim (eq_dart_dec d z).
intros.
rewrite a in H.
absurd (exd m z).
tauto.
apply pred_exd with k.
tauto.
unfold pred in |- *.
tauto.
intros.
apply IHm.
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
elim (eq_dart_dec d1 (bottom m d d0)).
elim (eq_dart_dec d1 (bottom m d z)).
tauto.
intros.
rewrite cA_eq in H.
generalize H.
clear H.
elim (succ_dec m d d0).
tauto.
intros.
rewrite a in H.
tauto.
tauto.
intros.
elim (eq_dart_dec d1 (bottom m d z)).
tauto.
intro.
rewrite <- a in b0.
elim b0.
rewrite nopred_bottom in |- *.
tauto.
tauto.
tauto.
tauto.
elim (eq_dart_dec d1 (bottom m d (A_1 m k z))).
elim (eq_dart_dec d1 (bottom m d z)).
tauto.
intros.
rewrite a0 in a.
rewrite IHm in a.
rewrite a0 in b.
tauto.
tauto.
unfold pred in |- *.
tauto.
elim (eq_dart_dec d1 (bottom m d z)).
intros.
rewrite a0 in b.
rewrite IHm in b.
rewrite a0 in a.
tauto.
tauto.
unfold pred in |- *; tauto.
intros.
rewrite a in |- *.
apply IHm.
tauto.
unfold pred in |- *.
tauto.
intros.
apply IHm.
tauto.
unfold pred in |- *.
Admitted.

Lemma top_A_1 : forall (m:fmap)(k:dim)(z:dart), inv_hmap m -> pred m k z -> top m k (A_1 m k z) = top m k z.
Proof.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
unfold prec_I in |- *.
unfold pred in |- *.
simpl in |- *.
intros.
elim (eq_dart_dec d (A_1 m k z)).
intro.
rewrite a in H.
absurd (exd m (A_1 m k z)).
tauto.
apply pred_exd_A_1.
tauto.
unfold pred in |- *.
tauto.
elim (eq_dart_dec d z).
intros.
rewrite a in H.
absurd (exd m z).
tauto.
apply pred_exd with k.
tauto.
unfold pred in |- *.
tauto.
intros.
apply IHm.
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
elim (eq_dart_dec d0 (top m d d0)).
elim (eq_dart_dec d0 (top m d z)).
tauto.
intros.
rewrite a0 in |- *.
tauto.
intros.
rewrite nosucc_top in b.
tauto.
tauto.
tauto.
tauto.
elim (eq_dart_dec d0 (top m d (A_1 m k z))).
elim (eq_dart_dec d0 (top m d z)).
tauto.
intros.
rewrite a0 in a.
rewrite a0 in b.
rewrite IHm in a.
tauto.
tauto.
unfold pred in |- *.
tauto.
elim (eq_dart_dec d0 (top m d z)).
intros.
rewrite a0 in b.
rewrite a0 in a.
rewrite IHm in b.
tauto.
tauto.
unfold pred in |- *.
tauto.
intros.
rewrite a in |- *.
apply IHm.
tauto.
unfold pred in |- *.
tauto.
intros.
apply IHm.
tauto.
unfold pred in |- *.
Admitted.

Lemma not_succ_top : forall (m:fmap)(k:dim)(z:dart), inv_hmap m -> ~succ m k (top m k z).
Proof.
unfold succ in |- *.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
unfold prec_I in |- *.
intros k z Inv.
elim (eq_dart_dec d z).
intros.
assert (A m k z = nil).
apply not_exd_A_nil.
tauto.
rewrite <- a.
tauto.
rewrite H.
tauto.
intro.
apply IHm.
tauto.
simpl in |- *.
unfold prec_L in |- *.
intros k z Inv.
elim (eq_dim_dec d k).
intros.
elim (eq_dart_dec d0 (top m d z)).
intro.
elim (eq_dart_dec d0 (top m d d1)).
intro.
generalize Inv.
rewrite cA_eq.
elim (succ_dec m d d0).
tauto.
rewrite a1.
rewrite bottom_top.
tauto.
tauto.
tauto.
tauto.
tauto.
intros.
rewrite a.
apply IHm.
tauto.
elim (eq_dart_dec d0 (top m d z)).
tauto.
intros.
rewrite a.
apply IHm.
tauto.
intro.
apply IHm.
Admitted.

Lemma not_pred_bottom : forall (m:fmap)(k:dim)(z:dart), inv_hmap m -> ~pred m k (bottom m k z).
Proof.
unfold pred in |- *.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
unfold prec_I in |- *.
intros k z Inv.
elim (eq_dart_dec d z).
intros.
assert (A_1 m k z = nil).
apply not_exd_A_1_nil.
tauto.
rewrite <- a in |- *.
tauto.
rewrite H in |- *.
tauto.
intro.
apply IHm.
tauto.
simpl in |- *.
unfold prec_L in |- *.
intros k z Inv.
elim (eq_dim_dec d k).
intros.
elim (eq_dart_dec d1 (bottom m d z)).
intro.
elim (eq_dart_dec d1 (bottom m d d0)).
intro.
generalize Inv.
rewrite cA_eq in |- *.
elim (succ_dec m d d0).
tauto.
rewrite a1 in |- *.
tauto.
tauto.
intros.
rewrite a in |- *.
apply IHm.
tauto.
elim (eq_dart_dec d1 (bottom m d z)).
tauto.
rewrite a in |- *.
intros.
apply IHm.
tauto.
intro.
apply IHm.
Admitted.

Lemma top_top_1 : forall (m:fmap)(k:dim)(z:dart), inv_hmap m -> ~ succ m k z -> top m k (top m k z) = top m k z.
Proof.
intros.
elim (exd_dec m z).
intros.
rewrite nosucc_top.
tauto.
tauto.
apply exd_top.
tauto.
tauto.
rewrite nosucc_top.
tauto.
tauto.
tauto.
tauto.
intros.
rewrite not_exd_top.
rewrite not_exd_top.
tauto.
tauto.
tauto.
tauto.
rewrite not_exd_top.
apply not_exd_nil.
tauto.
tauto.
Admitted.

Lemma top_top_2 : forall (m:fmap)(k:dim)(z:dart), inv_hmap m -> succ m k z -> top m k (top m k z) = top m k z.
Proof.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
unfold succ in |- *.
simpl in |- *.
intros.
elim (eq_dart_dec d z).
intro.
elim (eq_dart_dec d z).
tauto.
tauto.
elim (eq_dart_dec d (top m k z)).
tauto.
intros.
apply IHm.
tauto.
unfold succ in |- *.
tauto.
simpl in |- *.
unfold prec_L in |- *.
unfold succ in |- *.
unfold pred in |- *.
simpl in |- *.
intros.
generalize H0.
clear H0.
elim (eq_dim_dec d k).
intro.
rewrite a.
elim (eq_dart_dec d0 z).
intros.
elim (eq_dart_dec d0 (top m k z)).
elim (eq_dart_dec d0 (top m k (top m k d1))).
tauto.
intros.
elim (succ_dec m k d1).
apply IHm.
tauto.
apply top_top_1.
tauto.
elim (eq_dart_dec d0 (top m k (top m k z))).
intros.
rewrite a1 in b.
elim b.
rewrite <- a0.
apply top_top_1.
tauto.
unfold succ in |- *.
rewrite <- a.
tauto.
intros.
rewrite <- a0 in b0.
rewrite nosucc_top in b0.
tauto.
tauto.
tauto.
unfold succ in |- *.
rewrite <- a.
tauto.
elim (eq_dart_dec d0 (top m k z)).
elim (eq_dart_dec d0 (top m k (top m k d1))).
tauto.
intros.
elim (succ_dec m k d1).
apply IHm.
tauto.
apply top_top_1.
tauto.
elim (eq_dart_dec d0 (top m k (top m k z))).
intros.
rewrite IHm in a0.
tauto.
tauto.
unfold succ in |- *.
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

Lemma top_top : forall (m:fmap)(k:dim)(z:dart), inv_hmap m -> top m k (top m k z) = top m k z.
Proof.
intros.
elim (succ_dec m k z).
apply top_top_2.
tauto.
apply top_top_1.
Admitted.

Lemma bottom_bottom_1 : forall (m:fmap)(k:dim)(z:dart), inv_hmap m -> ~ pred m k z -> bottom m k (bottom m k z) = bottom m k z.
Proof.
intros.
elim (exd_dec m z).
intros.
rewrite nopred_bottom.
tauto.
tauto.
apply exd_bottom.
tauto.
tauto.
rewrite nopred_bottom.
tauto.
tauto.
tauto.
tauto.
intros.
rewrite not_exd_bottom.
rewrite not_exd_bottom.
tauto.
tauto.
tauto.
tauto.
rewrite not_exd_bottom.
apply not_exd_nil.
tauto.
tauto.
Admitted.

Lemma bottom_bottom : forall (m:fmap)(k:dim)(z:dart), inv_hmap m -> bottom m k (bottom m k z) = bottom m k z.
Proof.
intros.
elim (pred_dec m k z).
apply bottom_bottom_2.
tauto.
apply bottom_bottom_1.
Admitted.

Lemma succ_bottom:forall (m:fmap)(k:dim)(x:dart), inv_hmap m -> succ m k x -> bottom m k x <> A m k x.
Proof.
induction m.
simpl in |- *.
unfold succ in |- *.
simpl in |- *.
tauto.
simpl in |- *.
unfold succ in |- *.
unfold prec_I in |- *.
simpl in |- *.
intros.
elim (eq_dart_dec d x).
intro.
rewrite a in H.
elim H0.
apply not_exd_A_nil.
tauto.
tauto.
intro.
apply IHm.
tauto.
unfold succ in |- *.
tauto.
unfold succ in |- *.
simpl in |- *.
unfold prec_L in |- *.
unfold succ in |- *.
unfold pred in |- *.
intros.
generalize H0.
clear H0.
elim (eq_dim_dec d k).
intro.
rewrite a.
elim (eq_dart_dec d0 x).
intros.
rewrite a0.
elim (eq_dart_dec d1 (bottom m k x)).
intro.
rewrite a1 in H.
rewrite a0 in H.
rewrite a in H.
generalize (cA_eq m k x).
elim (succ_dec m k x).
unfold succ in |- *.
tauto.
unfold succ in |- *.
tauto.
intro.
intro.
symmetry in H1.
tauto.
elim (eq_dart_dec d1 (bottom m k x)).
intros.
rewrite <- bottom_A in a0.
intro.
rewrite <- H1 in a0.
rewrite bottom_bottom in a0.
generalize H.
rewrite cA_eq.
elim (succ_dec m d d0).
unfold succ in |- *.
tauto.
symmetry in a0.
rewrite a.
tauto.
tauto.
tauto.
tauto.
unfold succ in |- *.
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

Lemma pred_top :forall (m:fmap)(k:dim)(x:dart), inv_hmap m -> pred m k x -> top m k x <> A_1 m k x.
Proof.
induction m.
simpl in |- *.
unfold pred in |- *.
simpl in |- *.
tauto.
simpl in |- *.
unfold pred in |- *.
unfold prec_I in |- *.
simpl in |- *.
intros.
elim (eq_dart_dec d x).
intro.
rewrite a in H.
elim H0.
apply not_exd_A_1_nil.
tauto.
tauto.
intro.
apply IHm.
tauto.
unfold pred in |- *.
tauto.
unfold pred in |- *.
simpl in |- *.
unfold prec_L in |- *.
unfold succ in |- *.
unfold pred in |- *.
intros.
generalize H0.
clear H0.
elim (eq_dim_dec d k).
intro.
rewrite a in |- *.
elim (eq_dart_dec d1 x).
intros.
rewrite a0 in |- *.
elim (eq_dart_dec d0 (top m k x)).
intro.
rewrite a1 in H.
rewrite a0 in H.
rewrite a in H.
generalize (cA_1_eq m k x).
elim (pred_dec m k x).
unfold pred in |- *.
tauto.
unfold pred in |- *.
intros.
rewrite <- a1 in H1.
rewrite <- a1 in H.
rewrite <- H1 in H.
rewrite cA_cA_1 in H.
tauto.
tauto.
tauto.
tauto.
intro.
intro.
symmetry in H1.
tauto.
elim (eq_dart_dec d0 (top m k x)).
intros.
rewrite <- top_A_1 in a0.
intro.
rewrite <- H1 in a0.
rewrite top_top in a0.
rewrite <- a0 in H1.
assert (x = A m k d0).
rewrite H1 in |- *.
rewrite A_A_1 in |- *.
tauto.
tauto.
unfold pred in |- *.
tauto.
rewrite a in H.
rewrite <- H2 in H.
absurd (x = nil).
assert (exd m x).
eapply pred_exd.
tauto.
unfold pred in |- *.
apply H0.
apply exd_not_nil with m.
tauto.
tauto.
elim (eq_nat_dec x nil).
tauto.
tauto.
tauto.
tauto.
unfold pred in |- *.
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

Lemma cA_top:forall (m:fmap)(k:dim)(z:dart), inv_hmap m -> exd m z -> cA m k (top m k z) = bottom m k z.
Proof.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
unfold prec_I in |- *.
intros.
elim (eq_dart_dec d z).
elim (eq_dart_dec d z).
tauto.
tauto.
intro.
elim (eq_dart_dec d (top m k z)).
intro.
rewrite a in H.
absurd (exd m (top m k z)).
tauto.
apply exd_top.
tauto.
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
elim (eq_dart_dec d0 (top m d d1)).
intros.
rewrite a in H.
rewrite IHm in H.
rewrite nopred_bottom in H.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
elim (eq_dart_dec (cA_1 m k d1) (top m d d1)).
elim (eq_dart_dec d1 (bottom m d z)).
intros.
rewrite <- a2.
apply cA_bottom.
tauto.
tauto.
tauto.
intros.
rewrite a0.
rewrite a1.
apply IHm.
tauto.
tauto.
intros.
elim b.
rewrite <- a0.
apply cA_1_top.
tauto.
tauto.
tauto.
elim (eq_dart_dec d0 (top m d z)).
tauto.
intros.
elim (eq_dart_dec (cA_1 m k d1) (top m d z)).
intros.
elim (eq_dart_dec d1 (bottom m d z)).
intro.
rewrite <- a.
apply cA_bottom.
tauto.
tauto.
tauto.
intro.
rewrite <- a in a0.
assert (d1 = cA m d (top m d z)).
rewrite <- a0.
rewrite cA_cA_1.
tauto.
tauto.
tauto.
rewrite IHm in H1.
tauto.
tauto.
tauto.
intros.
elim (eq_dart_dec d1 (bottom m d z)).
intros.
rewrite <- IHm in a0.
assert (cA_1 m k d1 = top m d z).
rewrite a0.
rewrite <- a.
rewrite cA_1_cA.
tauto.
tauto.
apply exd_top.
tauto.
tauto.
tauto.
tauto.
tauto.
intro.
rewrite a.
apply IHm.
tauto.
tauto.
intro.
apply IHm.
tauto.
Admitted.

Lemma cA_1_bottom:forall (m:fmap)(k:dim)(z:dart), inv_hmap m -> exd m z -> cA_1 m k (bottom m k z) = top m k z.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
unfold prec_I in |- *.
intros.
elim (eq_dart_dec d z).
elim (eq_dart_dec d z).
tauto.
tauto.
intro.
elim (eq_dart_dec d (bottom m k z)).
intro.
rewrite a in H.
absurd (exd m (bottom m k z)).
tauto.
apply exd_bottom.
tauto.
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
elim (eq_dart_dec d1 (bottom m d d0)).
intros.
decompose [and] H.
clear H.
generalize H7.
rewrite cA_eq in |- *.
elim (succ_dec m d d0).
tauto.
symmetry in a.
tauto.
tauto.
elim (eq_dart_dec (cA m k d0) (bottom m d d0)).
elim (eq_dart_dec d0 (top m d z)).
intros.
rewrite <- a2 in |- *.
apply cA_1_top.
tauto.
tauto.
tauto.
intros.
rewrite a0 in |- *.
rewrite a1 in |- *.
apply IHm.
tauto.
tauto.
intros.
elim b.
rewrite <- a0 in |- *.
apply cA_bottom.
tauto.
tauto.
tauto.
elim (eq_dart_dec d1 (bottom m d z)).
tauto.
intros.
elim (eq_dart_dec (cA m k d0) (bottom m d z)).
intros.
elim (eq_dart_dec d0 (top m d z)).
intro.
rewrite <- a in |- *.
apply cA_1_top.
tauto.
tauto.
tauto.
intro.
rewrite <- a in a0.
assert (d0 = cA_1 m d (bottom m d z)).
rewrite <- a0 in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
tauto.
rewrite IHm in H1.
tauto.
tauto.
tauto.
intros.
elim (eq_dart_dec d0 (top m d z)).
intros.
rewrite <- IHm in a0.
assert (cA m k d0 = bottom m d z).
rewrite a0 in |- *.
rewrite <- a in |- *.
rewrite cA_cA_1 in |- *.
tauto.
tauto.
apply exd_bottom.
tauto.
tauto.
tauto.
tauto.
tauto.
intro.
rewrite a in |- *.
apply IHm.
tauto.
tauto.
intro.
apply IHm.
tauto.
Admitted.

Lemma top_top_bottom:forall(m:fmap)(k:dim)(x y:dart), inv_hmap m -> exd m x -> exd m y -> ~pred m k y -> top m k x = top m k y -> bottom m k x = y.
Proof.
intros.
assert (bottom m k (top m k x) = bottom m k (top m k y)).
rewrite H3 in |- *.
tauto.
rewrite bottom_top_bis in H4.
rewrite bottom_top_bis in H4.
rewrite (nopred_bottom m k y) in H4.
auto.
auto.
auto.
auto.
auto.
auto.
auto.
Admitted.

Lemma bottom_bottom_top:forall(m:fmap)(k:dim)(x y:dart), inv_hmap m -> exd m x -> exd m y -> ~succ m k y -> bottom m k x = bottom m k y -> top m k x = y.
Proof.
intros.
assert (top m k (bottom m k x) = top m k (bottom m k y)).
rewrite H3 in |- *.
tauto.
rewrite top_bottom_bis in H4.
rewrite top_bottom_bis in H4.
rewrite (nosucc_top m k y) in H4.
auto.
auto.
auto.
auto.
auto.
auto.
auto.
Admitted.

Lemma top_top_bottom_bottom:forall(m:fmap)(k:dim)(x y:dart), inv_hmap m -> exd m x -> exd m y -> top m k x = top m k y -> bottom m k x = bottom m k y.
Proof.
intros.
assert (exd m (bottom m k y)).
apply exd_bottom.
tauto.
tauto.
assert (~ pred m k (bottom m k y)).
apply not_pred_bottom.
tauto.
assert (top m k x = top m k (bottom m k y)).
rewrite top_bottom_bis in |- *.
tauto.
tauto.
tauto.
Admitted.

Lemma bottom_bottom_top_top:forall(m:fmap)(k:dim)(x y:dart), inv_hmap m -> exd m x -> exd m y -> bottom m k x = bottom m k y -> top m k x = top m k y.
Proof.
intros.
assert (exd m (top m k y)).
apply exd_top.
tauto.
tauto.
assert (~ succ m k (top m k y)).
apply not_succ_top.
tauto.
assert (bottom m k x = bottom m k (top m k y)).
rewrite bottom_top_bis in |- *.
tauto.
tauto.
tauto.
Admitted.

Lemma cA_cA_1_B : forall (m:fmap)(k:dim)(x z:dart), inv_hmap m -> succ m k x -> cA (B m k x) k z = (if eq_dart_dec x z then bottom m k x else if eq_dart_dec (top m k x) z then A m k x else cA m k z) /\ cA_1 (B m k x) k z = (if eq_dart_dec (A m k x) z then top m k x else if eq_dart_dec (bottom m k x) z then x else cA_1 m k z).
Proof.
induction m.
unfold succ in |- *.
simpl in |- *.
tauto.
simpl in |- *.
unfold prec_I in |- *.
unfold succ in |- *.
simpl in |- *.
intros.
elim (eq_dart_dec d x).
intro.
rewrite a in H.
absurd (exd m x).
tauto.
apply succ_exd with k.
tauto.
unfold succ in |- *.
tauto.
intro.
elim (eq_dart_dec d z).
intro.
elim (eq_dart_dec x z).
intro.
rewrite a0 in b.
tauto.
intro.
split.
elim (eq_dart_dec (top m k x) z).
intro.
rewrite a in H.
rewrite <- a0 in H.
absurd (exd m (top m k x)).
tauto.
apply exd_top.
tauto.
apply succ_exd with k.
tauto.
unfold succ in |- *.
tauto.
tauto.
elim (eq_dart_dec (A m k x) z).
intro.
rewrite <- a in a0.
rewrite <- a0 in H.
absurd (exd m (A m k x)).
tauto.
apply succ_exd_A.
tauto.
unfold succ in |- *.
tauto.
intro.
elim (eq_dart_dec (bottom m k x) z).
intro.
rewrite <- a in a0.
rewrite <- a0 in H.
absurd (exd m (bottom m k x)).
tauto.
apply exd_bottom.
tauto.
apply succ_exd with k.
tauto.
unfold succ in |- *.
tauto.
tauto.
intro.
apply IHm.
tauto.
unfold succ in |- *.
tauto.
unfold succ in |- *.
simpl in |- *.
unfold prec_L in |- *.
intros.
decompose [and] H.
clear H.
generalize H0.
clear H0.
rename d into i.
elim (eq_dim_dec i k).
intro.
rewrite <- a.
elim (eq_dart_dec d0 x).
intro.
rewrite <- a0.
intro.
elim (eq_dart_dec d1 (bottom m i d0)).
intro.
rewrite a1 in H7.
generalize H7.
clear H7.
rewrite cA_eq.
elim (succ_dec m i d0).
tauto.
tauto.
tauto.
intro.
elim (eq_dart_dec d0 (top m i d0)).
intro.
split.
elim (eq_dart_dec d0 z).
intro.
rewrite <- a2.
rewrite cA_eq.
elim (succ_dec m i d0).
tauto.
tauto.
tauto.
intro.
elim (eq_dart_dec (top m i d1) z).
intro.
assert (~ succ m i z).
rewrite <- a2.
apply not_succ_top.
tauto.
rewrite cA_eq.
elim (succ_dec m i z).
tauto.
intro.
rewrite <- a2.
apply bottom_top.
tauto.
tauto.
tauto.
tauto.
intro.
elim (eq_dart_dec (cA_1 m i d1) z).
rewrite cA_1_eq.
elim (pred_dec m i d1).
tauto.
tauto.
tauto.
tauto.
elim (eq_dart_dec d1 z).
intro.
rewrite <- a2.
rewrite cA_1_eq.
elim (pred_dec m i d1).
tauto.
tauto.
tauto.
intro.
elim (eq_dart_dec (bottom m i d0) z).
intro.
assert (~ pred m i z).
rewrite <- a2.
apply not_pred_bottom.
tauto.
rewrite cA_1_eq.
elim (pred_dec m i z).
tauto.
intro.
rewrite <- a2.
apply top_bottom.
tauto.
tauto.
tauto.
tauto.
intro.
elim (eq_dart_dec (cA m i d0) z).
rewrite cA_eq.
elim (succ_dec m i d0).
tauto.
tauto.
tauto.
tauto.
intro.
elim b0.
rewrite nosucc_top.
tauto.
tauto.
tauto.
tauto.
intros.
fold (succ m i x) in H0.
elim (eq_dart_dec d0 (top m i x)).
intro.
elim (eq_dart_dec d1 (bottom m i x)).
intro.
rewrite a1 in H7.
rewrite a0 in H7.
elim H7.
apply cA_top.
tauto.
apply succ_exd with i.
tauto.
unfold succ in |- *.
unfold succ in H0.
tauto.
intro.
split.
simpl in |- *.
elim (eq_dim_dec i i).
intro.
clear a1.
elim (eq_dart_dec d0 z).
intro.
elim (eq_dart_dec x z).
intro.
rewrite <- a2 in a1.
tauto.
elim (eq_dart_dec (top m i d1) z).
intros.
rewrite <- a2 in a1.
rewrite a1 in a0.
elim b0.
symmetry in |- *.
apply top_top_bottom.
tauto.
apply succ_exd with i.
tauto.
tauto.
tauto.
tauto.
symmetry in |- *.
tauto.
tauto.
intro.
elim (eq_dart_dec (cA_1 (B m i x) i d1) z).
intro.
generalize (IHm i x d0 H1 H0).
intros.
elim H.
clear H.
intros.
generalize (IHm i x d1 H1 H0).
intros.
elim H8.
clear H8.
intros.
generalize H.
clear H.
elim (eq_dart_dec x z).
intro.
elim (eq_dart_dec x d0).
tauto.
intro.
elim (eq_dart_dec (top m i x) d0).
intros.
rewrite <- a2 in a1.
generalize a1.
clear a1.
rewrite H9.
clear H9.
elim (eq_dart_dec (A m i x) d1).
intros.
rewrite a4 in a0.
tauto.
intro.
elim (eq_dart_dec (bottom m i x) d1).
intros.
symmetry in a1.
tauto.
intros.
rewrite cA_1_eq in a1.
generalize a1.
clear a1.
elim (pred_dec m i d1).
tauto.
intros.
rewrite <- a1 in b4.
rewrite bottom_top in b4.
tauto.
tauto.
tauto.
tauto.
tauto.
intros.
rewrite H.
rewrite cA_eq.
elim (succ_dec m i d0).
tauto.
intro.
rewrite a0.
apply bottom_top_bis.
tauto.
apply succ_exd with i.
tauto.
tauto.
tauto.
intro.
elim (eq_dart_dec x d0).
intro.
symmetry in a2.
tauto.
intro.
elim (eq_dart_dec (top m i x) d0).
intros.
elim (eq_dart_dec (top m i d1) z).
intros.
tauto.
intro.
elim (eq_dart_dec (cA_1 m i d1) z).
intro.
rewrite cA_1_eq in a3.
generalize a3.
elim (pred_dec m i d1).
tauto.
tauto.
tauto.
intro.
rewrite H.
generalize H9.
clear H9.
elim (eq_dart_dec (A m i x) d1).
intros.
rewrite <- a3 in H5.
unfold pred in H5.
rewrite A_1_A in H5.
absurd (x <> nil).
tauto.
apply exd_not_nil with m.
tauto.
apply succ_exd with i.
tauto.
tauto.
tauto.
tauto.
intro.
elim (eq_dart_dec (bottom m i x) d1).
intros.
symmetry in a3.
tauto.
intros.
rewrite a1 in H9.
symmetry in H9.
tauto.
symmetry in a0.
tauto.
intro.
generalize (IHm i x z H1 H0).
intros.
elim H.
clear H.
intros.
generalize (IHm i x d1 H1 H0).
intros.
elim H8.
clear H8.
intros.
generalize H.
clear H.
elim (eq_dart_dec x z).
tauto.
elim (eq_dart_dec (top m i x) z).
intros.
rewrite a1 in a0.
tauto.
intros.
elim (eq_dart_dec (top m i d1) z).
intros.
generalize H9.
clear H9.
elim (eq_dart_dec (A m i x) d1).
intro.
rewrite <- a2 in a1.
rewrite top_A in a1.
tauto.
tauto.
tauto.
elim (eq_dart_dec (bottom m i x) d1).
intros.
symmetry in a2.
tauto.
intros.
rewrite H9 in b2.
generalize b2.
rewrite cA_1_eq.
elim (pred_dec m i d1).
tauto.
tauto.
tauto.
elim (eq_dart_dec (cA_1 m i d1) z).
intros.
rewrite cA_1_eq in a1.
generalize a1.
elim (pred_dec m i d1).
tauto.
tauto.
tauto.
intros.
tauto.
tauto.
simpl in |- *.
elim (eq_dim_dec i i).
intro.
elim (eq_dart_dec d1 z).
intro.
rewrite <- a2.
elim (eq_dart_dec (A m i x) d1).
intros.
assert (d0 = top m i d1).
rewrite <- a3.
rewrite top_A.
tauto.
tauto.
tauto.
tauto.
elim (eq_dart_dec (bottom m i x) d1).
intros.
symmetry in a3.
tauto.
tauto.
intro.
elim (eq_dart_dec (cA (B m i x) i d0) z).
intro.
generalize (IHm i x d0 H1 H0).
intro.
elim H.
clear H.
intros.
generalize (IHm i x d1 H1 H0).
intro.
elim H8.
clear H8.
intros.
generalize H9.
clear H9.
generalize H.
clear H.
elim (eq_dart_dec x d0).
intro.
symmetry in a3.
tauto.
elim (eq_dart_dec (top m i x) d0).
intros.
generalize H9.
clear H9.
clear b2 a3.
elim (eq_dart_dec (A m i x) d1).
intros.
rewrite <- a3 in H5.
unfold pred in H5.
rewrite A_1_A in H5.
absurd (x <> nil).
tauto.
apply exd_not_nil with m.
tauto.
apply succ_exd with i.
tauto.
tauto.
tauto.
tauto.
intro.
elim (eq_dart_dec (bottom m i x) d1).
intro.
symmetry in |- *.
symmetry in a3.
tauto.
intros.
elim (eq_dart_dec (A m i x) z).
intro.
rewrite H9.
rewrite cA_1_eq.
elim (pred_dec m i d1).
tauto.
tauto.
tauto.
intro.
rewrite H in a2.
tauto.
intros.
generalize H9.
clear H9.
elim (eq_dart_dec (A m i x) d1).
intros.
rewrite <- a3 in H5.
unfold pred in H5.
rewrite A_1_A in H5.
absurd (x <> nil).
tauto.
apply exd_not_nil with m.
tauto.
apply succ_exd with i.
tauto.
tauto.
tauto.
tauto.
intro.
elim (eq_dart_dec (bottom m i x) d1).
intro.
symmetry in a3.
tauto.
intros.
elim (eq_dart_dec (A m i x) z).
intro.
rewrite H9.
rewrite cA_1_eq.
elim (pred_dec m i d1).
tauto.
tauto.
tauto.
intro.
symmetry in a0.
tauto.
intro.
generalize (IHm i x d0 H1 H0).
intro.
elim H.
clear H.
intros.
generalize (IHm i x z H1 H0).
intro.
elim H8.
clear H8.
intros.
generalize H9.
clear H9.
elim (eq_dart_dec (A m i x) z).
intros.
rewrite <- a0 in H9.
rewrite H in b2.
generalize b2.
clear b2.
elim (eq_dart_dec x d0).
intro.
symmetry in a3.
tauto.
elim (eq_dart_dec (top m i x) d0).
intros.
tauto.
intro.
symmetry in a0.
tauto.
intro.
elim (eq_dart_dec (bottom m i x) z).
tauto.
intros.
elim (eq_dart_dec (cA m i d0) z).
intro.
generalize a2.
rewrite cA_eq.
elim (succ_dec m i d0).
tauto.
intros.
rewrite a0 in a3.
rewrite bottom_top_bis in a3.
tauto.
tauto.
apply succ_exd with i.
tauto.
tauto.
tauto.
tauto.
tauto.
intro.
simpl in |- *.
elim (eq_dim_dec i i).
intro.
split.
elim (eq_dart_dec d0 z).
intro.
rewrite <- a1.
elim (eq_dart_dec x d0).
intro.
symmetry in a2.
tauto.
intro.
elim (eq_dart_dec (top m i x) d0).
intro.
symmetry in a2.
tauto.
tauto.
intro.
elim (eq_dart_dec x z).
intro.
rewrite <- a1.
generalize (IHm i x d1 H1 H0).
intro.
elim H.
clear H.
intros.
elim (eq_dart_dec (cA_1 (B m i x) i d1) x).
intros.
generalize (IHm i x d0 H1 H0).
intro.
elim H8.
clear H8.
intros.
rewrite H8.
elim (eq_dart_dec x d0).
intro.
symmetry in a3.
tauto.
intro.
elim (eq_dart_dec (top m i x) d0).
intro.
symmetry in a3.
tauto.
intro.
clear H8.
elim (eq_dart_dec d1 (bottom m i x)).
intro.
rewrite cA_eq.
elim (succ_dec m i d0).
tauto.
tauto.
tauto.
intros.
rewrite H6 in a2.
generalize a2.
elim (eq_dart_dec (A m i x) d1).
intro.
rewrite <- a3 in H5.
unfold pred in H5.
rewrite A_1_A in H5.
absurd (x <> nil).
tauto.
apply exd_not_nil with m.
tauto.
apply succ_exd with i.
tauto.
tauto.
tauto.
tauto.
intro.
elim (eq_dart_dec (bottom m i x) d1).
intro.
symmetry in a3.
tauto.
intros.
rewrite cA_1_eq in a3.
generalize a3.
elim (pred_dec m i d1).
tauto.
intros.
rewrite <- a4 in H0.
absurd (succ m i (top m i d1)).
apply not_succ_top.
tauto.
tauto.
tauto.
rewrite H6.
clear H6.
elim (eq_dart_dec (A m i x) d1).
intro.
rewrite <- a2 in H5.
unfold pred in H5.
rewrite A_1_A in H5.
absurd (x <> nil).
tauto.
apply exd_not_nil with m.
tauto.
apply succ_exd with i.
tauto.
tauto.
tauto.
tauto.
intro.
elim (eq_dart_dec (bottom m i x) d1).
intros.
tauto.
elim (eq_dart_dec d1 (bottom m i x)).
intros.
symmetry in a2.
tauto.
intros.
generalize (IHm i x x H1 H0).
intro.
elim H6.
clear H6.
intros.
rewrite H6.
clear H6.
elim (eq_dart_dec x x).
tauto.
tauto.
intro.
generalize (IHm i x z H1 H0).
intro.
elim H.
clear H.
intros.
generalize (IHm i x d1 H1 H0).
intro.
elim H8.
clear H8.
intros.
generalize H9.
elim (eq_dart_dec (A m i x) d1).
intro.
rewrite <- a1 in H5.
unfold pred in H5.
rewrite A_1_A in H5.
absurd (x <> nil).
tauto.
apply exd_not_nil with m.
tauto.
apply succ_exd with i.
tauto.
tauto.
tauto.
tauto.
elim (eq_dart_dec (bottom m i x) d1).
intros.
rewrite H10.
elim (eq_dart_dec x z).
tauto.
intro.
rewrite H.
clear H.
elim (eq_dart_dec x z).
tauto.
elim (eq_dart_dec (top m i x) z).
tauto.
elim (eq_dart_dec (cA_1 m i d1) z).
intros.
rewrite cA_1_eq in a2.
generalize a2; clear a2.
elim (pred_dec m i d1).
tauto.
intros.
rewrite cA_eq.
elim (succ_dec m i z).
intro.
rewrite <- a2 in a3.
absurd (succ m i (top m i d1)).
apply not_succ_top.
tauto.
tauto.
rewrite cA_eq.
elim (succ_dec m i d0).
tauto.
intros.
rewrite <- a1 in a2.
rewrite top_bottom_bis in a2.
tauto.
tauto.
apply succ_exd with i.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
intro.
intros.
elim (eq_dart_dec (cA_1 (B m i x) i d1) z).
intros.
generalize (IHm i x d0 H1 H0).
intro.
elim H11.
clear H11.
intros.
rewrite H11.
clear H11.
elim (eq_dart_dec x d0).
intro.
symmetry in a2.
tauto.
elim (eq_dart_dec (top m i x) d0).
intro.
symmetry in a2.
tauto.
intros.
elim (eq_dart_dec (top m i x) z).
intro.
rewrite H10 in a1.
generalize a1.
rewrite cA_1_eq.
elim (pred_dec m i d1).
tauto.
intros.
rewrite <- a3 in a2.
assert (bottom m i x = d1).
apply top_top_bottom.
tauto.
apply succ_exd with i.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
elim (eq_dart_dec (cA_1 m i d1) z).
tauto.
intros.
rewrite H10 in a1.
tauto.
intro.
rewrite H.
clear H.
elim (eq_dart_dec x z).
tauto.
elim (eq_dart_dec (top m i x) z).
intros.
tauto.
elim (eq_dart_dec (cA_1 m i d1) z).
rewrite H10 in b5.
tauto.
tauto.
generalize (IHm i x d0 H1 H0).
intro.
elim H.
clear H.
intros.
generalize H.
clear H.
elim (eq_dart_dec x d0).
intro.
symmetry in a1.
tauto.
elim (eq_dart_dec (top m i x) d0).
intro.
symmetry in a1.
tauto.
intros.
elim (eq_dart_dec d1 z).
intro.
rewrite <- a1.
elim (eq_dart_dec (A m i x) d1).
intro.
rewrite <- a2 in H5.
unfold pred in H5.
rewrite A_1_A in H5.
absurd (x <> nil).
tauto.
apply exd_not_nil with m.
tauto.
apply succ_exd with i.
tauto.
tauto.
tauto.
tauto.
elim (eq_dart_dec d1 (bottom m i x)).
intros.
elim (eq_dart_dec (bottom m i d0) d1).
intros.
rewrite <- a3 in a2.
symmetry in a2.
assert (top m i x = d0).
apply bottom_bottom_top.
tauto.
apply succ_exd with i.
tauto.
tauto.
tauto.
tauto.
tauto.
symmetry in H8.
tauto.
tauto.
elim (eq_dart_dec (bottom m i x) d1).
intro.
symmetry in a2.
tauto.
tauto.
intro.
elim (eq_dart_dec (cA (B m i x) i d0) z).
intro.
generalize (IHm i x d1 H1 H0).
intro.
elim H8.
clear H8.
intros.
rewrite H9.
clear H9.
elim (eq_dart_dec (A m i x) d1).
intro.
rewrite <- a2 in H5.
unfold pred in H5.
rewrite A_1_A in H5.
absurd (x <> nil).
tauto.
apply exd_not_nil with m.
tauto.
apply succ_exd with i.
tauto.
tauto.
tauto.
tauto.
elim (eq_dart_dec (bottom m i x) d1).
intros.
assert (cA m i d0 = bottom m i d0).
rewrite cA_eq.
elim (succ_dec m i d0).
tauto.
tauto.
tauto.
elim (eq_dart_dec (A m i x) z).
intro.
assert (pred m i z).
unfold pred in |- *.
rewrite <- a3.
rewrite A_1_A.
apply exd_not_nil with m.
tauto.
apply succ_exd with i.
tauto.
tauto.
tauto.
tauto.
rewrite <- a1 in H10.
rewrite H in H10.
rewrite H9 in H10.
absurd (pred m i (bottom m i d0)).
apply not_pred_bottom.
tauto.
tauto.
intro.
elim (eq_dart_dec d1 (bottom m i x)).
intro.
elim (eq_dart_dec (bottom m i d0) z).
tauto.
elim (eq_dart_dec (cA m i d0) z).
intros.
rewrite H9 in a4.
tauto.
intros.
rewrite H in a1.
tauto.
intro.
elim (eq_dart_dec (bottom m i x) z).
tauto.
elim (eq_dart_dec (cA m i d0) z).
intros.
rewrite cA_1_eq.
elim (pred_dec m i d1).
tauto.
intro.
symmetry in a2.
tauto.
tauto.
rewrite H in a1.
tauto.
intros.
elim (eq_dart_dec (A m i x) z).
intro.
rewrite cA_1_eq.
rewrite H in a1.
generalize a1.
rewrite cA_eq.
elim (succ_dec m i d0).
tauto.
intros.
assert (pred m i z).
rewrite <- a2.
unfold pred in |- *.
rewrite A_1_A.
apply exd_not_nil with m.
tauto.
apply succ_exd with i.
tauto.
tauto.
tauto.
tauto.
rewrite <- a3 in H9.
absurd (pred m i (bottom m i d0)).
apply not_pred_bottom.
tauto.
tauto.
tauto.
tauto.
intro.
elim (eq_dart_dec d1 (bottom m i x)).
intro.
symmetry in a2.
tauto.
elim (eq_dart_dec (bottom m i x) z).
intros.
rewrite H in a1.
generalize a1.
rewrite cA_eq.
elim (succ_dec m i d0).
intros.
tauto.
intros.
rewrite <- a3 in a2.
elim b1.
apply bottom_bottom_top.
tauto.
apply succ_exd with i.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
elim (eq_dart_dec (cA m i d0) z).
tauto.
intros.
rewrite H in a1.
tauto.
intro.
generalize (IHm i x z H1 H0).
intro.
elim H8.
clear H8.
intros.
rewrite H9.
clear H9.
elim (eq_dart_dec (A m i x) z).
tauto.
elim (eq_dart_dec (bottom m i x) z).
intros.
elim (eq_dart_dec d1 (bottom m i x)).
intro.
rewrite a1 in a2.
tauto.
elim (eq_dart_dec (bottom m i x) z).
tauto.
tauto.
elim (eq_dart_dec d1 (bottom m i x)).
intros.
elim (eq_dart_dec (bottom m i d0) z).
intros.
rewrite H in b4.
generalize b4.
rewrite cA_eq.
elim (succ_dec m i d0).
tauto.
tauto.
tauto.
elim (eq_dart_dec (cA m i d0) z).
rewrite H in b4.
tauto.
tauto.
intros.
elim (eq_dart_dec (bottom m i x) z).
intro.
tauto.
elim (eq_dart_dec (cA m i d0) z).
intros.
rewrite H in b4.
tauto.
tauto.
tauto.
simpl in |- *.
elim (eq_dim_dec i k).
tauto.
intros.
fold succ in H0.
fold (succ m k x) in H0.
apply IHm.
tauto.
Admitted.

Lemma bottom_bottom_2 : forall (m:fmap)(k:dim)(z:dart), inv_hmap m -> pred m k z -> bottom m k (bottom m k z) = bottom m k z.
Proof.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
unfold pred in |- *.
simpl in |- *.
intros.
elim (eq_dart_dec d z).
intro.
elim (eq_dart_dec d z).
tauto.
tauto.
elim (eq_dart_dec d (bottom m k z)).
tauto.
intros.
apply IHm.
tauto.
unfold pred in |- *.
tauto.
simpl in |- *.
unfold prec_L in |- *.
unfold succ in |- *.
unfold pred in |- *.
simpl in |- *.
intros.
generalize H0.
clear H0.
elim (eq_dim_dec d k).
intro.
rewrite a in |- *.
elim (eq_dart_dec d1 z).
intros.
elim (eq_dart_dec d1 (bottom m k z)).
elim (eq_dart_dec d1 (bottom m k (bottom m k d0))).
tauto.
intros.
elim (pred_dec m k d0).
apply IHm.
tauto.
apply bottom_bottom_1.
tauto.
elim (eq_dart_dec d1 (bottom m k (bottom m k z))).
intros.
rewrite a1 in b.
elim b.
rewrite <- a0 in |- *.
apply bottom_bottom_1.
tauto.
unfold pred in |- *.
rewrite <- a in |- *.
tauto.
intros.
rewrite <- a0 in b0.
rewrite nopred_bottom in b0.
tauto.
tauto.
tauto.
unfold pred in |- *.
rewrite <- a in |- *.
tauto.
elim (eq_dart_dec d1 (bottom m k z)).
elim (eq_dart_dec d1 (bottom m k (bottom m k d0))).
tauto.
intros.
elim (pred_dec m k d0).
apply IHm.
tauto.
apply bottom_bottom_1.
tauto.
elim (eq_dart_dec d1 (bottom m k (bottom m k z))).
intros.
rewrite IHm in a0.
tauto.
tauto.
unfold pred in |- *.
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
tauto.
