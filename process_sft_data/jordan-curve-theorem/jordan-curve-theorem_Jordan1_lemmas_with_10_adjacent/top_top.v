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

Lemma top_top : forall (m:fmap)(k:dim)(z:dart), inv_hmap m -> top m k (top m k z) = top m k z.
Proof.
intros.
elim (succ_dec m k z).
apply top_top_2.
tauto.
apply top_top_1.
tauto.
