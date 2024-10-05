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
