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
tauto.
