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
tauto.
