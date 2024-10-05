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
generalize (IHm k z); tauto.
