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
tauto.
