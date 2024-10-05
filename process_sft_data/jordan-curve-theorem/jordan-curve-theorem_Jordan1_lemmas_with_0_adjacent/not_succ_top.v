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
tauto.
