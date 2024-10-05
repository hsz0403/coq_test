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

Lemma nopred_bottom : forall (m:fmap)(k:dim)(z:dart), inv_hmap m -> exd m z -> ~pred m k z -> bottom m k z = z.
Proof.
induction m.
unfold pred in |- *.
simpl in |- *.
tauto.
unfold pred in |- *.
simpl in |- *.
intros.
elim (eq_dart_dec d z).
tauto.
intro.
unfold pred in IHm.
apply IHm.
tauto.
tauto.
tauto.
unfold pred in |- *.
simpl in |- *.
unfold prec_L in |- *.
intros k z Inv E.
elim (eq_dim_dec d k).
intro.
rewrite a.
elim (eq_dart_dec d1 z).
elim (eq_dart_dec d1 (bottom m k z)).
intros.
absurd (d0 <> nil).
tauto.
apply exd_not_nil with m.
tauto.
tauto.
intros.
absurd (d0 <> nil).
tauto.
apply exd_not_nil with m.
tauto.
tauto.
elim (eq_dart_dec d1 (bottom m k z)).
intros.
decompose [and] Inv.
generalize (IHm k z H0 E).
unfold pred in |- *.
intro.
rewrite H5 in a0.
tauto; tauto.
tauto.
intros.
apply IHm.
tauto.
tauto.
unfold pred in |- *.
tauto.
intros.
apply IHm.
tauto.
tauto.
unfold pred in |- *; tauto.
