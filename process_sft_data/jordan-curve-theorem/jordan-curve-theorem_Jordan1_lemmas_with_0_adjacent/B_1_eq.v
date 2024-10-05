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

Lemma B_1_eq : forall (m:fmap)(k:dim)(x:dart), inv_hmap m -> B_1 m k x = B m k (A_1 m k x).
Proof.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
intros.
decompose [and] H.
clear H.
rewrite IHm in |- *.
auto.
assumption.
simpl in |- *.
unfold prec_L in |- *.
unfold pred in |- *.
unfold succ in |- *.
intros.
decompose [and] H.
clear H.
elim (eq_dim_dec d k).
elim (eq_dart_dec d1 x).
elim (eq_dart_dec d0 d0).
auto.
tauto.
elim (eq_dart_dec d0 (A_1 m k x)).
intros.
assert (pred m k x).
unfold pred in |- *.
rewrite <- a in |- *.
eapply exd_not_nil.
apply H0.
tauto.
rewrite a in H3.
rewrite a0 in H3.
rewrite A_A_1 in H3.
absurd (x <> nil).
tauto.
assert (exd m x).
apply pred_exd with k.
tauto.
tauto.
eapply exd_not_nil.
apply H0.
tauto.
tauto.
tauto.
intros.
rewrite IHm in |- *.
tauto.
tauto.
intro.
rewrite IHm in |- *.
tauto.
tauto.
