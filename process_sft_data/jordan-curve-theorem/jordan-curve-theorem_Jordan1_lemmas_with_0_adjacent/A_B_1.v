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

Lemma A_B_1 : forall (m:fmap)(k:dim)(x:dart), inv_hmap m -> A (B_1 m k x) k (A_1 m k x) = nil.
Proof.
intros m k x.
elim (eq_dart_dec x nil).
intros.
rewrite a in |- *.
rewrite B_1_nil in |- *.
rewrite A_1_nil in |- *.
rewrite A_nil in |- *.
tauto.
tauto.
tauto.
tauto.
intro.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
intros.
apply IHm.
tauto.
simpl in |- *.
elim (eq_dim_dec d k).
elim (eq_dart_dec d1 x).
intros.
unfold prec_L in H.
unfold succ in H.
elim (eq_dart_dec (A m d d0) nil).
rewrite a0 in |- *.
tauto.
tauto.
simpl in |- *.
elim (eq_dim_dec d k).
elim (eq_dart_dec d0 (A_1 m k x)).
intros.
unfold prec_L in H.
assert (x = A m k d0).
rewrite a in |- *.
symmetry in |- *.
apply A_A_1.
tauto.
unfold pred in |- *.
rewrite <- a in |- *.
apply (exd_not_nil m d0).
tauto.
tauto.
unfold succ in H.
rewrite a0 in H.
rewrite <- H0 in H.
tauto.
intros.
apply IHm.
tauto.
tauto.
simpl in |- *.
elim (eq_dim_dec d k).
tauto.
tauto.
