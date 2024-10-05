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

Lemma A_1_cA_1 : forall (m:fmap)(k:dim)(x y:dart), inv_hmap m -> exd m x -> exd m y -> A_1 m k x = y -> cA_1 m k x = y.
Proof.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
unfold prec_I in |- *.
intros k x y.
elim (eq_dart_dec d x).
intuition.
rewrite <- H4 in H2.
assert (A_1 m k d = nil).
apply not_exd_A_1_nil.
tauto.
tauto.
rewrite H1 in H2.
rewrite <- H2 in H0.
absurd (exd m nil).
apply not_exd_nil.
tauto.
tauto.
rewrite a in H5.
tauto.
intuition.
rewrite <- H0 in H2.
elim H5.
rewrite <- H2 in |- *.
apply pred_exd_A_1.
tauto.
unfold pred in |- *.
rewrite H2 in |- *.
tauto.
intros k x y.
simpl in |- *.
unfold prec_L in |- *.
elim (eq_dim_dec d k).
elim (eq_dart_dec d1 x).
tauto.
elim (eq_dart_dec (cA m k d0) x).
intros.
assert (cA_1 m k x = y).
apply IHm.
tauto.
tauto.
tauto.
tauto.
assert (cA_1 m k x = d0).
rewrite <- a in |- *.
apply (cA_1_cA m k d0).
tauto.
tauto.
rewrite H3 in H4.
rewrite <- H4 in H.
unfold succ in H.
rewrite a0 in H.
assert (x = A m k y).
rewrite <- H2 in |- *.
rewrite A_A_1 in |- *.
tauto.
tauto.
unfold pred in |- *.
rewrite H2 in |- *.
apply (exd_not_nil m y).
tauto.
tauto.
rewrite <- H5 in H.
assert (x <> nil).
apply (exd_not_nil m x).
tauto.
tauto.
tauto.
intros.
apply IHm.
tauto.
tauto.
tauto.
tauto.
intros.
apply IHm.
tauto.
tauto.
tauto.
tauto.
