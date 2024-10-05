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

Lemma A_cA : forall (m:fmap)(k:dim)(x y:dart), inv_hmap m -> exd m x -> exd m y -> A m k x = y -> cA m k x = y.
Proof.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
unfold prec_I in |- *.
intros k x y.
elim (eq_dart_dec d x).
intuition.
rewrite H4 in H5.
generalize (not_exd_A_nil m k x H3 H5).
rewrite H2 in |- *.
intro.
rewrite H1 in H0.
absurd (exd m nil).
apply not_exd_nil.
tauto.
tauto.
rewrite a in H5.
tauto.
intuition.
rewrite <- H0 in H2.
absurd (exd m d).
tauto.
rewrite <- H2 in |- *.
apply succ_exd_A.
tauto.
unfold succ in |- *.
rewrite H2 in |- *.
tauto.
intros k x y.
simpl in |- *.
unfold prec_L in |- *.
elim (eq_dim_dec d k).
elim (eq_dart_dec d0 x).
tauto.
elim (eq_dart_dec (cA_1 m k d1) x).
intros.
assert (cA m k x = y).
apply IHm.
tauto.
tauto.
tauto.
tauto.
assert (cA m k x = d1).
rewrite <- a in |- *.
apply (cA_cA_1 m k d1).
tauto.
tauto.
rewrite H3 in H4.
rewrite <- H4 in H.
unfold pred in H.
rewrite a0 in H.
assert (x = A_1 m k y).
rewrite <- H2 in |- *.
rewrite A_1_A in |- *.
tauto.
tauto.
unfold succ in |- *.
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
