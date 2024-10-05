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

Lemma cA_cA_1 : forall (m:fmap)(k:dim)(z:dart), inv_hmap m -> exd m z -> cA m k (cA_1 m k z) = z.
Proof.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
intros k z.
unfold prec_I in |- *.
elim (eq_dart_dec d z).
elim (eq_dart_dec d z).
tauto.
tauto.
elim (eq_dart_dec d (cA_1 m k z)).
intros.
rewrite a in H.
absurd (exd m (cA_1 m k z)).
tauto.
generalize (exd_cA_cA_1 m k z).
tauto.
intros.
apply IHm.
tauto.
tauto.
intros k z.
simpl in |- *.
unfold prec_L in |- *.
intros.
elim (eq_dim_dec d k).
intros.
elim (eq_dart_dec d1 z).
intro.
rewrite a0 in |- *.
elim (eq_dart_dec d0 d0).
tauto.
tauto.
elim (eq_dart_dec (cA m k d0) z).
elim (eq_dart_dec d0 (cA_1 m k d1)).
intros.
rewrite a0 in a1.
generalize (IHm k d1).
intros.
rewrite a1 in H1.
symmetry in |- *.
tauto.
elim (eq_dart_dec (cA_1 m k d1) (cA_1 m k d1)).
intros.
tauto.
tauto.
elim (eq_dart_dec d0 (cA_1 m k z)).
intros.
rewrite a0 in b.
elim b.
apply IHm.
tauto.
tauto.
elim (eq_dart_dec (cA_1 m k d1) (cA_1 m k z)).
intros.
generalize (IHm k z).
intros.
rewrite <- a0 in H1.
generalize (IHm k d1).
intro.
rewrite H2 in H1.
tauto.
tauto.
tauto.
intros.
apply IHm.
tauto.
tauto.
intro.
apply IHm.
tauto.
tauto.
