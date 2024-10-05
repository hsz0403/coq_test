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

Lemma cA_cA_1_B_ter : forall (m:fmap)(k j:dim)(x z:dart), inv_hmap m -> k <> j -> cA (B m k x) j z = cA m j z /\ cA_1 (B m k x) j z = cA_1 m j z.
Proof.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
unfold prec_I in |- *.
intros.
elim (eq_dart_dec d z).
tauto.
intros.
apply IHm.
tauto.
tauto.
simpl in |- *.
unfold prec_L in |- *.
intros.
decompose [and] H.
clear H.
elim (eq_dim_dec d k).
elim (eq_dim_dec d j).
intros.
rewrite <- a0 in H0.
tauto.
elim (eq_dart_dec d0 x).
tauto.
simpl in |- *.
elim (eq_dim_dec d j).
tauto.
intros.
apply IHm.
tauto.
tauto.
simpl in |- *.
elim (eq_dim_dec d j).
intros.
assert (k <> j).
rewrite <- a.
intro.
symmetry in H.
tauto.
decompose [and] (IHm k j x d0 H1 H).
split.
elim (eq_dart_dec d0 z).
tauto.
elim (eq_dart_dec d1 z).
elim (eq_dart_dec (cA_1 (B m k x) j d1) z).
elim (eq_dart_dec (cA_1 m j d1) z).
intros.
decompose [and] (IHm k j x d0 H1).
tauto.
intros.
decompose [and] (IHm k j x d1 H1 H).
rewrite H10 in a0.
tauto.
elim (eq_dart_dec (cA_1 m j d1) z).
intros.
decompose [and] (IHm k j x d1 H1 H).
rewrite H10 in b0.
tauto.
intros.
decompose [and] (IHm k j x z H1 H).
tauto.
elim (eq_dart_dec (cA_1 (B m k x) j d1) z).
elim (eq_dart_dec (cA_1 m j d1) z).
tauto.
intros.
decompose [and] (IHm k j x d1 H1 H).
rewrite H10 in a0.
tauto.
elim (eq_dart_dec (cA_1 m j d1) z).
intros.
decompose [and] (IHm k j x d1 H1 H).
rewrite H10 in b0.
tauto.
intros.
decompose [and] (IHm k j x z H1 H).
tauto.
elim (eq_dart_dec d1 z).
tauto.
elim (eq_dart_dec (cA (B m k x) j d0) z).
elim (eq_dart_dec (cA m j d0) z).
decompose [and] (IHm k j x d1 H1 H).
tauto.
intros.
rewrite H6 in a0.
tauto.
elim (eq_dart_dec (cA m j d0) z).
decompose [and] (IHm k j x d1 H1 H).
rewrite H6.
tauto.
decompose [and] (IHm k j x z H1 H).
tauto.
intros.
apply IHm.
tauto.
tauto.
