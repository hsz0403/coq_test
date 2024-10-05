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

Lemma cA_cA_1_B_bis : forall (m:fmap)(k:dim)(x z:dart), inv_hmap m -> ~succ m k x -> cA (B m k x) k z = cA m k z /\ cA_1 (B m k x) k z = cA_1 m k z.
Proof.
induction m.
simpl in |- *.
tauto.
unfold prec_L in |- *.
unfold succ in |- *.
simpl in |- *.
unfold prec_I in |- *.
intros.
elim (eq_dart_dec d z).
tauto.
intro.
apply IHm.
tauto.
unfold succ in |- *.
tauto.
simpl in |- *.
unfold succ in |- *.
unfold prec_L in |- *.
simpl in |- *.
intros.
decompose [and] H.
clear H.
unfold succ in IHm.
generalize H0.
clear H0.
elim (eq_dim_dec d k).
elim (eq_dart_dec d0 x).
intros.
elim H0.
apply exd_not_nil with m.
tauto.
tauto.
intros.
simpl in |- *.
elim (eq_dim_dec d k).
split.
elim (eq_dart_dec d0 z).
tauto.
elim (eq_dart_dec (cA_1 (B m k x) k d1) z).
intros.
elim (eq_dart_dec (cA_1 m k d1) z).
intro.
generalize (IHm k x d0 H1 H0).
tauto.
intro.
decompose [and] (IHm k x d1 H1 H0).
rewrite a1 in H6.
symmetry in H6.
tauto.
intros.
elim (eq_dart_dec (cA_1 m k d1) z).
intro.
decompose [and] (IHm k x d1 H1 H0).
rewrite a1 in H6.
tauto.
intro.
decompose [and] (IHm k x z H1 H0).
tauto.
elim (eq_dart_dec d1 z).
tauto.
elim (eq_dart_dec (cA (B m k x) k d0) z).
intros.
elim (eq_dart_dec (cA m k d0) z).
intro.
decompose [and] (IHm k x d1 H1 H0).
tauto.
intro.
decompose [and] (IHm k x d0 H1 H0).
rewrite H in a1.
tauto.
elim (eq_dart_dec (cA m k d0) z).
intros.
decompose [and] (IHm k x d0 H1 H0).
rewrite H in b0.
tauto.
intros.
decompose [and] (IHm k x z H1 H0).
tauto.
tauto.
intros.
simpl in |- *.
elim (eq_dim_dec d k).
tauto.
intro.
apply IHm.
tauto.
tauto.
