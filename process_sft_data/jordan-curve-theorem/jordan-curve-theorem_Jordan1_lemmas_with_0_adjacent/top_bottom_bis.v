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

Lemma top_bottom_bis:forall(m:fmap)(k:dim)(z:dart), inv_hmap m -> exd m z -> top m k (bottom m k z) = top m k z.
Proof.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
unfold prec_I in |- *.
unfold succ in |- *.
simpl in |- *.
intros.
elim (eq_dart_dec d z).
elim (eq_dart_dec d z).
tauto.
tauto.
elim (eq_dart_dec d (bottom m k z)).
intros.
rewrite a in H.
generalize (exd_bottom m k z).
tauto.
intros.
apply IHm.
tauto.
tauto.
unfold succ in |- *.
simpl in |- *.
unfold prec_L in |- *.
unfold succ in |- *.
simpl in |- *.
intros.
elim (eq_dim_dec d k).
elim (eq_dart_dec d1 (bottom m d z)).
elim (eq_dart_dec d0 (top m d (bottom m d d0))).
intros.
elim (eq_dart_dec d0 (top m d z)).
intro.
tauto.
intro.
rewrite a0.
rewrite IHm.
tauto.
tauto.
tauto.
elim (eq_dart_dec d0 (top m d z)).
intros.
rewrite IHm in b.
rewrite nosucc_top in b.
tauto.
tauto; tauto.
tauto.
unfold succ in |- *.
tauto.
tauto.
tauto.
intros.
rewrite IHm in b0.
rewrite nosucc_top in b0.
tauto.
tauto.
tauto.
unfold succ in |- *.
tauto.
tauto.
tauto.
elim (eq_dart_dec d0 (top m d (bottom m d z))).
intros.
elim (eq_dart_dec d0 (top m d z)).
tauto.
intros.
rewrite IHm in a.
tauto.
tauto.
tauto.
intros.
elim (eq_dart_dec d0 (top m d z)).
intros.
rewrite IHm in b.
tauto.
tauto.
tauto.
intro.
rewrite IHm.
tauto.
tauto.
tauto.
intro.
rewrite IHm.
tauto.
tauto.
tauto.
