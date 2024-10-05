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

Lemma top_bottom : forall (m:fmap)(k:dim)(z:dart), inv_hmap m -> exd m z -> ~succ m k z -> top m k (bottom m k z) = z.
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
tauto.
simpl in |- *.
unfold prec_L in |- *.
unfold succ in |- *.
simpl in |- *.
intros.
generalize H1.
elim (eq_dim_dec d k).
clear H1.
elim (eq_dart_dec d0 z).
intros.
absurd (d1 <> nil).
tauto.
apply exd_not_nil with m.
tauto.
tauto.
elim (eq_dart_dec d1 (bottom m d z)).
elim (eq_dart_dec d0 (top m d (bottom m d d0))).
intros.
rewrite a0.
apply IHm.
tauto.
tauto.
unfold succ in |- *.
rewrite a1.
tauto.
intros.
rewrite IHm in b.
tauto.
tauto.
tauto.
tauto.
elim (eq_dart_dec d0 (top m d (bottom m d z))).
intros.
rewrite IHm in a.
tauto.
tauto.
tauto.
unfold succ in |- *.
rewrite a0.
tauto.
intros.
apply IHm.
tauto.
tauto.
unfold succ in |- *.
rewrite a.
tauto.
intros.
apply IHm.
tauto.
tauto.
unfold succ.
tauto.
