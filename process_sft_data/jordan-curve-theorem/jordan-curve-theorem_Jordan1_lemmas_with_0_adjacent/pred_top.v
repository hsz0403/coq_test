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

Lemma pred_top :forall (m:fmap)(k:dim)(x:dart), inv_hmap m -> pred m k x -> top m k x <> A_1 m k x.
Proof.
induction m.
simpl in |- *.
unfold pred in |- *.
simpl in |- *.
tauto.
simpl in |- *.
unfold pred in |- *.
unfold prec_I in |- *.
simpl in |- *.
intros.
elim (eq_dart_dec d x).
intro.
rewrite a in H.
elim H0.
apply not_exd_A_1_nil.
tauto.
tauto.
intro.
apply IHm.
tauto.
unfold pred in |- *.
tauto.
unfold pred in |- *.
simpl in |- *.
unfold prec_L in |- *.
unfold succ in |- *.
unfold pred in |- *.
intros.
generalize H0.
clear H0.
elim (eq_dim_dec d k).
intro.
rewrite a in |- *.
elim (eq_dart_dec d1 x).
intros.
rewrite a0 in |- *.
elim (eq_dart_dec d0 (top m k x)).
intro.
rewrite a1 in H.
rewrite a0 in H.
rewrite a in H.
generalize (cA_1_eq m k x).
elim (pred_dec m k x).
unfold pred in |- *.
tauto.
unfold pred in |- *.
intros.
rewrite <- a1 in H1.
rewrite <- a1 in H.
rewrite <- H1 in H.
rewrite cA_cA_1 in H.
tauto.
tauto.
tauto.
tauto.
intro.
intro.
symmetry in H1.
tauto.
elim (eq_dart_dec d0 (top m k x)).
intros.
rewrite <- top_A_1 in a0.
intro.
rewrite <- H1 in a0.
rewrite top_top in a0.
rewrite <- a0 in H1.
assert (x = A m k d0).
rewrite H1 in |- *.
rewrite A_A_1 in |- *.
tauto.
tauto.
unfold pred in |- *.
tauto.
rewrite a in H.
rewrite <- H2 in H.
absurd (x = nil).
assert (exd m x).
eapply pred_exd.
tauto.
unfold pred in |- *.
apply H0.
apply exd_not_nil with m.
tauto.
tauto.
elim (eq_nat_dec x nil).
tauto.
tauto.
tauto.
tauto.
unfold pred in |- *.
tauto.
intros.
apply IHm.
tauto.
unfold pred in |- *.
tauto.
intros.
apply IHm.
tauto.
unfold pred in |- *.
tauto.
