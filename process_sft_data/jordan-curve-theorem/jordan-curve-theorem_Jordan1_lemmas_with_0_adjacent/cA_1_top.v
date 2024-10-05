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

Lemma cA_1_top : forall (m:fmap)(k:dim)(z:dart), inv_hmap m -> exd m z -> ~pred m k z -> cA_1 m k z = top m k z.
Proof.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
unfold prec_I in |- *.
unfold pred in |- *.
simpl in |- *.
intros.
elim (eq_dart_dec d z).
tauto.
intro.
apply IHm; tauto.
unfold pred in |- *.
simpl in |- *.
unfold prec_L in |- *.
intros k z Inv E.
decompose [and] Inv.
elim (eq_dim_dec d k).
elim (eq_dart_dec d1 z).
intros.
absurd (d0 <> nil).
tauto.
apply exd_not_nil with m.
tauto.
tauto.
elim (eq_dart_dec (cA m k d0) z).
intros.
clear Inv.
elim (eq_dart_dec d0 (top m d z)).
intro.
rewrite a0 in |- *.
apply IHm.
tauto.
tauto.
rewrite a0 in H3.
tauto.
intro.
rewrite <- IHm in b0.
rewrite <- a in b0.
rewrite a0 in b0.
rewrite cA_1_cA in b0.
tauto.
tauto.
tauto.
tauto.
tauto.
unfold pred in |- *.
rewrite a0 in |- *.
tauto.
intros.
elim (eq_dart_dec d0 (top m d z)).
intro.
clear Inv.
rewrite a in a0.
rewrite <- IHm in a0.
rewrite a in |- *.
rewrite a0 in b.
rewrite cA_cA_1 in b.
tauto.
tauto.
tauto.
tauto.
tauto.
unfold pred in |- *.
tauto.
intro.
rewrite a in |- *.
apply IHm.
tauto.
tauto.
unfold pred in |- *.
tauto.
intros.
apply IHm.
tauto.
tauto.
unfold pred in |- *.
tauto.
