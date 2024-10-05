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

Lemma cA_top:forall (m:fmap)(k:dim)(z:dart), inv_hmap m -> exd m z -> cA m k (top m k z) = bottom m k z.
Proof.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
unfold prec_I in |- *.
intros.
elim (eq_dart_dec d z).
elim (eq_dart_dec d z).
tauto.
tauto.
intro.
elim (eq_dart_dec d (top m k z)).
intro.
rewrite a in H.
absurd (exd m (top m k z)).
tauto.
apply exd_top.
tauto.
tauto.
intro.
apply IHm.
tauto.
tauto.
simpl in |- *.
unfold prec_L in |- *.
intros.
elim (eq_dim_dec d k).
elim (eq_dart_dec d0 (top m d z)).
elim (eq_dart_dec d0 (top m d d1)).
intros.
rewrite a in H.
rewrite IHm in H.
rewrite nopred_bottom in H.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
elim (eq_dart_dec (cA_1 m k d1) (top m d d1)).
elim (eq_dart_dec d1 (bottom m d z)).
intros.
rewrite <- a2.
apply cA_bottom.
tauto.
tauto.
tauto.
intros.
rewrite a0.
rewrite a1.
apply IHm.
tauto.
tauto.
intros.
elim b.
rewrite <- a0.
apply cA_1_top.
tauto.
tauto.
tauto.
elim (eq_dart_dec d0 (top m d z)).
tauto.
intros.
elim (eq_dart_dec (cA_1 m k d1) (top m d z)).
intros.
elim (eq_dart_dec d1 (bottom m d z)).
intro.
rewrite <- a.
apply cA_bottom.
tauto.
tauto.
tauto.
intro.
rewrite <- a in a0.
assert (d1 = cA m d (top m d z)).
rewrite <- a0.
rewrite cA_cA_1.
tauto.
tauto.
tauto.
rewrite IHm in H1.
tauto.
tauto.
tauto.
intros.
elim (eq_dart_dec d1 (bottom m d z)).
intros.
rewrite <- IHm in a0.
assert (cA_1 m k d1 = top m d z).
rewrite a0.
rewrite <- a.
rewrite cA_1_cA.
tauto.
tauto.
apply exd_top.
tauto.
tauto.
tauto.
tauto.
tauto.
intro.
rewrite a.
apply IHm.
tauto.
tauto.
intro.
apply IHm.
tauto.
tauto.
