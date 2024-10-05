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

Lemma fixpt_cA_cA_1 : forall (m:fmap)(k:dim)(z:dart), inv_hmap m -> exd m z -> ~succ m k z -> ~pred m k z -> cA m k z = z /\ cA_1 m k z = z.
Proof.
induction m.
simpl in |- *.
tauto.
unfold succ in |- *; unfold pred in |- *.
simpl in |- *.
intros k z.
elim (eq_dart_dec d z).
tauto.
intros.
apply IHm.
tauto.
tauto.
unfold succ in |- *; tauto.
unfold pred in |- *; tauto.
intros k z.
unfold succ in |- *; unfold pred in |- *.
simpl in |- *.
unfold prec_L in |- *.
elim (eq_dim_dec d k).
elim (eq_dart_dec d0 z).
elim (eq_dart_dec d1 z).
intros.
rewrite a0; rewrite a.
tauto.
intros.
absurd (d1 <> nil).
tauto.
intro.
rewrite H3 in H.
absurd (exd m nil).
apply not_exd_nil.
tauto.
tauto.
elim (eq_dart_dec d1 z).
intros.
absurd (d0 <> nil).
tauto.
intro.
rewrite H3 in H.
absurd (exd m nil).
apply not_exd_nil.
tauto.
tauto.
intros.
elim (eq_dart_dec (cA_1 m k d1) z).
intro.
elim (eq_dart_dec (cA m k d0) z).
intros.
rewrite a0; rewrite a1.
tauto.
intros.
split.
assert (z = d1).
assert (cA_1 m k z = z).
generalize (IHm k z).
tauto.
symmetry in H3.
rewrite H3 in a0.
assert (inj_dart (exd m) (cA_1 m k)).
apply inj_cA_1.
tauto.
unfold inj_dart in H4.
generalize (H4 z d1).
intros.
apply H5.
tauto.
tauto.
symmetry in |- *; tauto.
symmetry in H3.
tauto.
generalize (IHm k z).
unfold pred in |- *; unfold succ in |- *.
tauto.
elim (eq_dart_dec (cA m k d0) z).
intros.
generalize (IHm k z).
unfold pred in |- *; unfold succ in |- *.
intros.
assert (z = d0).
assert (cA m k z = z).
tauto.
rewrite <- H4 in a0.
assert (inj_dart (exd m) (cA m k)).
apply inj_cA.
tauto.
unfold inj_dart in H5.
generalize (H5 z d0).
intros.
symmetry in a0.
tauto.
symmetry in H4.
tauto.
intros.
generalize (IHm k z).
tauto.
intros.
generalize (IHm k z).
tauto.
