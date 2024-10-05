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

Lemma A_1_A : forall (m:fmap)(k:dim)(z:dart), inv_hmap m -> succ m k z -> A_1 m k (A m k z) = z.
Proof.
induction m.
simpl in |- *.
simpl in |- *.
unfold succ in |- *.
unfold prec_I in |- *.
simpl in |- *.
tauto.
unfold succ in |- *.
simpl in |- *.
intros.
apply IHm.
tauto.
unfold succ in |- *.
tauto.
unfold succ in |- *.
simpl in |- *.
unfold prec_L in |- *.
intros k z Inv.
elim (eq_dim_dec d k).
elim (eq_dart_dec d0 z).
elim (eq_dart_dec d1 d1).
tauto.
tauto.
elim (eq_dart_dec d1 (A m k z)).
intros.
assert (z = A_1 m k d1).
rewrite a.
symmetry in |- *.
apply IHm.
tauto.
unfold succ in |- *.
tauto.
unfold pred in Inv.
rewrite a0 in Inv.
rewrite <- H0 in Inv.
assert (exd m z).
eapply succ_exd.
tauto.
unfold succ in |- *.
apply H.
assert (z <> nil).
apply exd_not_nil with m.
tauto.
tauto.
tauto.
intros.
apply IHm.
tauto.
unfold succ in |- *.
tauto.
intros.
apply IHm.
tauto.
unfold succ in |- *.
tauto.
