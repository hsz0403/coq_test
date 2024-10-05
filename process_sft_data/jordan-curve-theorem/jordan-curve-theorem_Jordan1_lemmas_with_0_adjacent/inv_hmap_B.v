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

Lemma inv_hmap_B : forall (m:fmap)(k:dim)(z:dart), inv_hmap m -> inv_hmap (B m k z).
Proof.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
intros.
split.
apply IHm.
tauto.
unfold prec_I in |- *.
split.
unfold prec_I in H.
tauto.
unfold prec_I in H.
generalize (exd_B m k z d).
tauto.
simpl in |- *.
unfold prec_L in |- *.
intros.
decompose [and] H.
clear H.
elim (eq_dim_dec d k).
elim (eq_dart_dec d0 z).
tauto.
simpl in |- *.
intros.
split.
apply IHm.
tauto.
unfold prec_L in |- *.
split.
generalize (exd_B m k z d0).
tauto.
split.
generalize (exd_B m k z d1).
tauto.
split.
rewrite <- a.
unfold succ in |- *.
rewrite A_B_bis.
tauto.
tauto.
unfold pred in |- *.
split.
unfold pred in H4.
rewrite <- a.
elim (eq_dart_dec d1 (A m d z)).
intro.
rewrite a0.
rewrite A_1_B.
tauto.
tauto.
intro.
rewrite A_1_B_bis.
tauto.
tauto.
tauto.
rewrite a.
elim (succ_dec m k z).
intro.
rewrite cA_B.
elim (eq_dart_dec z d0).
intro.
elim (eq_dart_dec (top m k z) d0).
intros.
generalize H6.
rewrite cA_eq.
elim (succ_dec m d d0).
tauto.
intros.
rewrite a1.
rewrite <- a.
tauto.
tauto.
intro.
rewrite a1 in a0.
rewrite <- a in a0.
tauto.
elim (eq_dart_dec (top m k z) d0).
intros.
intro.
unfold pred in H4.
rewrite <- H in H4.
rewrite a in H4.
rewrite A_1_A in H4.
absurd (z <> nil).
tauto.
apply exd_not_nil with m.
tauto.
apply succ_exd with k.
tauto.
tauto.
tauto.
tauto.
intros.
rewrite <- a.
tauto.
tauto.
tauto.
intro.
rewrite cA_B_bis.
rewrite <- a.
tauto.
tauto.
tauto.
intro.
simpl in |- *.
split.
apply IHm.
tauto.
unfold prec_L in |- *.
simpl in |- *.
split.
generalize (exd_B m k z d0).
tauto.
split.
generalize (exd_B m k z d1).
tauto.
split.
unfold succ in |- *.
rewrite A_B_ter.
unfold succ in H3.
tauto.
intro.
symmetry in H.
tauto.
split.
unfold pred in |- *.
rewrite A_1_B_ter.
unfold pred in H4.
tauto.
intro.
symmetry in H.
tauto.
rewrite cA_B_ter.
tauto.
tauto.
intro.
symmetry in H.
tauto.
