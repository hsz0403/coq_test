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

Lemma cA_cA_1_B : forall (m:fmap)(k:dim)(x z:dart), inv_hmap m -> succ m k x -> cA (B m k x) k z = (if eq_dart_dec x z then bottom m k x else if eq_dart_dec (top m k x) z then A m k x else cA m k z) /\ cA_1 (B m k x) k z = (if eq_dart_dec (A m k x) z then top m k x else if eq_dart_dec (bottom m k x) z then x else cA_1 m k z).
Proof.
induction m.
unfold succ in |- *.
simpl in |- *.
tauto.
simpl in |- *.
unfold prec_I in |- *.
unfold succ in |- *.
simpl in |- *.
intros.
elim (eq_dart_dec d x).
intro.
rewrite a in H.
absurd (exd m x).
tauto.
apply succ_exd with k.
tauto.
unfold succ in |- *.
tauto.
intro.
elim (eq_dart_dec d z).
intro.
elim (eq_dart_dec x z).
intro.
rewrite a0 in b.
tauto.
intro.
split.
elim (eq_dart_dec (top m k x) z).
intro.
rewrite a in H.
rewrite <- a0 in H.
absurd (exd m (top m k x)).
tauto.
apply exd_top.
tauto.
apply succ_exd with k.
tauto.
unfold succ in |- *.
tauto.
tauto.
elim (eq_dart_dec (A m k x) z).
intro.
rewrite <- a in a0.
rewrite <- a0 in H.
absurd (exd m (A m k x)).
tauto.
apply succ_exd_A.
tauto.
unfold succ in |- *.
tauto.
intro.
elim (eq_dart_dec (bottom m k x) z).
intro.
rewrite <- a in a0.
rewrite <- a0 in H.
absurd (exd m (bottom m k x)).
tauto.
apply exd_bottom.
tauto.
apply succ_exd with k.
tauto.
unfold succ in |- *.
tauto.
tauto.
intro.
apply IHm.
tauto.
unfold succ in |- *.
tauto.
unfold succ in |- *.
simpl in |- *.
unfold prec_L in |- *.
intros.
decompose [and] H.
clear H.
generalize H0.
clear H0.
rename d into i.
elim (eq_dim_dec i k).
intro.
rewrite <- a.
elim (eq_dart_dec d0 x).
intro.
rewrite <- a0.
intro.
elim (eq_dart_dec d1 (bottom m i d0)).
intro.
rewrite a1 in H7.
generalize H7.
clear H7.
rewrite cA_eq.
elim (succ_dec m i d0).
tauto.
tauto.
tauto.
intro.
elim (eq_dart_dec d0 (top m i d0)).
intro.
split.
elim (eq_dart_dec d0 z).
intro.
rewrite <- a2.
rewrite cA_eq.
elim (succ_dec m i d0).
tauto.
tauto.
tauto.
intro.
elim (eq_dart_dec (top m i d1) z).
intro.
assert (~ succ m i z).
rewrite <- a2.
apply not_succ_top.
tauto.
rewrite cA_eq.
elim (succ_dec m i z).
tauto.
intro.
rewrite <- a2.
apply bottom_top.
tauto.
tauto.
tauto.
tauto.
intro.
elim (eq_dart_dec (cA_1 m i d1) z).
rewrite cA_1_eq.
elim (pred_dec m i d1).
tauto.
tauto.
tauto.
tauto.
elim (eq_dart_dec d1 z).
intro.
rewrite <- a2.
rewrite cA_1_eq.
elim (pred_dec m i d1).
tauto.
tauto.
tauto.
intro.
elim (eq_dart_dec (bottom m i d0) z).
intro.
assert (~ pred m i z).
rewrite <- a2.
apply not_pred_bottom.
tauto.
rewrite cA_1_eq.
elim (pred_dec m i z).
tauto.
intro.
rewrite <- a2.
apply top_bottom.
tauto.
tauto.
tauto.
tauto.
intro.
elim (eq_dart_dec (cA m i d0) z).
rewrite cA_eq.
elim (succ_dec m i d0).
tauto.
tauto.
tauto.
tauto.
intro.
elim b0.
rewrite nosucc_top.
tauto.
tauto.
tauto.
tauto.
intros.
fold (succ m i x) in H0.
elim (eq_dart_dec d0 (top m i x)).
intro.
elim (eq_dart_dec d1 (bottom m i x)).
intro.
rewrite a1 in H7.
rewrite a0 in H7.
elim H7.
apply cA_top.
tauto.
apply succ_exd with i.
tauto.
unfold succ in |- *.
unfold succ in H0.
tauto.
intro.
split.
simpl in |- *.
elim (eq_dim_dec i i).
intro.
clear a1.
elim (eq_dart_dec d0 z).
intro.
elim (eq_dart_dec x z).
intro.
rewrite <- a2 in a1.
tauto.
elim (eq_dart_dec (top m i d1) z).
intros.
rewrite <- a2 in a1.
rewrite a1 in a0.
elim b0.
symmetry in |- *.
apply top_top_bottom.
tauto.
apply succ_exd with i.
tauto.
tauto.
tauto.
tauto.
symmetry in |- *.
tauto.
tauto.
intro.
elim (eq_dart_dec (cA_1 (B m i x) i d1) z).
intro.
generalize (IHm i x d0 H1 H0).
intros.
elim H.
clear H.
intros.
generalize (IHm i x d1 H1 H0).
intros.
elim H8.
clear H8.
intros.
generalize H.
clear H.
elim (eq_dart_dec x z).
intro.
elim (eq_dart_dec x d0).
tauto.
intro.
elim (eq_dart_dec (top m i x) d0).
intros.
rewrite <- a2 in a1.
generalize a1.
clear a1.
rewrite H9.
clear H9.
elim (eq_dart_dec (A m i x) d1).
intros.
rewrite a4 in a0.
tauto.
intro.
elim (eq_dart_dec (bottom m i x) d1).
intros.
symmetry in a1.
tauto.
intros.
rewrite cA_1_eq in a1.
generalize a1.
clear a1.
elim (pred_dec m i d1).
tauto.
intros.
rewrite <- a1 in b4.
rewrite bottom_top in b4.
tauto.
tauto.
tauto.
tauto.
tauto.
intros.
rewrite H.
rewrite cA_eq.
elim (succ_dec m i d0).
tauto.
intro.
rewrite a0.
apply bottom_top_bis.
tauto.
apply succ_exd with i.
tauto.
tauto.
tauto.
intro.
elim (eq_dart_dec x d0).
intro.
symmetry in a2.
tauto.
intro.
elim (eq_dart_dec (top m i x) d0).
intros.
elim (eq_dart_dec (top m i d1) z).
intros.
tauto.
intro.
elim (eq_dart_dec (cA_1 m i d1) z).
intro.
rewrite cA_1_eq in a3.
generalize a3.
elim (pred_dec m i d1).
tauto.
tauto.
tauto.
intro.
rewrite H.
generalize H9.
clear H9.
elim (eq_dart_dec (A m i x) d1).
intros.
rewrite <- a3 in H5.
unfold pred in H5.
rewrite A_1_A in H5.
absurd (x <> nil).
tauto.
apply exd_not_nil with m.
tauto.
apply succ_exd with i.
tauto.
tauto.
tauto.
tauto.
intro.
elim (eq_dart_dec (bottom m i x) d1).
intros.
symmetry in a3.
tauto.
intros.
rewrite a1 in H9.
symmetry in H9.
tauto.
symmetry in a0.
tauto.
intro.
generalize (IHm i x z H1 H0).
intros.
elim H.
clear H.
intros.
generalize (IHm i x d1 H1 H0).
intros.
elim H8.
clear H8.
intros.
generalize H.
clear H.
elim (eq_dart_dec x z).
tauto.
elim (eq_dart_dec (top m i x) z).
intros.
rewrite a1 in a0.
tauto.
intros.
elim (eq_dart_dec (top m i d1) z).
intros.
generalize H9.
clear H9.
elim (eq_dart_dec (A m i x) d1).
intro.
rewrite <- a2 in a1.
rewrite top_A in a1.
tauto.
tauto.
tauto.
elim (eq_dart_dec (bottom m i x) d1).
intros.
symmetry in a2.
tauto.
intros.
rewrite H9 in b2.
generalize b2.
rewrite cA_1_eq.
elim (pred_dec m i d1).
tauto.
tauto.
tauto.
elim (eq_dart_dec (cA_1 m i d1) z).
intros.
rewrite cA_1_eq in a1.
generalize a1.
elim (pred_dec m i d1).
tauto.
tauto.
tauto.
intros.
tauto.
tauto.
simpl in |- *.
elim (eq_dim_dec i i).
intro.
elim (eq_dart_dec d1 z).
intro.
rewrite <- a2.
elim (eq_dart_dec (A m i x) d1).
intros.
assert (d0 = top m i d1).
rewrite <- a3.
rewrite top_A.
tauto.
tauto.
tauto.
tauto.
elim (eq_dart_dec (bottom m i x) d1).
intros.
symmetry in a3.
tauto.
tauto.
intro.
elim (eq_dart_dec (cA (B m i x) i d0) z).
intro.
generalize (IHm i x d0 H1 H0).
intro.
elim H.
clear H.
intros.
generalize (IHm i x d1 H1 H0).
intro.
elim H8.
clear H8.
intros.
generalize H9.
clear H9.
generalize H.
clear H.
elim (eq_dart_dec x d0).
intro.
symmetry in a3.
tauto.
elim (eq_dart_dec (top m i x) d0).
intros.
generalize H9.
clear H9.
clear b2 a3.
elim (eq_dart_dec (A m i x) d1).
intros.
rewrite <- a3 in H5.
unfold pred in H5.
rewrite A_1_A in H5.
absurd (x <> nil).
tauto.
apply exd_not_nil with m.
tauto.
apply succ_exd with i.
tauto.
tauto.
tauto.
tauto.
intro.
elim (eq_dart_dec (bottom m i x) d1).
intro.
symmetry in |- *.
symmetry in a3.
tauto.
intros.
elim (eq_dart_dec (A m i x) z).
intro.
rewrite H9.
rewrite cA_1_eq.
elim (pred_dec m i d1).
tauto.
tauto.
tauto.
intro.
rewrite H in a2.
tauto.
intros.
generalize H9.
clear H9.
elim (eq_dart_dec (A m i x) d1).
intros.
rewrite <- a3 in H5.
unfold pred in H5.
rewrite A_1_A in H5.
absurd (x <> nil).
tauto.
apply exd_not_nil with m.
tauto.
apply succ_exd with i.
tauto.
tauto.
tauto.
tauto.
intro.
elim (eq_dart_dec (bottom m i x) d1).
intro.
symmetry in a3.
tauto.
intros.
elim (eq_dart_dec (A m i x) z).
intro.
rewrite H9.
rewrite cA_1_eq.
elim (pred_dec m i d1).
tauto.
tauto.
tauto.
intro.
symmetry in a0.
tauto.
intro.
generalize (IHm i x d0 H1 H0).
intro.
elim H.
clear H.
intros.
generalize (IHm i x z H1 H0).
intro.
elim H8.
clear H8.
intros.
generalize H9.
clear H9.
elim (eq_dart_dec (A m i x) z).
intros.
rewrite <- a0 in H9.
rewrite H in b2.
generalize b2.
clear b2.
elim (eq_dart_dec x d0).
intro.
symmetry in a3.
tauto.
elim (eq_dart_dec (top m i x) d0).
intros.
tauto.
intro.
symmetry in a0.
tauto.
intro.
elim (eq_dart_dec (bottom m i x) z).
tauto.
intros.
elim (eq_dart_dec (cA m i d0) z).
intro.
generalize a2.
rewrite cA_eq.
elim (succ_dec m i d0).
tauto.
intros.
rewrite a0 in a3.
rewrite bottom_top_bis in a3.
tauto.
tauto.
apply succ_exd with i.
tauto.
tauto.
tauto.
tauto.
tauto.
intro.
simpl in |- *.
elim (eq_dim_dec i i).
intro.
split.
elim (eq_dart_dec d0 z).
intro.
rewrite <- a1.
elim (eq_dart_dec x d0).
intro.
symmetry in a2.
tauto.
intro.
elim (eq_dart_dec (top m i x) d0).
intro.
symmetry in a2.
tauto.
tauto.
intro.
elim (eq_dart_dec x z).
intro.
rewrite <- a1.
generalize (IHm i x d1 H1 H0).
intro.
elim H.
clear H.
intros.
elim (eq_dart_dec (cA_1 (B m i x) i d1) x).
intros.
generalize (IHm i x d0 H1 H0).
intro.
elim H8.
clear H8.
intros.
rewrite H8.
elim (eq_dart_dec x d0).
intro.
symmetry in a3.
tauto.
intro.
elim (eq_dart_dec (top m i x) d0).
intro.
symmetry in a3.
tauto.
intro.
clear H8.
elim (eq_dart_dec d1 (bottom m i x)).
intro.
rewrite cA_eq.
elim (succ_dec m i d0).
tauto.
tauto.
tauto.
intros.
rewrite H6 in a2.
generalize a2.
elim (eq_dart_dec (A m i x) d1).
intro.
rewrite <- a3 in H5.
unfold pred in H5.
rewrite A_1_A in H5.
absurd (x <> nil).
tauto.
apply exd_not_nil with m.
tauto.
apply succ_exd with i.
tauto.
tauto.
tauto.
tauto.
intro.
elim (eq_dart_dec (bottom m i x) d1).
intro.
symmetry in a3.
tauto.
intros.
rewrite cA_1_eq in a3.
generalize a3.
elim (pred_dec m i d1).
tauto.
intros.
rewrite <- a4 in H0.
absurd (succ m i (top m i d1)).
apply not_succ_top.
tauto.
tauto.
tauto.
rewrite H6.
clear H6.
elim (eq_dart_dec (A m i x) d1).
intro.
rewrite <- a2 in H5.
unfold pred in H5.
rewrite A_1_A in H5.
absurd (x <> nil).
tauto.
apply exd_not_nil with m.
tauto.
apply succ_exd with i.
tauto.
tauto.
tauto.
tauto.
intro.
elim (eq_dart_dec (bottom m i x) d1).
intros.
tauto.
elim (eq_dart_dec d1 (bottom m i x)).
intros.
symmetry in a2.
tauto.
intros.
generalize (IHm i x x H1 H0).
intro.
elim H6.
clear H6.
intros.
rewrite H6.
clear H6.
elim (eq_dart_dec x x).
tauto.
tauto.
intro.
generalize (IHm i x z H1 H0).
intro.
elim H.
clear H.
intros.
generalize (IHm i x d1 H1 H0).
intro.
elim H8.
clear H8.
intros.
generalize H9.
elim (eq_dart_dec (A m i x) d1).
intro.
rewrite <- a1 in H5.
unfold pred in H5.
rewrite A_1_A in H5.
absurd (x <> nil).
tauto.
apply exd_not_nil with m.
tauto.
apply succ_exd with i.
tauto.
tauto.
tauto.
tauto.
elim (eq_dart_dec (bottom m i x) d1).
intros.
rewrite H10.
elim (eq_dart_dec x z).
tauto.
intro.
rewrite H.
clear H.
elim (eq_dart_dec x z).
tauto.
elim (eq_dart_dec (top m i x) z).
tauto.
elim (eq_dart_dec (cA_1 m i d1) z).
intros.
rewrite cA_1_eq in a2.
generalize a2; clear a2.
elim (pred_dec m i d1).
tauto.
intros.
rewrite cA_eq.
elim (succ_dec m i z).
intro.
rewrite <- a2 in a3.
absurd (succ m i (top m i d1)).
apply not_succ_top.
tauto.
tauto.
rewrite cA_eq.
elim (succ_dec m i d0).
tauto.
intros.
rewrite <- a1 in a2.
rewrite top_bottom_bis in a2.
tauto.
tauto.
apply succ_exd with i.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
intro.
intros.
elim (eq_dart_dec (cA_1 (B m i x) i d1) z).
intros.
generalize (IHm i x d0 H1 H0).
intro.
elim H11.
clear H11.
intros.
rewrite H11.
clear H11.
elim (eq_dart_dec x d0).
intro.
symmetry in a2.
tauto.
elim (eq_dart_dec (top m i x) d0).
intro.
symmetry in a2.
tauto.
intros.
elim (eq_dart_dec (top m i x) z).
intro.
rewrite H10 in a1.
generalize a1.
rewrite cA_1_eq.
elim (pred_dec m i d1).
tauto.
intros.
rewrite <- a3 in a2.
assert (bottom m i x = d1).
apply top_top_bottom.
tauto.
apply succ_exd with i.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
elim (eq_dart_dec (cA_1 m i d1) z).
tauto.
intros.
rewrite H10 in a1.
tauto.
intro.
rewrite H.
clear H.
elim (eq_dart_dec x z).
tauto.
elim (eq_dart_dec (top m i x) z).
intros.
tauto.
elim (eq_dart_dec (cA_1 m i d1) z).
rewrite H10 in b5.
tauto.
tauto.
generalize (IHm i x d0 H1 H0).
intro.
elim H.
clear H.
intros.
generalize H.
clear H.
elim (eq_dart_dec x d0).
intro.
symmetry in a1.
tauto.
elim (eq_dart_dec (top m i x) d0).
intro.
symmetry in a1.
tauto.
intros.
elim (eq_dart_dec d1 z).
intro.
rewrite <- a1.
elim (eq_dart_dec (A m i x) d1).
intro.
rewrite <- a2 in H5.
unfold pred in H5.
rewrite A_1_A in H5.
absurd (x <> nil).
tauto.
apply exd_not_nil with m.
tauto.
apply succ_exd with i.
tauto.
tauto.
tauto.
tauto.
elim (eq_dart_dec d1 (bottom m i x)).
intros.
elim (eq_dart_dec (bottom m i d0) d1).
intros.
rewrite <- a3 in a2.
symmetry in a2.
assert (top m i x = d0).
apply bottom_bottom_top.
tauto.
apply succ_exd with i.
tauto.
tauto.
tauto.
tauto.
tauto.
symmetry in H8.
tauto.
tauto.
elim (eq_dart_dec (bottom m i x) d1).
intro.
symmetry in a2.
tauto.
tauto.
intro.
elim (eq_dart_dec (cA (B m i x) i d0) z).
intro.
generalize (IHm i x d1 H1 H0).
intro.
elim H8.
clear H8.
intros.
rewrite H9.
clear H9.
elim (eq_dart_dec (A m i x) d1).
intro.
rewrite <- a2 in H5.
unfold pred in H5.
rewrite A_1_A in H5.
absurd (x <> nil).
tauto.
apply exd_not_nil with m.
tauto.
apply succ_exd with i.
tauto.
tauto.
tauto.
tauto.
elim (eq_dart_dec (bottom m i x) d1).
intros.
assert (cA m i d0 = bottom m i d0).
rewrite cA_eq.
elim (succ_dec m i d0).
tauto.
tauto.
tauto.
elim (eq_dart_dec (A m i x) z).
intro.
assert (pred m i z).
unfold pred in |- *.
rewrite <- a3.
rewrite A_1_A.
apply exd_not_nil with m.
tauto.
apply succ_exd with i.
tauto.
tauto.
tauto.
tauto.
rewrite <- a1 in H10.
rewrite H in H10.
rewrite H9 in H10.
absurd (pred m i (bottom m i d0)).
apply not_pred_bottom.
tauto.
tauto.
intro.
elim (eq_dart_dec d1 (bottom m i x)).
intro.
elim (eq_dart_dec (bottom m i d0) z).
tauto.
elim (eq_dart_dec (cA m i d0) z).
intros.
rewrite H9 in a4.
tauto.
intros.
rewrite H in a1.
tauto.
intro.
elim (eq_dart_dec (bottom m i x) z).
tauto.
elim (eq_dart_dec (cA m i d0) z).
intros.
rewrite cA_1_eq.
elim (pred_dec m i d1).
tauto.
intro.
symmetry in a2.
tauto.
tauto.
rewrite H in a1.
tauto.
intros.
elim (eq_dart_dec (A m i x) z).
intro.
rewrite cA_1_eq.
rewrite H in a1.
generalize a1.
rewrite cA_eq.
elim (succ_dec m i d0).
tauto.
intros.
assert (pred m i z).
rewrite <- a2.
unfold pred in |- *.
rewrite A_1_A.
apply exd_not_nil with m.
tauto.
apply succ_exd with i.
tauto.
tauto.
tauto.
tauto.
rewrite <- a3 in H9.
absurd (pred m i (bottom m i d0)).
apply not_pred_bottom.
tauto.
tauto.
tauto.
tauto.
intro.
elim (eq_dart_dec d1 (bottom m i x)).
intro.
symmetry in a2.
tauto.
elim (eq_dart_dec (bottom m i x) z).
intros.
rewrite H in a1.
generalize a1.
rewrite cA_eq.
elim (succ_dec m i d0).
intros.
tauto.
intros.
rewrite <- a3 in a2.
elim b1.
apply bottom_bottom_top.
tauto.
apply succ_exd with i.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
elim (eq_dart_dec (cA m i d0) z).
tauto.
intros.
rewrite H in a1.
tauto.
intro.
generalize (IHm i x z H1 H0).
intro.
elim H8.
clear H8.
intros.
rewrite H9.
clear H9.
elim (eq_dart_dec (A m i x) z).
tauto.
elim (eq_dart_dec (bottom m i x) z).
intros.
elim (eq_dart_dec d1 (bottom m i x)).
intro.
rewrite a1 in a2.
tauto.
elim (eq_dart_dec (bottom m i x) z).
tauto.
tauto.
elim (eq_dart_dec d1 (bottom m i x)).
intros.
elim (eq_dart_dec (bottom m i d0) z).
intros.
rewrite H in b4.
generalize b4.
rewrite cA_eq.
elim (succ_dec m i d0).
tauto.
tauto.
tauto.
elim (eq_dart_dec (cA m i d0) z).
rewrite H in b4.
tauto.
tauto.
intros.
elim (eq_dart_dec (bottom m i x) z).
intro.
tauto.
elim (eq_dart_dec (cA m i d0) z).
intros.
rewrite H in b4.
tauto.
tauto.
tauto.
simpl in |- *.
elim (eq_dim_dec i k).
tauto.
intros.
fold succ in H0.
fold (succ m k x) in H0.
apply IHm.
tauto.
tauto.
