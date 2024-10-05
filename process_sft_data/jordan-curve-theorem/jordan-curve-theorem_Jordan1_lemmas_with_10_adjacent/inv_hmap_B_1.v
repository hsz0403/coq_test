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

Lemma cA_B : forall (m:fmap)(k:dim)(x z:dart), inv_hmap m -> succ m k x -> cA (B m k x) k z = (if eq_dart_dec x z then bottom m k x else if eq_dart_dec (top m k x) z then A m k x else cA m k z).
Proof.
intros.
generalize (cA_cA_1_B m k x z H H0).
Admitted.

Lemma cA_1_B : forall (m:fmap)(k:dim)(x z:dart), inv_hmap m -> succ m k x -> cA_1 (B m k x) k z = (if eq_dart_dec (A m k x) z then top m k x else if eq_dart_dec (bottom m k x) z then x else cA_1 m k z).
Proof.
intros.
generalize (cA_cA_1_B m k x z H H0).
Admitted.

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
Admitted.

Lemma cA_B_bis : forall (m:fmap)(k:dim)(x z:dart), inv_hmap m -> ~succ m k x -> cA (B m k x) k z = cA m k z.
Proof.
intros.
generalize (cA_cA_1_B_bis m k x z H H0).
Admitted.

Lemma cA_1_B_bis : forall (m:fmap)(k:dim)(x z:dart), inv_hmap m -> ~succ m k x -> cA_1 (B m k x) k z = cA_1 m k z.
Proof.
intros.
generalize (cA_cA_1_B_bis m k x z H H0).
Admitted.

Lemma cA_cA_1_B_ter : forall (m:fmap)(k j:dim)(x z:dart), inv_hmap m -> k <> j -> cA (B m k x) j z = cA m j z /\ cA_1 (B m k x) j z = cA_1 m j z.
Proof.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
unfold prec_I in |- *.
intros.
elim (eq_dart_dec d z).
tauto.
intros.
apply IHm.
tauto.
tauto.
simpl in |- *.
unfold prec_L in |- *.
intros.
decompose [and] H.
clear H.
elim (eq_dim_dec d k).
elim (eq_dim_dec d j).
intros.
rewrite <- a0 in H0.
tauto.
elim (eq_dart_dec d0 x).
tauto.
simpl in |- *.
elim (eq_dim_dec d j).
tauto.
intros.
apply IHm.
tauto.
tauto.
simpl in |- *.
elim (eq_dim_dec d j).
intros.
assert (k <> j).
rewrite <- a.
intro.
symmetry in H.
tauto.
decompose [and] (IHm k j x d0 H1 H).
split.
elim (eq_dart_dec d0 z).
tauto.
elim (eq_dart_dec d1 z).
elim (eq_dart_dec (cA_1 (B m k x) j d1) z).
elim (eq_dart_dec (cA_1 m j d1) z).
intros.
decompose [and] (IHm k j x d0 H1).
tauto.
intros.
decompose [and] (IHm k j x d1 H1 H).
rewrite H10 in a0.
tauto.
elim (eq_dart_dec (cA_1 m j d1) z).
intros.
decompose [and] (IHm k j x d1 H1 H).
rewrite H10 in b0.
tauto.
intros.
decompose [and] (IHm k j x z H1 H).
tauto.
elim (eq_dart_dec (cA_1 (B m k x) j d1) z).
elim (eq_dart_dec (cA_1 m j d1) z).
tauto.
intros.
decompose [and] (IHm k j x d1 H1 H).
rewrite H10 in a0.
tauto.
elim (eq_dart_dec (cA_1 m j d1) z).
intros.
decompose [and] (IHm k j x d1 H1 H).
rewrite H10 in b0.
tauto.
intros.
decompose [and] (IHm k j x z H1 H).
tauto.
elim (eq_dart_dec d1 z).
tauto.
elim (eq_dart_dec (cA (B m k x) j d0) z).
elim (eq_dart_dec (cA m j d0) z).
decompose [and] (IHm k j x d1 H1 H).
tauto.
intros.
rewrite H6 in a0.
tauto.
elim (eq_dart_dec (cA m j d0) z).
decompose [and] (IHm k j x d1 H1 H).
rewrite H6.
tauto.
decompose [and] (IHm k j x z H1 H).
tauto.
intros.
apply IHm.
tauto.
Admitted.

Lemma cA_B_ter : forall (m:fmap)(k j:dim)(x z:dart), inv_hmap m -> k <> j -> cA (B m k x) j z = cA m j z.
Proof.
intros.
generalize (cA_cA_1_B_ter m k j x z).
Admitted.

Lemma cA_1_B_ter : forall (m:fmap)(k j:dim)(x z:dart), inv_hmap m -> k <> j -> cA_1 (B m k x) j z = cA_1 m j z.
Proof.
intros.
generalize (cA_cA_1_B_ter m k j x z).
Admitted.

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
Admitted.

Lemma B_1_eq : forall (m:fmap)(k:dim)(x:dart), inv_hmap m -> B_1 m k x = B m k (A_1 m k x).
Proof.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
intros.
decompose [and] H.
clear H.
rewrite IHm in |- *.
auto.
assumption.
simpl in |- *.
unfold prec_L in |- *.
unfold pred in |- *.
unfold succ in |- *.
intros.
decompose [and] H.
clear H.
elim (eq_dim_dec d k).
elim (eq_dart_dec d1 x).
elim (eq_dart_dec d0 d0).
auto.
tauto.
elim (eq_dart_dec d0 (A_1 m k x)).
intros.
assert (pred m k x).
unfold pred in |- *.
rewrite <- a in |- *.
eapply exd_not_nil.
apply H0.
tauto.
rewrite a in H3.
rewrite a0 in H3.
rewrite A_A_1 in H3.
absurd (x <> nil).
tauto.
assert (exd m x).
apply pred_exd with k.
tauto.
tauto.
eapply exd_not_nil.
apply H0.
tauto.
tauto.
tauto.
intros.
rewrite IHm in |- *.
tauto.
tauto.
intro.
rewrite IHm in |- *.
tauto.
Admitted.

Lemma inv_hmap_B_1 : forall (m:fmap)(k:dim)(x:dart), inv_hmap m -> inv_hmap (B_1 m k x).
Proof.
intros.
rewrite B_1_eq in |- *.
apply inv_hmap_B.
tauto.
tauto.
