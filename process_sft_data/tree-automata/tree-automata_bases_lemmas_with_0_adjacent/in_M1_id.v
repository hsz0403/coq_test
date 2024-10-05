Require Import Bool.
Require Import Arith.
Require Import ZArith.
Require Import NArith.
Require Import Ndec.
From IntMap Require Import Allmaps.
Require Import EqNat.
Require Export Max.

Lemma in_M1_id : forall (A : Set) (a : A) (x : ad) (e : A), (exists c : ad, MapGet A (M1 A x e) c = Some a) -> a = e.
Proof.
intros.
elim H.
intros.
cut (x = x0).
intro.
rewrite H1 in H0.
cut (MapGet A (M1 A x0 e) x0 = Some e).
intros.
cut (Some e = Some a).
intro.
inversion H3.
trivial.
transitivity (MapGet A (M1 A x0 e) x0).
symmetry in |- *.
assumption.
assumption.
exact (M1_semantics_1 A x0 e).
cut (N.eqb x x0 = false \/ N.eqb x x0 = true).
intro.
elim H1; intros.
cut (MapGet A (M1 A x e) x0 = None).
intro.
cut (Some a = None).
intro.
inversion H4.
transitivity (MapGet A (M1 A x e) x0).
symmetry in |- *.
assumption.
assumption.
exact (M1_semantics_2 A x x0 e H2).
exact (Neqb_complete x x0 H2).
elim (bool_dec_eq (N.eqb x x0) true).
intros.
right.
assumption.
intro y.
left.
exact (not_true_is_false (N.eqb x x0) y).
