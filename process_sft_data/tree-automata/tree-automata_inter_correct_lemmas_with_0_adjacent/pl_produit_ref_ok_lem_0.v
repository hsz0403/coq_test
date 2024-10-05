Require Import Bool.
Require Import NArith Ndec Ndigits.
Require Import ZArith.
From IntMap Require Import Allmaps.
Require Import bases.
Require Import defs.
Require Import semantics.
Require Import signature.
Require Import refcorrect.
Require Import inter.
Definition pl_produit_ref_ok_0 (la pl : prec_list) : Prop := forall (a b : ad) (l : prec_list) (n : nat), prec_occur (pl_produit_0 a la pl n l) b -> (exists a0 : ad, (exists a1 : ad, b = iad_conv a0 a1 /\ prec_occur la a0 /\ prec_occur pl a1)) \/ (exists a1 : ad, b = iad_conv a a1 /\ prec_occur pl a1) \/ prec_occur l b.
Definition pl_produit_ref_ok_1 (p0 p1 : prec_list) : Prop := forall (b : ad) (n : nat), prec_occur (pl_produit_1 p0 n p1) b -> exists a0 : ad, (exists a1 : ad, b = iad_conv a0 a1 /\ prec_occur p0 a0 /\ prec_occur p1 a1).

Lemma pl_produit_ref_ok_lem_0 : forall p : prec_list, pl_produit_ref_ok_0 p prec_empty.
Proof.
unfold pl_produit_ref_ok_0 in |- *.
intros.
induction p as [a0 p1 Hrecp1 p0 Hrecp0| ].
induction n as [| n Hrecn].
simpl in H.
inversion H.
simpl in H.
right.
right.
exact H.
induction n as [| n Hrecn].
simpl in H.
inversion H.
simpl in H.
right.
right.
exact H.
