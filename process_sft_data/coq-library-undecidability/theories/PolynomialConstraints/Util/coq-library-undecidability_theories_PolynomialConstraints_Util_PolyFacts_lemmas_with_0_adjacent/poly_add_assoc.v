Require Import Lia List.
Import ListNotations.
Require Import Undecidability.PolynomialConstraints.LPolyNC.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Local Notation "p ≃ q" := (poly_eq p q) (at level 65).

Lemma poly_add_assoc {p q r} : poly_add p (poly_add q r) ≃ poly_add (poly_add p q) r.
Proof.
move=> i.
rewrite ?poly_add_nthP.
by lia.
