Require Import Lia List.
Import ListNotations.
Require Import Undecidability.PolynomialConstraints.LPolyNC.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Local Notation "p ≃ q" := (poly_eq p q) (at level 65).

Lemma poly_eq_trans {p q r} : p ≃ q -> q ≃ r -> p ≃ r.
Proof.
by move=> + + i => /(_ i) + /(_ i) => -> ->.
