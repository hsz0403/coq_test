Require Import Lia List.
Import ListNotations.
Require Import Undecidability.PolynomialConstraints.LPolyNC.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Local Notation "p ≃ q" := (poly_eq p q) (at level 65).

Lemma poly_eq_consE {a b p q} : a :: p ≃ b :: q -> a = b /\ p ≃ q.
Proof.
move=> H.
constructor=> [| i]; [by move: (H 0) | by move: (H (S i))].
