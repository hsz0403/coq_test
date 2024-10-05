Require Import Lia List.
Import ListNotations.
Require Import Undecidability.PolynomialConstraints.LPolyNC.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Local Notation "p ≃ q" := (poly_eq p q) (at level 65).

Lemma poly_eq_consI {a b p q} : a = b -> p ≃ q -> a :: p ≃ b :: q.
Proof.
move=> -> + i => /(_ (Nat.pred i)).
by case i.
