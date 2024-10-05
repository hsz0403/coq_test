Require Import Lia List.
Import ListNotations.
Require Import Undecidability.PolynomialConstraints.LPolyNC.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Local Notation "p ≃ q" := (poly_eq p q) (at level 65).

Lemma poly_eq_nilI {a p} : a = 0 -> p ≃ [] -> a :: p ≃ [].
Proof.
move=> -> + i => /(_ (Nat.pred i)).
case: i; [done | by case].
