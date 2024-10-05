Require Import Lia List.
Import ListNotations.
Require Import Undecidability.PolynomialConstraints.LPolyNC.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Local Notation "p ≃ q" := (poly_eq p q) (at level 65).

Lemma repeat_0P {n} : repeat 0 n ≃ [].
Proof.
elim: n; first done.
move=> n + i => /(_ (Nat.pred i)).
case: i; [done | by case].
