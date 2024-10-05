Require Import Lia List.
Import ListNotations.
Require Import Undecidability.PolynomialConstraints.LPolyNC.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Local Notation "p ≃ q" := (poly_eq p q) (at level 65).

Lemma poly_eq_nilE {a p} : a :: p ≃ [] -> a = 0 /\ p ≃ [].
Proof.
move=> Hp.
constructor; first by move: (Hp 0).
move=> i.
move: (Hp (S i)).
by case: i.
