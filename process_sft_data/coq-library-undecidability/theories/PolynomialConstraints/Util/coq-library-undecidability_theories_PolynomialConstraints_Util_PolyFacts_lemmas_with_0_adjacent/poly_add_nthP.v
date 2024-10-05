Require Import Lia List.
Import ListNotations.
Require Import Undecidability.PolynomialConstraints.LPolyNC.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Local Notation "p ≃ q" := (poly_eq p q) (at level 65).

Lemma poly_add_nthP {i p q} : nth i (poly_add p q) 0 = (nth i p 0) + (nth i q 0).
Proof.
elim: i p q.
-
move=> [| a p [/= | ]]; [done | by lia | done].
-
move=> i IH [| a p [/= | b q /=]]; [done | by lia | done].
