Require Import Lia List.
Import ListNotations.
Require Import Undecidability.PolynomialConstraints.LPolyNC.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Local Notation "p ≃ q" := (poly_eq p q) (at level 65).

Lemma poly_add_comm {p q} : poly_add p q = poly_add q p.
Proof.
elim: p q; first by case.
move=> a p IH [|b q /=]; [done | by f_equal; [lia | ]].
