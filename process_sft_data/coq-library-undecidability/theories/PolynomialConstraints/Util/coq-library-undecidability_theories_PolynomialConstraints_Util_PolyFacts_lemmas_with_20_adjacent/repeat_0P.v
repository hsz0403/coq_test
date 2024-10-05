Require Import Lia List.
Import ListNotations.
Require Import Undecidability.PolynomialConstraints.LPolyNC.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Local Notation "p ≃ q" := (poly_eq p q) (at level 65).

Lemma poly_eq_refl {p} : p ≃ p.
Proof.
Admitted.

Lemma poly_eq_sym {p q} : p ≃ q -> q ≃ p.
Proof.
Admitted.

Lemma poly_eq_trans {p q r} : p ≃ q -> q ≃ r -> p ≃ r.
Proof.
Admitted.

Lemma poly_add_nthP {i p q} : nth i (poly_add p q) 0 = (nth i p 0) + (nth i q 0).
Proof.
elim: i p q.
-
move=> [| a p [/= | ]]; [done | by lia | done].
-
Admitted.

Lemma poly_add_comm {p q} : poly_add p q = poly_add q p.
Proof.
elim: p q; first by case.
Admitted.

Lemma poly_add_assoc {p q r} : poly_add p (poly_add q r) ≃ poly_add (poly_add p q) r.
Proof.
move=> i.
rewrite ?poly_add_nthP.
Admitted.

Lemma poly_eq_consI {a b p q} : a = b -> p ≃ q -> a :: p ≃ b :: q.
Proof.
move=> -> + i => /(_ (Nat.pred i)).
Admitted.

Lemma poly_eq_consE {a b p q} : a :: p ≃ b :: q -> a = b /\ p ≃ q.
Proof.
move=> H.
Admitted.

Lemma poly_eq_nilE {a p} : a :: p ≃ [] -> a = 0 /\ p ≃ [].
Proof.
move=> Hp.
constructor; first by move: (Hp 0).
move=> i.
move: (Hp (S i)).
Admitted.

Lemma poly_eq_nilI {a p} : a = 0 -> p ≃ [] -> a :: p ≃ [].
Proof.
move=> -> + i => /(_ (Nat.pred i)).
Admitted.

Lemma repeat_0P {n} : repeat 0 n ≃ [].
Proof.
elim: n; first done.
move=> n + i => /(_ (Nat.pred i)).
case: i; [done | by case].
