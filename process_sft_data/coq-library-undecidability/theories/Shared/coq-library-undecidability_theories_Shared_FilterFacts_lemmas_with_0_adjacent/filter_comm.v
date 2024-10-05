Require Import List.
Section Filter.
Variable X : Type.
Implicit Types (x y: X) (A B C: list X) (p q: X -> bool).
Local Notation "x 'el' L" := (In x L) (at level 50).
Local Notation "A '<<=' B" := (incl A B) (at level 50).
End Filter.

Lemma filter_comm p q A : filter p (filter q A) = filter q (filter p A).
Proof.
rewrite !filter_and.
apply filter_pq_eq.
intros x _.
now destruct (p x), (q x).
