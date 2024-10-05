Require Import List.
Section Filter.
Variable X : Type.
Implicit Types (x y: X) (A B C: list X) (p q: X -> bool).
Local Notation "x 'el' L" := (In x L) (at level 50).
Local Notation "A '<<=' B" := (incl A B) (at level 50).
End Filter.

Lemma filter_fst p x A : p x = true -> filter p (x::A) = x::filter p A.
Proof.
cbn.
destruct (p x); auto.
congruence.
