Require Import List.
Section Filter.
Variable X : Type.
Implicit Types (x y: X) (A B C: list X) (p q: X -> bool).
Local Notation "x 'el' L" := (In x L) (at level 50).
Local Notation "A '<<=' B" := (incl A B) (at level 50).
End Filter.

Lemma filter_mono p A B : A <<= B -> filter p A <<= filter p B.
Proof.
intros D x E.
apply in_filter_iff in E as [E E'].
apply in_filter_iff.
auto.
