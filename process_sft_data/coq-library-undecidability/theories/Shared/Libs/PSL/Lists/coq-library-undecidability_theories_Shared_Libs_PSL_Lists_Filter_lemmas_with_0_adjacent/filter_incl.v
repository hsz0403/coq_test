From Undecidability.Shared.Libs.PSL Require Import BaseLists.
Section Filter.
Variable X : Type.
Implicit Types (x y: X) (A B C: list X) (p q: X -> bool).
End Filter.

Lemma filter_incl p A : filter p A <<= A.
Proof.
intros x D.
apply in_filter_iff in D.
apply D.
