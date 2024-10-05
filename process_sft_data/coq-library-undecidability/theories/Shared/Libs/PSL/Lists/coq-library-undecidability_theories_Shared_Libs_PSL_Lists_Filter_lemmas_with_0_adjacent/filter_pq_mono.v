From Undecidability.Shared.Libs.PSL Require Import BaseLists.
Section Filter.
Variable X : Type.
Implicit Types (x y: X) (A B C: list X) (p q: X -> bool).
End Filter.

Lemma filter_pq_mono p q A : (forall x, x el A -> p x -> q x) -> filter p A <<= filter q A.
Proof.
intros D x E.
apply in_filter_iff in E as [E E'].
apply in_filter_iff.
auto.
