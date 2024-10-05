From Undecidability.Shared.Libs.PSL Require Import BaseLists.
Section Filter.
Variable X : Type.
Implicit Types (x y: X) (A B C: list X) (p q: X -> bool).
End Filter.

Lemma filter_fst' p x A : ~ p x -> filter p (x::A) = filter p A.
Proof.
cbn.
destruct (p x); auto.
