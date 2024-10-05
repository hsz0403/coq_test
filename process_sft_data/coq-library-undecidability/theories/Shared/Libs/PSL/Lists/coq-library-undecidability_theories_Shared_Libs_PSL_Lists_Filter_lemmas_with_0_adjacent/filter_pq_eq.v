From Undecidability.Shared.Libs.PSL Require Import BaseLists.
Section Filter.
Variable X : Type.
Implicit Types (x y: X) (A B C: list X) (p q: X -> bool).
End Filter.

Lemma filter_pq_eq p q A : (forall x, x el A -> p x = q x) -> filter p A = filter q A.
Proof.
intros C; induction A as [|x A]; cbn.
-
reflexivity.
-
destruct (p x) eqn:D, (q x) eqn:E.
+
f_equal.
auto.
+
exfalso.
enough (p x = q x) by congruence.
auto.
+
exfalso.
enough (p x = q x) by congruence.
auto.
+
auto.
